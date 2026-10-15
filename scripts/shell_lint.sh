#!/usr/bin/env bash
# Shell lint (multiradial roadmap, MR0; no-shell criterion (L1)).
#
# Lists the Prop-valued fields of all structures and classes in the import closure of a module
# (outside Lean core, Mathlib and its third-party dependencies; see scripts/ShellLint.lean) and
# compares them with the allowlist scripts/shell_lint_allowlist.txt.
#
# Usage: scripts/shell_lint.sh [--report | --ratchet | --list | --update] [MODULE]
#   MODULE      the module whose import closure is audited (default: Iut, the whole library)
#   --report    print the comparison with the allowlist; never fails (default)
#   --ratchet   as --report, but fail if there is an entry that is not in the allowlist
#               (a NEW Prop field; entries that disappeared are reported, not errors)
#   --list      print the entries only
#   --update    append the new entries to the allowlist with the tag `new` (to be reviewed)
#
# Allowlist format: one entry `<Structure>.<field>` per line, then a TAB and a tag:
#   def       a defining condition of a mathematical notion (allowed at MR30)
#   shell     a property proved in the papers, made into an input (ROADMAP §5; must go)
#   statement a Prop-structure that is the statement of a theorem about a model (must go)
#   baseline  recorded at MR0, not yet classified
#   new       added by --update, to be classified in review
# Lines starting with `#` are comments.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

mode="--report"
module="Iut"
for arg in "$@"; do
  case "$arg" in
    --report|--ratchet|--list|--update) mode="$arg" ;;
    -*) echo "shell_lint: unknown option $arg" >&2; exit 2 ;;
    *) module="$arg" ;;
  esac
done

allowlist="scripts/shell_lint_allowlist.txt"
tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/iut-shell-lint.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

if [[ "$module" != "Iut" ]]; then
  lake build "$module" > /dev/null
fi
sed "s/^import Iut\$/import $module/" scripts/ShellLint.lean > "$tmp_dir/ShellLint.lean"
SHELL_LINT_OUTPUT="$tmp_dir/entries.tsv" lake env lean "$tmp_dir/ShellLint.lean"

if [[ "$mode" == "--list" ]]; then
  cat "$tmp_dir/entries.tsv"
  exit 0
fi

cut -f1 "$tmp_dir/entries.tsv" | LC_ALL=C sort -u > "$tmp_dir/found.txt"
grep -v '^#' "$allowlist" | grep -v '^[[:space:]]*$' | cut -f1 | LC_ALL=C sort -u \
  > "$tmp_dir/allowed.txt"
LC_ALL=C comm -23 "$tmp_dir/found.txt" "$tmp_dir/allowed.txt" > "$tmp_dir/new.txt"
LC_ALL=C comm -13 "$tmp_dir/found.txt" "$tmp_dir/allowed.txt" > "$tmp_dir/gone.txt"

found_count="$(wc -l < "$tmp_dir/found.txt" | tr -d ' ')"
new_count="$(wc -l < "$tmp_dir/new.txt" | tr -d ' ')"
gone_count="$(wc -l < "$tmp_dir/gone.txt" | tr -d ' ')"
echo "shell_lint: $found_count Prop field(s) of structures in the closure of $module"
for tag in def shell statement baseline new; do
  n="$(grep -v '^#' "$allowlist" | awk -F'\t' -v t="$tag" '$2 == t' | cut -f1 \
    | LC_ALL=C sort -u | LC_ALL=C comm -12 - "$tmp_dir/found.txt" | wc -l | tr -d ' ')"
  echo "shell_lint:   allowlisted as $tag: $n"
done
if [[ "$gone_count" != 0 && "$module" == "Iut" ]]; then
  echo "shell_lint: $gone_count allowlisted entr(y/ies) no longer present (remove them):"
  sed 's/^/  - /' "$tmp_dir/gone.txt"
fi
if [[ "$new_count" != 0 ]]; then
  echo "shell_lint: $new_count Prop field(s) NOT in the allowlist:"
  sed 's/^/  + /' "$tmp_dir/new.txt"
fi

case "$mode" in
  --update)
    if [[ "$new_count" != 0 ]]; then
      sed 's/$/\tnew/' "$tmp_dir/new.txt" >> "$allowlist"
      echo "shell_lint: appended $new_count entr(y/ies) with tag 'new' to $allowlist"
    fi
    ;;
  --ratchet)
    if [[ "$new_count" != 0 ]]; then
      echo "shell_lint: new Prop fields of structures (possible shells). If a field is a defining" >&2
      echo "  condition of a notion, add it to $allowlist with the tag 'def'" >&2
      echo "  (scripts/shell_lint.sh --update appends it with the tag 'new')." >&2
      exit 1
    fi
    ;;
esac
