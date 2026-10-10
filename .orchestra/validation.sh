#!/usr/bin/env bash
set -euo pipefail

# $HOME is read-only in this sandbox, so keep lake's cache dir inside the repo.
export XDG_CACHE_HOME="$PWD/.cache-home"

# scripts/check_comparator_signature.sh sorts with LC_ALL=C but then pipes into
# `comm`, which inherits the ambient locale and reports "not in sorted order"
# under any non-C collation. Pin the collation for the whole run.
export LC_ALL=C

# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
#
# The root files `Iut.lean` and `Iut4Sec1.lean` carry the standard copyright header,
# which `mk_all --check` (a byte-for-byte comparison with the generated import list)
# does not know about. So check that each root file is exactly the standard header,
# one blank line, and then precisely what `mk_all` generates: strip the header,
# run `mk_all --check` on the remainder, and restore the file in every case.
check_root_imports() {
  local lib="$1"
  local root="$lib.lean"
  local backup
  backup="$(mktemp "${TMPDIR:-/tmp}/iut-root-imports.XXXXXX")"
  cp "$root" "$backup"
  if ! head -n 6 "$root" | python3 -c '
import re, sys
header = re.compile(
    r"/-\nCopyright \(c\) \d{4} [^\n]+\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: [^\n]+\n-/\n\n\Z")
sys.exit(0 if header.match(sys.stdin.read()) else 1)'; then
    echo "$root must start with the standard copyright header followed by one blank line"
    rm -f "$backup"
    return 1
  fi
  local status=0
  tail -n +7 "$backup" > "$root"
  lake exe mk_all --lib "$lib" --git --check || status=$?
  cp "$backup" "$root"
  rm -f "$backup"
  return "$status"
}
check_root_imports Iut || exit 1
check_root_imports Iut4Sec1 || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds, with warnings as errors (as in CI).
lake build --wfail

# Comparator pair (the main theorem): the public declarations of Challenge and Solution
# must match, and the config must list exactly the shared theorem.
./scripts/check_comparator_signature.sh

# Tracked-path, credential, and .pi source checks.
./scripts/audit_trust.sh

# Axiom audit of the libraries and of the theorem exported by Solution, and the audit of the
# challenge's trusted import closure (statement-only, sorry-free). This is what catches an
# accidental `sorry` now that `warn.sorry = false` is set in the lakefile:
# a sorried theorem shows up here as `sorryAx`.
./scripts/audit_axioms.sh
