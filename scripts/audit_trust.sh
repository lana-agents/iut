#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

rejected='(^|[^[:alnum:]_])(axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe)([^[:alnum:]_]|$)'
challenge='Comparator/Challenge.lean'

if git grep -n -E "$rejected" -- '*.lean' ":(exclude)$challenge"; then
  echo "audit_trust: rejected token in tracked Lean source" >&2
  exit 1
fi

if [[ -n "$(git ls-files --others --exclude-standard -- '*.lean')" ]]; then
  echo "audit_trust: untracked Lean source is not permitted:" >&2
  git ls-files --others --exclude-standard -- '*.lean' >&2
  exit 1
fi

if [[ -f "$challenge" ]]; then
  other_rejected='(^|[^[:alnum:]_])(axiom|constant|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe)([^[:alnum:]_]|$)'
  sorry_count="$(perl -ne '$count += () = /(?<![[:alnum:]_])sorry(?![[:alnum:]_])/g; END { print "$count\n" }' "$challenge")"
  if [[ "$sorry_count" != 1 ]]; then
    echo "audit_trust: $challenge must contain exactly one sorry occurrence (found $sorry_count)" >&2
    exit 1
  fi
  if grep -n -E "$other_rejected" "$challenge"; then
    echo "audit_trust: rejected non-placeholder token in $challenge" >&2
    exit 1
  fi
fi

echo "audit_trust: tracked and untracked Lean source checks passed"
