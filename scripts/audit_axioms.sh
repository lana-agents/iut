#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build Iut4Sec1

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/iut4-sec1-axioms.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
manifest="$tmp_dir/compiled-manifest.txt"
visited="$tmp_dir/visited-manifest.txt"

IUT4_SEC1_AUDIT_MODE=manifest IUT4_SEC1_AUDIT_OUTPUT="$manifest" \
  lake env lean scripts/AuditAxioms.lean
IUT4_SEC1_AUDIT_MODE=visited IUT4_SEC1_AUDIT_OUTPUT="$visited" \
  lake env lean scripts/AuditAxioms.lean

if [[ ! -s "$manifest" || ! -s "$visited" ]]; then
  echo "audit_axioms: declaration coverage is empty" >&2
  exit 1
fi

if ! diff -u "$manifest" "$visited"; then
  echo "audit_axioms: compiled and visited declaration manifests differ" >&2
  exit 1
fi

echo "audit_axioms: manifest covers $(wc -l < "$manifest" | tr -d ' ') declaration(s)"
lake env lean scripts/AuditAxioms.lean

if [[ -f Comparator/Solution.lean ]]; then
  echo "audit_axioms: auditing Comparator/Solution.lean in its separate environment"
  lake env lean scripts/AuditComparatorSolution.lean
fi
