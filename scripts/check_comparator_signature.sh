#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build Challenge Solution

fixture_dir="$repo_root/.pi/comparator-signature"
challenge_manifest="$fixture_dir/challenge.manifest"
solution_manifest="$fixture_dir/solution.manifest"
challenge_names="$fixture_dir/challenge.names"
solution_names="$fixture_dir/solution.names"
shared_names="$fixture_dir/shared.names"
shared_theorems="$fixture_dir/shared.theorems"
config_names="$fixture_dir/config.names"
challenge_fixture="$fixture_dir/ChallengeSignature.lean"
solution_fixture="$fixture_dir/SolutionSignature.lean"
challenge_raw="$fixture_dir/challenge.raw"
solution_raw="$fixture_dir/solution.raw"
challenge_type="$fixture_dir/challenge.type"
solution_type="$fixture_dir/solution.type"

rm -rf "$fixture_dir"
mkdir -p "$fixture_dir"
trap 'rm -rf "$fixture_dir"' EXIT

write_manifest_fixture() {
  local module="$1"
  local target="$2"
  cat > "$target" <<EOF
import $module
import Mathlib.Tactic.Linter.PrivateModule

open Lean Elab Command

private def comparatorNamespace : Name := \`Iut4Sec1

private def isComparatorPublicName (env : Environment) (declName : Name) : Bool :=
  comparatorNamespace.isPrefixOf declName &&
    !isPrivateName declName && !isReservedName env declName

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let some output ← IO.getEnv "COMPARATOR_MANIFEST_OUTPUT" |
    throwError "COMPARATOR_MANIFEST_OUTPUT is required"
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun entries declName info =>
    if isComparatorPublicName env declName then
      entries.push s!"{declName}|{declarationKind info}"
    else entries
  let entries := entries.qsort fun left right => left < right
  IO.FS.writeFile output (String.intercalate "\n" entries.toList ++ "\n")
EOF
}

write_manifest_fixture Challenge "$fixture_dir/ChallengeManifest.lean"
write_manifest_fixture Solution "$fixture_dir/SolutionManifest.lean"

COMPARATOR_MANIFEST_OUTPUT="$challenge_manifest" \
  lake env lean "$fixture_dir/ChallengeManifest.lean"
COMPARATOR_MANIFEST_OUTPUT="$solution_manifest" \
  lake env lean "$fixture_dir/SolutionManifest.lean"

test -s "$challenge_manifest"
test -s "$solution_manifest"
cut -d'|' -f1 "$challenge_manifest" | LC_ALL=C sort -u > "$challenge_names"
cut -d'|' -f1 "$solution_manifest" | LC_ALL=C sort -u > "$solution_names"
comm -12 "$challenge_names" "$solution_names" > "$shared_names"
test -s "$shared_names"

while IFS= read -r name; do
  challenge_kind="$(awk -F'|' -v name="$name" '$1 == name { print $2 }' "$challenge_manifest")"
  solution_kind="$(awk -F'|' -v name="$name" '$1 == name { print $2 }' "$solution_manifest")"
  if [[ -z "$challenge_kind" || "$challenge_kind" != "$solution_kind" ]]; then
    echo "check_comparator_signature: declaration-kind mismatch for $name: Challenge=$challenge_kind Solution=$solution_kind" >&2
    exit 1
  fi
  if [[ "$challenge_kind" == theorem ]]; then
    echo "$name"
  fi
done < "$shared_names" | LC_ALL=C sort -u > "$shared_theorems"

python3 - "$config_names" <<'PY'
import json
import sys

with open("Comparator/config.json", encoding="utf-8") as stream:
    config = json.load(stream)
if config.get("challenge_module") != "Challenge":
    raise SystemExit("check_comparator_signature: challenge_module must be Challenge")
if config.get("solution_module") != "Solution":
    raise SystemExit("check_comparator_signature: solution_module must be Solution")
if config.get("definition_names") != []:
    raise SystemExit("check_comparator_signature: definition_names must be empty")
names = config.get("theorem_names")
if not isinstance(names, list) or any(not isinstance(name, str) for name in names):
    raise SystemExit("check_comparator_signature: theorem_names must be an array of strings")
if len(names) != len(set(names)):
    raise SystemExit("check_comparator_signature: theorem_names contains duplicates")
with open(sys.argv[1], "w", encoding="utf-8") as stream:
    for name in sorted(names):
        stream.write(name + "\n")
PY

if ! diff -u "$shared_theorems" "$config_names"; then
  echo "check_comparator_signature: config must list exactly the shared theorem targets exported by Solution" >&2
  exit 1
fi

write_type_fixture() {
  local module="$1"
  local target="$2"
  {
    echo "import $module"
    echo
    while IFS= read -r name; do
      printf 'set_option pp.all true in\n#check @%s\n\n' "$name"
    done < "$shared_names"
  } > "$target"
}

write_type_fixture Challenge "$challenge_fixture"
write_type_fixture Solution "$solution_fixture"

if ! lake env lean "$challenge_fixture" >"$challenge_raw" 2>&1; then
  cat "$challenge_raw" >&2
  exit 1
fi
if ! lake env lean "$solution_fixture" >"$solution_raw" 2>&1; then
  cat "$solution_raw" >&2
  exit 1
fi

# Keep complete pretty-printed declarations. Strip only diagnostic source
# locations and standalone warning headers from the temporary fixtures.
normalize() {
  sed -E \
    -e '/^[^:]*\.lean:[0-9]+:[0-9]+: warning:/d' \
    -e 's#^[^:]*\.lean:[0-9]+:[0-9]+: (info: )?##' \
    "$1" > "$2"
}

normalize "$challenge_raw" "$challenge_type"
normalize "$solution_raw" "$solution_type"

diff -u "$challenge_type" "$solution_type"
echo "check_comparator_signature: all shared public declarations match; config is complete"
