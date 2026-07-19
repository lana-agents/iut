#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build Challenge Solution

fixture_dir="$repo_root/.pi/comparator-signature"
challenge_fixture="$fixture_dir/ChallengeSignature.lean"
solution_fixture="$fixture_dir/SolutionSignature.lean"
challenge_raw="$fixture_dir/challenge.raw"
solution_raw="$fixture_dir/solution.raw"
challenge_type="$fixture_dir/challenge.type"
solution_type="$fixture_dir/solution.type"

rm -rf "$fixture_dir"
mkdir -p "$fixture_dir"
trap 'rm -rf "$fixture_dir"' EXIT

write_fixture() {
  local module="$1"
  local target="$2"
  cat > "$target" <<EOF
import $module

set_option pp.all true in
#check @Iut4Sec1.nonarchimedean_logError_sum_le
EOF
}

write_fixture Challenge "$challenge_fixture"
write_fixture Solution "$solution_fixture"

if ! lake env lean "$challenge_fixture" >"$challenge_raw" 2>&1; then
  cat "$challenge_raw" >&2
  exit 1
fi
if ! lake env lean "$solution_fixture" >"$solution_raw" 2>&1; then
  cat "$solution_raw" >&2
  exit 1
fi

# Keep the complete pretty-printed type. Strip only diagnostic source locations
# and standalone warning headers, which depend on the temporary fixture path.
normalize() {
  sed -E \
    -e '/^[^:]*\.lean:[0-9]+:[0-9]+: warning:/d' \
    -e 's#^[^:]*\.lean:[0-9]+:[0-9]+: (info: )?##' \
    "$1" > "$2"
}

normalize "$challenge_raw" "$challenge_type"
normalize "$solution_raw" "$solution_type"

diff -u "$challenge_type" "$solution_type"
echo "check_comparator_signature: complete elaborated types match"
