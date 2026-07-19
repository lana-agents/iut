#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

# Reviewed exceptions are exact (path, line, token, reason) records. Paths must
# name one Lean file; directory and glob exceptions are rejected below.
readonly trust_exceptions=()
readonly rejected_token_pattern='axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe'
readonly rejected_line_pattern="(^|[^[:alnum:]_])(${rejected_token_pattern})([^[:alnum:]_]|$)"

# Machine-local path exceptions use the same exact (path, line, literal, reason)
# mechanism as trust-token exceptions. Keep this list empty unless a review
# approves a specific occurrence; directory and glob exceptions are rejected.
# Build a reviewed token from the components below so its allow-list record does
# not itself become another forbidden path occurrence in this tracked script.
readonly users_path_component='Users'
readonly home_path_component='home'
readonly machine_local_path_exceptions=()
readonly machine_local_path_pattern='/(Users|home)/'

# Ignored Lean probes are permitted only in the two feasibility phases from the
# specification, only below .pi/probes/, and only with an explicit phase ID:
#   AUDIT_FEASIBILITY_PHASE=P5 ./scripts/audit_trust.sh
feasibility_phase="${AUDIT_FEASIBILITY_PHASE:-}"
case "$feasibility_phase" in
  '') ;;
  P5|P14)
    echo "audit_trust: feasibility mode $feasibility_phase enabled for ignored .pi/probes/*.lean files" >&2
    ;;
  *)
    echo "audit_trust: AUDIT_FEASIBILITY_PHASE must be P5 or P14 (got '$feasibility_phase')" >&2
    exit 1
    ;;
esac

exception_seen=()
machine_local_path_exception_seen=()
audit_failed=0

validate_exceptions() {
  local record path line token reason
  local index=0
  for record in ${trust_exceptions[@]+"${trust_exceptions[@]}"}; do
    IFS='|' read -r path line token reason <<< "$record"
    if [[ -z "$path" || -z "$line" || -z "$token" || -z "$reason" ||
          "$path" == /* || "$path" == */ || "$path" != *.lean ||
          "$path" == *'*'* || "$path" == *'?'* || "$path" == *'['* ||
          "$path" == *']'* || "$path" == *'{'* || "$path" == *'}'* ||
          "$path" == *'//'* || "$path" == './'* || "$path" == *'/./'* ||
          "$path" == '../'* || "$path" == *'/../'* || ! "$line" =~ ^[1-9][0-9]*$ ||
          ! "$token" =~ ^(${rejected_token_pattern})$ ]]; then
      echo "audit_trust: invalid exception record (literal file, line, token, and reason required): $record" >&2
      exit 1
    fi
    if [[ -e "$path" && ! -f "$path" ]]; then
      echo "audit_trust: exception path must name a file, not a directory: $path" >&2
      exit 1
    fi
    exception_seen[index]=0
    index=$((index + 1))
  done

  index=0
  for record in ${machine_local_path_exceptions[@]+"${machine_local_path_exceptions[@]}"}; do
    IFS='|' read -r path line token reason <<< "$record"
    if [[ -z "$path" || -z "$line" || -z "$token" || -z "$reason" ||
          "$path" == /* || "$path" == */ ||
          "$path" == *'*'* || "$path" == *'?'* || "$path" == *'['* ||
          "$path" == *']'* || "$path" == *'{'* || "$path" == *'}'* ||
          "$path" == *'//'* || "$path" == './'* || "$path" == *'/./'* ||
          "$path" == '../'* || "$path" == *'/../'* || ! "$line" =~ ^[1-9][0-9]*$ ||
          ( "$token" != "/${users_path_component}/" &&
            "$token" != "/${home_path_component}/" ) ]]; then
      echo "audit_trust: invalid machine-local path exception (literal file, line, path token, and reason required): $record" >&2
      exit 1
    fi
    if [[ -e "$path" && ! -f "$path" ]]; then
      echo "audit_trust: machine-local path exception must name a file, not a directory: $path" >&2
      exit 1
    fi
    machine_local_path_exception_seen[index]=0
    index=$((index + 1))
  done
}

allow_exception() {
  local candidate_path="$1"
  local candidate_line="$2"
  local candidate_token="$3"
  local record path line token reason
  local index=0
  for record in ${trust_exceptions[@]+"${trust_exceptions[@]}"}; do
    IFS='|' read -r path line token reason <<< "$record"
    if [[ "$candidate_path" == "$path" && "$candidate_line" == "$line" &&
          "$candidate_token" == "$token" ]]; then
      if [[ "${exception_seen[index]}" == 1 ]]; then
        return 1
      fi
      exception_seen[index]=1
      echo "audit_trust: reviewed exception: $path:$line: $token ($reason)" >&2
      return 0
    fi
    index=$((index + 1))
  done
  return 1
}

scan_file() {
  local path="$1"
  local permit_exceptions="$2"
  local line token
  while IFS='|' read -r line token; do
    [[ -n "$line" ]] || continue
    if [[ "$permit_exceptions" == 1 ]] && allow_exception "$path" "$line" "$token"; then
      continue
    fi
    echo "audit_trust: rejected token: $path:$line: $token" >&2
    audit_failed=1
  done < <(perl -ne 'while (/(?<![[:alnum:]_])(axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe)(?![[:alnum:]_])/g) { print "$.|$1\n" }' "$path")
}

readonly challenge_file='Comparator/Challenge.lean'
readonly challenge_targets=(
  'localParameters_eq_of_smallRamification'
  'nonarchimedean_logError_sum_le'
  'nonarchimedean_secondError_sum_le'
  'complexTensorToProd_bijective'
  'complexTensorToProd_normSq'
  'eventually_primeCounting_le_four_thirds'
  'weighted_average_eq'
  'average_range_sum'
  'average_range_sq_sum'
  'normalizedArithmeticDivisorDegree_nonneg'
)

audit_challenge() {
  local line token target declaration_count block_count
  local token_count=0
  local theorem_count

  while IFS='|' read -r line token; do
    [[ -n "$line" ]] || continue
    token_count=$((token_count + 1))
    if [[ "$token" != sorry ]]; then
      echo "audit_trust: rejected challenge token: $challenge_file:$line: $token" >&2
      audit_failed=1
    fi
  done < <(perl -ne 'while (/(?<![[:alnum:]_])(axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe)(?![[:alnum:]_])/g) { print "$.|$1\n" }' "$challenge_file")

  if [[ "$token_count" != 10 ]]; then
    echo "audit_trust: $challenge_file must contain exactly ten reviewed proof placeholders (found $token_count)" >&2
    audit_failed=1
  fi

  theorem_count="$(grep -Ec '^theorem[[:space:]]+' "$challenge_file" || true)"
  if [[ "$theorem_count" != 10 ]]; then
    echo "audit_trust: $challenge_file must declare exactly ten theorems (found $theorem_count)" >&2
    audit_failed=1
  fi

  for target in "${challenge_targets[@]}"; do
    declaration_count="$(grep -Ec "^theorem[[:space:]]+${target}([[:space:]]|$)" "$challenge_file" || true)"
    if [[ "$declaration_count" != 1 ]]; then
      echo "audit_trust: expected exactly one challenge theorem declaration for Iut4Sec1.$target (found $declaration_count)" >&2
      audit_failed=1
      continue
    fi
    block_count="$(awk -v target="$target" '
      $0 ~ ("^theorem[[:space:]]+" target "([[:space:]]|$)") { active = 1; next }
      active && /^theorem[[:space:]]+/ { exit }
      active {
        line = $0
        while (match(line, /(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)/)) {
          count++
          line = substr(line, RSTART + RLENGTH)
        }
      }
      END { print count + 0 }
    ' "$challenge_file")"
    if [[ "$block_count" != 1 ]]; then
      echo "audit_trust: Iut4Sec1.$target must have exactly one proof placeholder (found $block_count)" >&2
      audit_failed=1
    fi
  done
}

allow_machine_local_path_exception() {
  local candidate_path="$1"
  local candidate_line="$2"
  local candidate_token="$3"
  local record path line token reason
  local index=0
  for record in ${machine_local_path_exceptions[@]+"${machine_local_path_exceptions[@]}"}; do
    IFS='|' read -r path line token reason <<< "$record"
    if [[ "$candidate_path" == "$path" && "$candidate_line" == "$line" &&
          "$candidate_token" == "$token" ]]; then
      if [[ "${machine_local_path_exception_seen[index]}" == 1 ]]; then
        return 1
      fi
      machine_local_path_exception_seen[index]=1
      echo "audit_trust: reviewed machine-local path exception: $path:$line: $token ($reason)" >&2
      return 0
    fi
    index=$((index + 1))
  done
  return 1
}

scan_machine_local_paths() {
  local path="$1"
  local line token
  while IFS='|' read -r line token; do
    [[ -n "$line" ]] || continue
    if allow_machine_local_path_exception "$path" "$line" "$token"; then
      continue
    fi
    echo "audit_trust: rejected machine-local path: $path:$line: $token" >&2
    audit_failed=1
  done < <(perl -ne 'while (m{/(Users|home)/}g) { print "$.|/$1/\n" }' "$path")
}

validate_exceptions

# Scan all tracked text files. `-I` excludes binary files; an unexpected git
# failure is fatal rather than being treated as an empty result.
path_scan_results="$(mktemp "${TMPDIR:-/tmp}/iut4-sec1-path-audit.XXXXXX")"
trap 'rm -f "$path_scan_results"' EXIT
if git grep -l -z -I -E "$machine_local_path_pattern" > "$path_scan_results"; then
  :
else
  grep_status=$?
  if [[ "$grep_status" != 1 ]]; then
    echo "audit_trust: tracked-file machine-local path scan failed (git grep exit $grep_status)" >&2
    exit 1
  fi
fi
while IFS= read -r -d '' path; do
  scan_machine_local_paths "$path"
done < "$path_scan_results"

# Use the specification's ERE with git grep to select contaminated tracked
# files, then identify each exact token occurrence for literal exception checks.
while IFS= read -r -d '' path; do
  scan_file "$path" 1
done < <(git grep -l -z -E "$rejected_line_pattern" -- '*.lean' \
  ':(exclude)Comparator/Challenge.lean' || true)

audit_challenge

while IFS= read -r -d '' path; do
  echo "audit_trust: untracked Lean source is not permitted: $path" >&2
  scan_file "$path" 0
  audit_failed=1
done < <(git ls-files --others --exclude-standard -z -- '*.lean')

if [[ -d .pi ]]; then
  # Fail closed on every symlink in the ignored probe boundary. In particular,
  # feasibility mode must never permit a probe to escape .pi through a link.
  while IFS= read -r -d '' path; do
    path="${path#./}"
    echo "audit_trust: symlink is not permitted under .pi: $path" >&2
    audit_failed=1
  done < <(find .pi -type l -print0)

  while IFS= read -r -d '' path; do
    path="${path#./}"
    if ! git check-ignore -q -- "$path"; then
      continue
    fi
    if [[ -n "$feasibility_phase" && "$path" == .pi/probes/*.lean ]]; then
      continue
    fi
    echo "audit_trust: ignored .pi Lean source is not permitted outside explicit P5/P14 feasibility mode: $path" >&2
    scan_file "$path" 0
    audit_failed=1
  done < <(find .pi -type f -name '*.lean' -print0)
fi

index=0
for record in ${trust_exceptions[@]+"${trust_exceptions[@]}"}; do
  IFS='|' read -r path line token reason <<< "$record"
  if [[ -f "$path" && "${exception_seen[index]}" != 1 ]]; then
    echo "audit_trust: expected reviewed exception was not found exactly at $path:$line: $token" >&2
    audit_failed=1
  fi
  index=$((index + 1))
done

index=0
for record in ${machine_local_path_exceptions[@]+"${machine_local_path_exceptions[@]}"}; do
  IFS='|' read -r path line token reason <<< "$record"
  if [[ -f "$path" && "${machine_local_path_exception_seen[index]}" != 1 ]]; then
    echo "audit_trust: expected reviewed machine-local path exception was not found exactly at $path:$line: $token" >&2
    audit_failed=1
  fi
  index=$((index + 1))
done

if [[ "$audit_failed" != 0 ]]; then
  echo "audit_trust: trust audit failed" >&2
  exit 1
fi

echo "audit_trust: tracked text path and tracked, untracked, and ignored .pi Lean source checks passed"
