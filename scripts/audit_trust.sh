#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

# Reviewed exceptions are exact (path, line, token, reason) records. Paths must
# name one Lean file; directory and glob exceptions are rejected below.
readonly trust_exceptions=(
  'Comparator/Challenge.lean|18|sorry|Comparator challenge theorem placeholder reviewed in Plans/Iut4Sec1Spec.md sections 3 and 4'
)
readonly rejected_token_pattern='axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe'
readonly rejected_line_pattern="(^|[^[:alnum:]_])(${rejected_token_pattern})([^[:alnum:]_]|$)"

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
audit_failed=0

validate_exceptions() {
  local record path line token reason
  local index=0
  for record in "${trust_exceptions[@]}"; do
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
}

allow_exception() {
  local candidate_path="$1"
  local candidate_line="$2"
  local candidate_token="$3"
  local record path line token reason
  local index=0
  for record in "${trust_exceptions[@]}"; do
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

validate_exceptions

# Use the specification's ERE with git grep to select contaminated tracked
# files, then identify each exact token occurrence for literal exception checks.
while IFS= read -r -d '' path; do
  scan_file "$path" 1
done < <(git grep -l -z -E "$rejected_line_pattern" -- '*.lean' || true)

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
for record in "${trust_exceptions[@]}"; do
  IFS='|' read -r path line token reason <<< "$record"
  if [[ -f "$path" && "${exception_seen[index]}" != 1 ]]; then
    echo "audit_trust: expected reviewed exception was not found exactly at $path:$line: $token" >&2
    audit_failed=1
  fi
  index=$((index + 1))
done

if [[ "$audit_failed" != 0 ]]; then
  echo "audit_trust: trust audit failed" >&2
  exit 1
fi

echo "audit_trust: tracked, untracked, and ignored .pi Lean source checks passed"
