#!/usr/bin/env bash
# Run leanprover/comparator on the challenge/solution pair in Comparator/, as in the
# comparator README: inside a systemd unit that forbids AF_UNIX sockets (the guard against a
# landrun sandbox escape on Linux < 7.1), with `lake env` providing LEAN_PATH.
#
# Requirements (see Comparator/README.md): a comparator build for this Lean version, and
# `landrun` and `lean4export` in PATH or given by COMPARATOR_LANDRUN / COMPARATOR_LEAN4EXPORT.
#
#   COMPARATOR=/path/to/comparator ./scripts/run_comparator.sh

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
comparator="${COMPARATOR:?set COMPARATOR to the comparator binary}"

env_args=(-E PATH="$PATH" -E HOME="$HOME")
for var in COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT; do
  if [[ -n "${!var:-}" ]]; then
    env_args+=(-E "$var=${!var}")
  fi
done

exec systemd-run --user --pipe --wait --quiet \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=MemoryMax="${COMPARATOR_MEMORY_MAX:-7G}" --property=MemorySwapMax=0 \
  "${env_args[@]}" --working-directory "$repo_root" -- \
  bash -c 'lake env "$0" Comparator/config.json' "$comparator"
