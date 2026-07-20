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
lake exe mk_all --lib Iut --git --check || exit 1
lake exe mk_all --lib Iut4Sec1 --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds.
#
# Note: this is `lake build`, not `lake build --wfail`. Three pre-existing
# `linter.unusedDecidableInType` warnings (Iut4Sec1/Real/LogError.lean and the two
# mirrored Comparator/Challenge.lean statements) would fail --wfail, and the fix
# changes theorem signatures that the comparator suite pins. The audits below are
# the project's real honesty gate.
lake build

# Comparator suite: shared public declarations must match between Challenge and
# Solution, and the config must be complete.
./scripts/check_comparator_signature.sh

# Tracked-path, credential, and .pi source checks.
./scripts/audit_trust.sh

# Axiom audit of the theorems exported by Solution. This is what catches an
# accidental `sorry` now that `warn.sorry = false` is set in the lakefile:
# a sorried theorem shows up here as `sorryAx`.
./scripts/audit_axioms.sh
