#!/usr/bin/env bash

# Check repository-wide Lean module-scope invariants.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

status=0

while IFS= read -r file; do
  if ! grep -qx 'module' "$file"; then
    echo "ERROR: $file does not enable module mode with a 'module' command." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean' 'PolyFunTest/*.lean')

while IFS= read -r file; do
  if ! grep -qx 'public section' "$file"; then
    echo "ERROR: $file does not declare its Interaction API in a 'public section'." >&2
    status=1
  fi
done < <(git ls-files -- 'PolyFun/Interaction/*.lean')

if grep -rEn --include='*.lean' '@\[expose\][[:space:]]+public section' PolyFun/Interaction; then
  echo "ERROR: Broad exposed public sections are forbidden in PolyFun/Interaction." >&2
  echo "Expose individual definitions, or use 'import all' in proof modules." >&2
  status=1
fi

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Module scopes and Interaction API boundaries are valid."
