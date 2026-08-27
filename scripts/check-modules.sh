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

# The `Std.Do` quarantine (AGENTS.md gotcha 8, docs/wiki/program-logic.md): core's
# weakest-precondition / `mvcgen` API moves fast, so only the bridge modules may depend on it.
# Everything they export is a construction, never a global instance.
std_do_allowed() {
  case "$1" in
    PolyFun/Control/Do/Basic.lean|PolyFun/PFunctor/Free/Do.lean|PolyFunTest/Do/*) return 0 ;;
    *) return 1 ;;
  esac
}

while IFS= read -r file; do
  if grep -qE '^[[:space:]]*(public[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+Std\.(Tactic\.)?Do([[:space:]]*$|\.)' "$file"; then
    if ! std_do_allowed "$file"; then
      echo "ERROR: $file imports core Std.Do outside the quarantine." >&2
      echo "Only PolyFun/Control/Do/Basic.lean, PolyFun/PFunctor/Free/Do.lean, and" >&2
      echo "PolyFunTest/Do/ may depend on it. See AGENTS.md gotcha 8." >&2
      status=1
    fi
  fi
done < <(git ls-files -- 'PolyFun.lean' 'PolyFun/*.lean' 'PolyFunTest/*.lean')

if grep -rEn --include='*.lean' '@\[expose\][[:space:]]+public section' PolyFun/Interaction; then
  echo "ERROR: Broad exposed public sections are forbidden in PolyFun/Interaction." >&2
  echo "Expose individual definitions, or use 'import all' in proof modules." >&2
  status=1
fi

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Module scopes and Interaction API boundaries are valid."
