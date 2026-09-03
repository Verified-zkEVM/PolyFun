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
# weakest-precondition / `mvcgen` / `vcgen` API moves fast, so only the bridge modules may depend
# on it. The fence covers both stacks core ships, `Std.Do` and `Std.Internal.Do`, and the tactic
# layer `Std.Tactic.Do`. Everything the bridge modules export is a construction, never a global
# instance.
std_do_allowed() {
  case "$1" in
    PolyFun/Control/Do/Basic.lean|PolyFun/PFunctor/Free/Do.lean|PolyFunTest/Do/*) return 0 ;;
    *) return 1 ;;
  esac
}

std_do_import_pattern='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import([[:space:]]+all)?[[:space:]]+Std\.((Tactic|Internal)\.)?Do([[:space:]]*$|\.)'

# Keep every supported import modifier covered: otherwise a valid Lean import form can bypass
# the quarantine while the repository's existing files still leave this check green.
for std_do_import in \
    'import Std.Do' \
    'import Std.Internal.Do' \
    'public import Std.Internal.Do.WP.Basic' \
    'public import Std.Tactic.Do' \
    'import all Std.Tactic.Do' \
    'public import all Std.Tactic.Do' \
    'meta import Std.Tactic.Do' \
    'public meta import Std.Tactic.Do' \
    'meta import all Std.Tactic.Do' \
    'public meta import all Std.Tactic.Do'; do
  if ! grep -qE "$std_do_import_pattern" <<< "$std_do_import"; then
    echo "ERROR: Std.Do import matcher does not recognize: $std_do_import" >&2
    status=1
  fi
done

while IFS= read -r file; do
  if grep -qE "$std_do_import_pattern" "$file"; then
    if ! std_do_allowed "$file"; then
      echo "ERROR: $file imports core Std.Do / Std.Internal.Do outside the quarantine." >&2
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
