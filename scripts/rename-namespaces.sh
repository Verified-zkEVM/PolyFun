#!/usr/bin/env bash

# Phase-2 mechanical rename pass for the VCV-io → PolyFun port.
#
# Rewrites:
#   ToMathlib.PFunctor.*           → PolyFun.PFunctor.*
#   ToMathlib.ITree.*              → PolyFun.ITree.*
#   ToMathlib.Control.<X>          → PolyFun.Control.<X>     (only ported subset)
#   ToMathlib.Logic.HEq            → PolyFun.Logic.HEq
#   VCVio.Interaction.*            → PolyFun.Interaction.*
#
# Applies inside import lines, namespace/end declarations, and `open` lines.
# Mathlib / Std / Init / Batteries imports are left alone.
#
# Run this *after* `port-from-vcvio.sh`. Run from the PolyFun repo root.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if [[ ! -d "PolyFun" || ! -f "PolyFun.lean" ]]; then
  echo "ERROR: must be run from the PolyFun repository root." >&2
  exit 1
fi

# Files in scope: every ported .lean under PolyFun/.
mapfile -t files < <(find PolyFun -name '*.lean' -type f | LC_ALL=C sort)

if (( ${#files[@]} == 0 )); then
  echo "ERROR: no .lean files found under PolyFun/. Run port-from-vcvio.sh first." >&2
  exit 1
fi

echo "# Renaming namespaces across ${#files[@]} files"

# Subset of Control modules we actually ported.
CONTROL_SUFFIXES=(
  "Coalgebra"
  "Comonad.Basic"
  "Comonad.Cofree"
  "Comonad.Instances"
  "Lawful.Basic"
  "Monad.Algebra"
  "Monad.Hom"
  "Monad.Iter"
  "Monad.Free"
  "Monad.FreeCont"
  "Monad.Equiv"
)

# Build perl substitution program.
#
# Order matters: longer / more specific patterns first so that e.g. the
# `ToMathlib.PFunctor.Free.Displayed.Decoration` rewrite happens before
# the broader `ToMathlib.PFunctor` rewrite.
perl_program=""

# Specific Control suffixes (only those we ported).
for suffix in "${CONTROL_SUFFIXES[@]}"; do
  perl_program+="s/\\bToMathlib\\.Control\\.${suffix}\\b/PolyFun.Control.${suffix}/g; "
done

# Catch-all PFunctor / ITree subtrees.
perl_program+='s/\bToMathlib\.PFunctor\b/PolyFun.PFunctor/g; '
perl_program+='s/\bToMathlib\.ITree\b/PolyFun.ITree/g; '

# Logic.HEq.
perl_program+='s/\bToMathlib\.Logic\.HEq\b/PolyFun.Logic.HEq/g; '

# Interaction subtree.
perl_program+='s/\bVCVio\.Interaction\b/PolyFun.Interaction/g; '

perl -i.bak -pe "$perl_program" "${files[@]}"

# Drop the .bak files perl created.
find PolyFun -name '*.lean.bak' -delete

echo "# Smoke check: no stale source-namespace strings in import lines"
if rg -n '^(public )?import (ToMathlib|VCVio\.Interaction)\.' PolyFun >/dev/null 2>&1; then
  echo "❌ Stale import lines remain — investigate:" >&2
  rg -n '^(public )?import (ToMathlib|VCVio\.Interaction)\.' PolyFun >&2
  exit 1
fi

# Check that no `namespace VCVio` / `namespace ToMathlib` headers survived.
if rg -n '^(end )?namespace (VCVio|ToMathlib)(\.|$| )' PolyFun >/dev/null 2>&1; then
  echo "⚠ Stale namespace blocks (VCVio / ToMathlib) remain — review manually:" >&2
  rg -n '^(end )?namespace (VCVio|ToMathlib)(\.|$| )' PolyFun >&2
fi

echo ""
echo "✓ Namespace rename complete. Next steps:"
echo "  1. ./scripts/update-lib.sh   — regenerate PolyFun.lean aggregator"
echo "  2. lake exe cache get && lake build"
echo "  3. fix any straggling references the script missed"
echo "  4. commit phase-2 separately for review legibility"
