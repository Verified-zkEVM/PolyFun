#!/usr/bin/env bash

# Wholesale-copy phase of the VCV-io → PolyFun port.
#
# This script is intentionally one-shot. It performs the wholesale-copy
# phase of the original PolyFun extraction. The expectation is that you run
# it exactly once, then commit, then run `rename-namespaces.sh` for the
# textual rename pass.
#
# Usage:
#   ./scripts/port-from-vcvio.sh [SRC]
# where SRC defaults to ~/Documents/Lean/VCV-io-freeM-displayed
#
# Idempotency: the script uses `cp -p`, so re-running clobbers existing
# destination files with whatever the current source has. That is the
# intended behaviour — re-running picks up upstream cutover work in the
# VCV-io worktree.
#
# Pre-flight checks:
#   1. The VCV-io PFUNCTOR-FIRST cutover (in the source worktree) must
#      be merged or deemed stable.
#   2. `git status` in the destination must be clean.

set -euo pipefail

SRC="${1:-$HOME/Documents/Lean/VCV-io-freeM-displayed}"
REPO_ROOT="$(git rev-parse --show-toplevel)"
DST="$REPO_ROOT"

if [[ ! -d "$SRC" ]]; then
  echo "ERROR: VCV-io source tree not found at: $SRC" >&2
  exit 1
fi

if [[ ! -d "$SRC/ToMathlib/PFunctor" || ! -d "$SRC/VCVio/Interaction" ]]; then
  echo "ERROR: $SRC does not look like the VCV-io worktree." >&2
  exit 1
fi

if [[ ! -d "$DST/PolyFun" || ! -f "$DST/PolyFun.lean" ]]; then
  echo "ERROR: must be run from the PolyFun repository root." >&2
  exit 1
fi

echo "# Source: $SRC"
echo "# Destination: $DST"
echo ""

# -----------------------------------------------------------------------------
# Layer A: PFunctor core
# -----------------------------------------------------------------------------
echo "# Copying Layer A — PFunctor core"
mkdir -p "$DST/PolyFun/PFunctor/Free/Displayed"
mkdir -p "$DST/PolyFun/PFunctor/Chart"
mkdir -p "$DST/PolyFun/PFunctor/Equiv"
mkdir -p "$DST/PolyFun/PFunctor/Lens"

cp -p "$SRC"/ToMathlib/PFunctor/{Basic,Bound,Category,Cofree,MFacts,Trace}.lean \
      "$DST/PolyFun/PFunctor/"
cp -p "$SRC"/ToMathlib/PFunctor/Free/{Basic,Path,Displayed}.lean \
      "$DST/PolyFun/PFunctor/Free/"
cp -p "$SRC"/ToMathlib/PFunctor/Free/Displayed/Decoration.lean \
      "$DST/PolyFun/PFunctor/Free/Displayed/"
cp -p "$SRC"/ToMathlib/PFunctor/Chart/Basic.lean       "$DST/PolyFun/PFunctor/Chart/"
cp -p "$SRC"/ToMathlib/PFunctor/Equiv/Basic.lean       "$DST/PolyFun/PFunctor/Equiv/"
cp -p "$SRC"/ToMathlib/PFunctor/Lens/{Basic,Cartesian,State}.lean \
      "$DST/PolyFun/PFunctor/Lens/"

# -----------------------------------------------------------------------------
# Layer B: ITree
# -----------------------------------------------------------------------------
echo "# Copying Layer B — ITree"
mkdir -p "$DST/PolyFun/ITree"/{Bisim,Sim,Events}

cp -p "$SRC"/ToMathlib/ITree/{Basic,Construct,Handler,Rec}.lean "$DST/PolyFun/ITree/"
cp -p "$SRC"/ToMathlib/ITree/Bisim/{Defs,Bind,Equiv}.lean       "$DST/PolyFun/ITree/Bisim/"
cp -p "$SRC"/ToMathlib/ITree/Sim/{Defs,Facts}.lean              "$DST/PolyFun/ITree/Sim/"
cp -p "$SRC"/ToMathlib/ITree/Events/{Exception,State}.lean      "$DST/PolyFun/ITree/Events/"

# -----------------------------------------------------------------------------
# Layer C: Generic interaction framework
# -----------------------------------------------------------------------------
echo "# Copying Layer C — Interaction framework"
mkdir -p "$DST/PolyFun/Interaction"/{Basic,Concurrent,TwoParty,Multiparty,UC/OpenSyntax}

cp -p "$SRC"/VCVio/Interaction/Basic/*.lean       "$DST/PolyFun/Interaction/Basic/"
cp -p "$SRC"/VCVio/Interaction/Concurrent/*.lean  "$DST/PolyFun/Interaction/Concurrent/"
cp -p "$SRC"/VCVio/Interaction/TwoParty/*.lean    "$DST/PolyFun/Interaction/TwoParty/"
cp -p "$SRC"/VCVio/Interaction/Multiparty/*.lean  "$DST/PolyFun/Interaction/Multiparty/"

# UC: only the generic-friendly subset. Excludes Computational, Runtime,
# Standard, AsyncRuntime, AsyncSecurity, StdDoBridge.
# EnvAction is included; it gets a generic-monad rewrite in the rename phase.
cp -p "$SRC"/VCVio/Interaction/UC/Interface.lean         "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/OpenProcess.lean       "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/OpenProcessModel.lean  "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/OpenTheory.lean        "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/Notation.lean          "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/Emulates.lean          "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/MachineId.lean         "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/Leakage.lean           "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/EnvAction.lean         "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/EnvOpenProcess.lean    "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/CorruptionModel.lean   "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/MomentaryCorruption.lean "$DST/PolyFun/Interaction/UC/"
cp -p "$SRC"/VCVio/Interaction/UC/OpenSyntax/{Raw,Interp,Expr}.lean \
      "$DST/PolyFun/Interaction/UC/OpenSyntax/"

# -----------------------------------------------------------------------------
# Layer D: transitively-required Control / Logic helpers
# -----------------------------------------------------------------------------
echo "# Copying Layer D — Control / Logic helpers"
mkdir -p "$DST/PolyFun/Control"/{Comonad,Lawful,Monad}
mkdir -p "$DST/PolyFun/Logic"

cp -p "$SRC"/ToMathlib/Control/{Coalgebra,Trace}.lean      "$DST/PolyFun/Control/"
cp -p "$SRC"/ToMathlib/Control/Comonad/{Basic,Cofree,Instances}.lean \
      "$DST/PolyFun/Control/Comonad/"
cp -p "$SRC"/ToMathlib/Control/Lawful/Basic.lean           "$DST/PolyFun/Control/Lawful/"
cp -p "$SRC"/ToMathlib/Control/Monad/{Algebra,Hom,Iter,Free,FreeCont,Equiv}.lean \
      "$DST/PolyFun/Control/Monad/"

cp -p "$SRC"/ToMathlib/Logic/HEq.lean   "$DST/PolyFun/Logic/"

echo ""
echo "# File count under PolyFun/"
find "$DST/PolyFun" -name '*.lean' | wc -l

echo ""
echo "✓ Wholesale copy complete. Next steps:"
echo "  1. git status     — review the file additions"
echo "  2. git add PolyFun"
echo "  3. git commit -m 'port: wholesale copy from VCV-io @ <sha>'"
echo "  4. ./scripts/rename-namespaces.sh   — phase-2 textual rename"
