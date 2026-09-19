#!/usr/bin/env bash

# Update a library's umbrella module with all public imports.
#
#   ./scripts/update-lib.sh                       # regenerates PolyFun.lean
#   ./scripts/update-lib.sh ToCslib               # regenerates ToCslib.lean
#   ./scripts/update-lib.sh ComplexityBackends    # regenerates ComplexityBackends.lean
#   ./scripts/update-lib.sh Examples.Parliament   # regenerates Examples/Parliament.lean
#
# This script only considers tracked files. New <Lib>/**/*.lean files
# must be staged first.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

lib="${1:-PolyFun}"
case "$lib" in
  PolyFun|ToCslib|ComplexityBackends|Examples.Parliament) ;;
  *)
    echo "ERROR: unknown library '$lib' (expected PolyFun, ToCslib, ComplexityBackends, or Examples.Parliament)." >&2
    exit 1
    ;;
esac

source_root="${lib//.//}"

if [[ ! -d "$source_root" || ! -f "$source_root.lean" ]]; then
  echo "ERROR: Run this script from inside the PolyFun repository." >&2
  exit 1
fi

untracked_lean_files=()
while IFS= read -r file; do
  if [[ -n "$file" ]]; then
    untracked_lean_files+=("$file")
  fi
done < <(git ls-files --others --exclude-standard -- "$source_root/*.lean")

if (( ${#untracked_lean_files[@]} > 0 )); then
  echo "ERROR: Untracked Lean files under $lib/ are not included in $lib.lean generation." >&2
  echo "Stage them first, then rerun this script:" >&2
  printf '  git add %q\n' "${untracked_lean_files[@]}" >&2
  exit 1
fi

echo "Updating $lib.lean with all tracked imports..."

tmp_file="$(mktemp "${TMPDIR:-/tmp}/polyfun-imports.XXXXXX")"
cleanup() {
  rm -f "$tmp_file"
}
trap cleanup EXIT

# `PolyFun.lean` is a bare import index. The `ToCslib` and `ComplexityBackends` umbrellas are Lake
# library roots in their own right, so they keep the standard file header and a module docstring
# around their generated imports.
umbrella_header() {
  case "$1" in
    Examples.Parliament)
      cat <<'EOF_HEADER'
/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

EOF_HEADER
      ;;
    ToCslib)
      cat <<'EOF_HEADER'
/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

EOF_HEADER
      ;;
    ComplexityBackends)
      cat <<'EOF_HEADER'
/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin, Quang Dao
-/

EOF_HEADER
      ;;
  esac
}

umbrella_docstring() {
  case "$1" in
    Examples.Parliament)
      cat <<'EOF_DOCSTRING'

/-!
# Executable parliamentary procedure and certified draft minutes

A bounded RONR case study of indexed interaction, legal histories, dynamical execution,
and interchangeable IO handlers. See `Examples/Parliament/README.md` for the runnable
walkthrough and the explicit specification and physical-IO proof boundary.
-/
EOF_DOCSTRING
      ;;
    ToCslib)
      cat <<'EOF_DOCSTRING'

/-!
# Extensions of the pinned cslib library

This library stages reusable extensions of the pinned cslib, Mathlib, and core APIs: free-monad
lemmas in cslib's simp normal form, transport of loop combinators along monad morphisms,
`PureForIn` instances, the bridge from Mathlib's complete lattices to core's `Lean.Order`,
single-bit overwrites on bitvectors, and monotonicity of natural-number polynomial evaluation.
It imports core, cslib, and Mathlib only — never `PolyFun`, a concrete complexity backend, or any
downstream oracle or cryptographic semantics. `PolyFun` imports the modules it needs explicitly;
`ComplexityBackends` may do the same.
-/
EOF_DOCSTRING
      ;;
    ComplexityBackends)
      cat <<'EOF_DOCSTRING'

/-!
# Concrete complexity backends for PolyFun realizability

This library hosts optional concrete backends that instantiate PolyFun's abstract quantitative
realizability layer (`PolyFun.Realizability.Quantitative`) with a specific machine model. Each
backend lives in its own subdirectory and is self-contained: `CslibSingleTape` grounds encoded
polynomial-time families, finite-table machine constructions, and a counting separation in cslib's
single-tape Turing machines, then certifies PolyFun step maps with them. The library imports
`PolyFun`, `ToCslib`, cslib, and Mathlib; it is a separate Lake library and is intentionally absent
from the backend-neutral `PolyFun` umbrella.
-/
EOF_DOCSTRING
      ;;
  esac
}

{
  umbrella_header "$lib"
  echo "module"
  echo ""
  git ls-files -- "$source_root/*.lean" \
    | LC_ALL=C sort \
    | sed 's/\.lean//;s,/,.,g;s/^/public import /'
  umbrella_docstring "$lib"
} > "$tmp_file"

mv "$tmp_file" "$source_root.lean"
trap - EXIT

import_count="$(grep -c '^public import ' "$source_root.lean")"
echo "✓ $lib.lean updated with $import_count public imports"
