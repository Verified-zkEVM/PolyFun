#!/usr/bin/env bash

# Update a library's umbrella module with all public imports.
#
#   ./scripts/update-lib.sh            # regenerates PolyFun.lean
#   ./scripts/update-lib.sh ToCslib    # regenerates ToCslib.lean
#
# This script only considers tracked files. New <Lib>/**/*.lean files
# must be staged first.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

lib="${1:-PolyFun}"
case "$lib" in
  PolyFun|ToCslib) ;;
  *)
    echo "ERROR: unknown library '$lib' (expected PolyFun or ToCslib)." >&2
    exit 1
    ;;
esac

if [[ ! -d "$lib" || ! -f "$lib.lean" ]]; then
  echo "ERROR: Run this script from inside the PolyFun repository." >&2
  exit 1
fi

untracked_lean_files=()
while IFS= read -r file; do
  if [[ -n "$file" ]]; then
    untracked_lean_files+=("$file")
  fi
done < <(git ls-files --others --exclude-standard -- "$lib/*.lean")

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

# `PolyFun.lean` is a bare import index. The `ToCslib` umbrella is a Lake library root in its own
# right, so it keeps the standard file header and a module docstring around its generated imports.
umbrella_header() {
  case "$1" in
    ToCslib)
      cat <<'EOF_HEADER'
/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/

EOF_HEADER
      ;;
  esac
}

umbrella_docstring() {
  case "$1" in
    ToCslib)
      cat <<'EOF_DOCSTRING'

/-!
# Extensions of the pinned cslib library

This library stages reusable extensions of the pinned cslib API: free-monad lemmas in cslib's
simp normal form, transport of loop combinators along monad morphisms, `PureForIn` instances,
the bridge from Mathlib's complete lattices to core's `Lean.Order`, and local machine and
complexity theory (encoded polynomial-time families, machine constructions, and counting
separation). It imports cslib and Mathlib only — never PolyFun's realizability theory or any
downstream oracle or cryptographic semantics. `PolyFun` imports the free-monad slice
explicitly; optional backend libraries import the machine modules without adding concrete
machine extensions to the generic `PolyFun` umbrella.
-/
EOF_DOCSTRING
      ;;
  esac
}

{
  umbrella_header "$lib"
  echo "module"
  echo ""
  git ls-files -- "$lib/*.lean" \
    | LC_ALL=C sort \
    | sed 's/\.lean//;s,/,.,g;s/^/public import /'
  umbrella_docstring "$lib"
} > "$tmp_file"

mv "$tmp_file" "$lib.lean"
trap - EXIT

import_count="$(grep -c '^public import ' "$lib.lean")"
echo "✓ $lib.lean updated with $import_count public imports"
