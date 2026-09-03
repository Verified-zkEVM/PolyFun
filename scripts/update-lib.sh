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

{
  echo "module"
  echo ""
  git ls-files -- "$lib/*.lean" \
    | LC_ALL=C sort \
    | sed 's/\.lean//;s,/,.,g;s/^/public import /'
} > "$tmp_file"

mv "$tmp_file" "$lib.lean"
trap - EXIT

import_count="$(grep -c '^public import ' "$lib.lean")"
echo "✓ $lib.lean updated with $import_count public imports"
