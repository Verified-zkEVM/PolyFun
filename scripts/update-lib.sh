#!/usr/bin/env bash

# Update PolyFun.lean with all imports.
# This script only considers tracked files. New PolyFun/**/*.lean files
# must be staged first.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if [[ ! -d "PolyFun" || ! -f "PolyFun.lean" ]]; then
  echo "ERROR: Run this script from inside the PolyFun repository." >&2
  exit 1
fi

untracked_lean_files=()
while IFS= read -r file; do
  if [[ -n "$file" ]]; then
    untracked_lean_files+=("$file")
  fi
done < <(git ls-files --others --exclude-standard -- 'PolyFun/*.lean')

if (( ${#untracked_lean_files[@]} > 0 )); then
  echo "ERROR: Untracked Lean files under PolyFun/ are not included in PolyFun.lean generation." >&2
  echo "Stage them first, then rerun this script:" >&2
  printf '  git add %q\n' "${untracked_lean_files[@]}" >&2
  exit 1
fi

echo "Updating PolyFun.lean with all tracked imports..."

tmp_file="$(mktemp "${TMPDIR:-/tmp}/polyfun-imports.XXXXXX")"
cleanup() {
  rm -f "$tmp_file"
}
trap cleanup EXIT

git ls-files -- 'PolyFun/*.lean' \
  | LC_ALL=C sort \
  | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$tmp_file"

mv "$tmp_file" PolyFun.lean
trap - EXIT

echo "✓ PolyFun.lean updated with $(wc -l < PolyFun.lean) imports"
