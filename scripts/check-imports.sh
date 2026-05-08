#!/usr/bin/env bash

# Check whether PolyFun.lean matches the tracked PolyFun/**/*.lean file set.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "Checking if all imports are up to date..."

backup_file="$(mktemp "${TMPDIR:-/tmp}/PolyFun.lean.backup.XXXXXX")"
cp PolyFun.lean "$backup_file"

restore_original() {
  if [[ -f "$backup_file" ]]; then
    mv "$backup_file" PolyFun.lean
  fi
}
trap restore_original EXIT

./scripts/update-lib.sh

if git diff --quiet -- PolyFun.lean; then
  echo "✓ All imports are up to date!"
  exit 0
fi

echo "❌ Import file is out of date!"
echo "Differences found:"
git diff -- PolyFun.lean
echo ""
echo "To fix this, run: ./scripts/update-lib.sh"
exit 1
