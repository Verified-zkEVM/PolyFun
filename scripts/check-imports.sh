#!/usr/bin/env bash

# Check whether each umbrella module (PolyFun.lean, ToCslib.lean) matches the
# tracked <Lib>/**/*.lean file set.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

status=0

for lib in PolyFun ToCslib; do
  echo "Checking if all $lib imports are up to date..."

  backup_file="$(mktemp "${TMPDIR:-/tmp}/$lib.lean.backup.XXXXXX")"
  cp "$lib.lean" "$backup_file"

  ./scripts/update-lib.sh "$lib"

  if cmp -s "$backup_file" "$lib.lean"; then
    echo "✓ All $lib imports are up to date!"
  else
    echo "❌ $lib.lean is out of date!"
    echo "Differences found:"
    diff -u "$backup_file" "$lib.lean" || true
    echo ""
    echo "To fix this, run: ./scripts/update-lib.sh $lib"
    status=1
  fi

  mv "$backup_file" "$lib.lean"
done

exit "$status"
