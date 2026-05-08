#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in PolyFun.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint]

Default checks:
  - lake build
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py

Optional checks:
  --lint   Run ./scripts/lint-style.sh
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      run_lint=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "ERROR: Unknown flag: $arg" >&2
      usage >&2
      exit 1
      ;;
  esac
done

echo "# Building project"
lake build

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

if (( run_lint )); then
  echo ""
  echo "# Running Lean style lint"
  ./scripts/lint-style.sh
fi

echo ""
echo "All requested validation checks passed."
