#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in PolyFun.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0
run_test=0
run_axioms=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--test] [--axioms]

Default checks:
  - lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunProbability PolyFunExamples +PolyFunParliamentMain --wfail
  - ./scripts/check-modules.sh
  - ./scripts/check-imports.sh
  - uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py

Optional checks:
  --lint    Run environment and text-style linters over production, tutorials, and case studies
  --test    Build regressions, run CLI/filesystem tests, and build both separate consumers
  --axioms  Test axiomsweep, then enforce the zero axiom/sorry-debt gate
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      run_lint=1
      ;;
    --test)
      run_test=1
      ;;
    --axioms)
      run_axioms=1
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
lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunProbability PolyFunExamples +PolyFunParliamentMain --wfail

echo ""
echo "# Checking module scopes"
./scripts/check-modules.sh

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
uv run --no-project --python 3.12 python ./scripts/test-docs-integrity.py
uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py

if (( run_lint )); then
  echo ""
  echo "# Running environment linters (runLinter, one process per lintDriverArgs root)"
  # One process per root, as in CI: a single `lake lint` keeps every root's imports alive and
  # reads each later root's oleans into memory instead of mapping them (docs/development/linting.md).
  lint_roots="$(uv run --no-project --python 3.12 python -c \
    "import tomllib; print('\n'.join(tomllib.load(open('lakefile.toml', 'rb'))['lintDriverArgs']))")"
  for root in $lint_roots; do
    lake exe runLinter "$root"
  done
  lake exe lint-style PolyFun ToCslib ComplexityBackends \
    Examples.Tutorials.Requests Examples.Tutorials.Machines Examples.Tutorials.IndexedPrograms \
    Examples.Tutorials.InteractionTrees Examples.Tutorials.ParallelReports \
    Examples.Tutorials.VersionedRequests Examples.Tutorials.UpdatePolicies \
    Examples.Tutorials.ReviewableWorkflows Examples.Tutorials.FairWorkQueues \
    Examples.Tutorials.BoundedController PolyFunIO PolyFunProbability \
    Examples.Parliament PolyFunParliamentMain
fi

if (( run_test )); then
  echo ""
  echo "# Running test library (lake test)"
  lake build PolyFunTest --wfail --iofail
  lake test
  lake -d test/DocumentationConsumer build --wfail
  lake build polyfun-parliament --wfail
  uv run --no-project --python 3.12 python scripts/test-parliament-cli.py
  lake -d test/ParliamentConsumer build --wfail
fi

if (( run_axioms )); then
  echo ""
  echo "# Building axiom sweep roots"
  lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunProbability PolyFunExamples +PolyFunParliamentMain --wfail

  echo ""
  echo "# Testing the axiom sweep tool"
  ./scripts/test-axiomsweep.sh

  echo ""
  echo "# Enforcing zero axiom/sorry debt"
  lake exe polyfun-axiomsweep --root PolyFun --root ToCslib --root ComplexityBackends \
    --root Examples.Tutorials.Requests --root Examples.Tutorials.Machines \
    --root Examples.Tutorials.IndexedPrograms --root Examples.Tutorials.InteractionTrees \
    --root Examples.Tutorials.ParallelReports --root Examples.Tutorials.VersionedRequests \
    --root Examples.Tutorials.UpdatePolicies \
    --root Examples.Tutorials.ReviewableWorkflows --root Examples.Tutorials.FairWorkQueues \
    --root Examples.Tutorials.BoundedController \
    --root Examples.Parliament \
    --root PolyFunParliamentMain --root PolyFunIO --root PolyFunProbability --check
fi

echo ""
echo "All requested validation checks passed."
