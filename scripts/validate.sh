#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in PolyFun.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0
run_test=0
run_axioms=0
run_examples=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--examples] [--lint] [--test] [--axioms]

Default checks:
  - lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunExamples --wfail
  - ./scripts/check-modules.sh
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py

Optional checks:
  --examples Include the independent Parliament, Notes, and Pipeline packages and their CLI tests
  --lint    Run environment and text-style linters over production, tutorials, and case studies
  --test    Build regressions and the separate documentation consumer
  --axioms  Test axiomsweep, then enforce the zero axiom/sorry-debt gate
EOF
}

for arg in "$@"; do
  case "$arg" in
    --examples) run_examples=1 ;;
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
lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunExamples --wfail

echo ""
echo "# Checking module scopes"
./scripts/check-modules.sh

echo ""
echo "# Checking umbrella imports"
./scripts/check-imports.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/test-docs-integrity.py
python3 ./scripts/check-docs-integrity.py

if (( run_lint )); then
  echo ""
  echo "# Running environment linters (lake lint)"
  lake lint
  lake exe lint-style PolyFun ToCslib ComplexityBackends \
    Examples.Tutorials.Requests Examples.Tutorials.Machines Examples.Tutorials.IndexedPrograms \
    Examples.Tutorials.InteractionTrees Examples.Tutorials.ParallelReports \
    Examples.Tutorials.VersionedRequests Examples.Tutorials.UpdatePolicies \
    Examples.Tutorials.ReviewableWorkflows Examples.Tutorials.FairWorkQueues \
    Examples.Tutorials.BoundedController PolyFunIO
fi

if (( run_test )); then
  echo ""
  echo "# Running test library (lake test)"
  lake build PolyFunTest --wfail --iofail
  lake test
  lake -d test/DocumentationConsumer build --wfail
fi

if (( run_axioms )); then
  echo ""
  echo "# Building axiom sweep roots"
  lake build PolyFun ToCslib ComplexityBackends PolyFunIO PolyFunExamples --wfail

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
    --root Examples.Tutorials.BoundedController --root PolyFunIO --check
fi

if (( run_examples )); then
  for example in Parliament Notes Pipeline; do
    echo "# Validating standalone $example package"
    (
    cd "Examples/$example"
    lake build --wfail
    if (( run_lint )); then
      lake lint
      lake exe lint-style "$example" "${example}Main"
    fi
    if (( run_test )); then
      lake build "${example}Test" --wfail --iofail
      lake test
    fi
    if (( run_axioms )); then
      lake exe polyfun-axiomsweep --root "$example" \
        --root "${example}Main" --baseline ../../scripts/axiom_baseline.json --check
    fi
    )
  done
  if (( run_test )); then
    python3 scripts/test-parliament-cli.py
    python3 scripts/test-notes-cli.py
    python3 scripts/test-pipeline-cli.py
  fi
fi

echo ""
echo "All requested validation checks passed."
