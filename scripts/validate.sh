#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in PolyFun.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_lint=0
run_test=0
run_axioms=0
run_cryptol_external=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--test] [--axioms] [--cryptol-external]

Default checks:
  - lake build PolyFun ToCslib ComplexityBackends PolyFunCryptol PolyFunExamples
    +PolyFunParliamentMain +PolyFunCryptolMain --wfail
  - ./scripts/check-modules.sh
  - ./scripts/check-imports.sh
  - python3 ./scripts/check-docs-integrity.py

Optional checks:
  --lint    Run environment and text-style linters over production, tutorials, and case studies
  --test    Build regressions, run CLI/filesystem tests, and build both separate consumers
  --axioms  Test axiomsweep, then enforce the zero axiom/sorry-debt gate
  --cryptol-external
            Also compare the Cryptol model with the pinned Cryptol 3.6.0 executable
            named by CRYPTOL_BINARY (implies --test). With FOUNDATION_PATH, also run
            the importer canaries through both evaluators. With CRYPTOL_EXPORTER and
            CRYPTOL_SOURCE, regenerate the cases, census and corpus status. With
            CRYPTOL_UPSTREAM_BINARY, reproduce the evaluator audit
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
    --cryptol-external)
      run_test=1
      run_cryptol_external=1
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

if (( run_cryptol_external )); then
  : "${CRYPTOL_BINARY:?Set CRYPTOL_BINARY to the pinned Cryptol 3.6.0 executable}"
fi

echo "# Building project"
lake build PolyFun ToCslib ComplexityBackends PolyFunCryptol PolyFunExamples \
  +PolyFunParliamentMain +PolyFunCryptolMain --wfail

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
    Examples.Tutorials.BoundedController Examples.Tutorials.ScopedPrograms \
    Examples.Tutorials.ScopedExecution Examples.Tutorials.ScopedFamily \
    Examples.Parliament PolyFunParliamentMain PolyFunCryptol PolyFunCryptolMain
fi

if (( run_test )); then
  echo ""
  echo "# Running test library (lake test)"
  lake build PolyFunTest --wfail --iofail
  lake test
  lake -d test/DocumentationConsumer build --wfail
  lake build polyfun-parliament --wfail
  python3 scripts/test-parliament-cli.py
  lake -d test/ParliamentConsumer build --wfail
  lake build PolyFunCryptolTest polyfun-cryptol --wfail --iofail
  cryptol_model_test=(python3 -u PolyFunCryptol/scripts/test_model.py)
  if (( run_cryptol_external )); then cryptol_model_test+=(--cryptol "$CRYPTOL_BINARY"); fi
  "${cryptol_model_test[@]}"
  cryptol_source_test=(python3 -u PolyFunCryptol/scripts/test_source.py)
  if (( run_cryptol_external )) && [[ -n "${FOUNDATION_PATH:-}" ]]; then
    cryptol_source_test+=(--cryptol "$CRYPTOL_BINARY" --foundation "$FOUNDATION_PATH")
  fi
  "${cryptol_source_test[@]}"
  python3 -u PolyFunCryptol/scripts/test_modules.py
  if (( run_cryptol_external )) && [[ -n "${FOUNDATION_PATH:-}" ]]; then
    cryptol_reports="${CRYPTOL_REPORT_DIR:-${TMPDIR:-/tmp}/polyfun-cryptol-validation}"
    mkdir -p "$cryptol_reports"
    if [[ -n "${CRYPTOL_UPSTREAM_BINARY:-}" ]]; then
      python3 -u PolyFunCryptol/scripts/test_evaluators.py --cryptol "$CRYPTOL_BINARY" \
        --upstream-cryptol "$CRYPTOL_UPSTREAM_BINARY" --foundation "$FOUNDATION_PATH" \
        --report "$cryptol_reports/evaluators.json"
      cmp PolyFunCryptol/artifacts/evaluator-audit.json "$cryptol_reports/evaluators.json"
    fi
    if [[ -n "${CRYPTOL_EXPORTER:-}" ]]; then
      : "${CRYPTOL_SOURCE:?Set CRYPTOL_SOURCE to the pinned Cryptol source checkout}"
      cryptol_export=(--exporter "$CRYPTOL_EXPORTER" --foundation "$FOUNDATION_PATH")
      python3 -u PolyFunCryptol/scripts/export_cases.py --check "${cryptol_export[@]}" \
        --cryptol-source "$CRYPTOL_SOURCE"
      python3 -u PolyFunCryptol/scripts/inventory_foundation.py "${cryptol_export[@]}" \
        --out "$cryptol_reports/foundation-inventory.json"
      python3 -u PolyFunCryptol/scripts/corpus.py --all --check "${cryptol_export[@]}" \
        --cryptol-source "$CRYPTOL_SOURCE" --out "$cryptol_reports"
      python3 -u PolyFunCryptol/scripts/test_modules.py --report "$cryptol_reports"
    fi
  fi
fi

if (( run_axioms )); then
  echo ""
  echo "# Building axiom sweep roots"
  lake build PolyFun ToCslib ComplexityBackends PolyFunCryptol PolyFunExamples \
    +PolyFunParliamentMain +PolyFunCryptolMain --wfail

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
    --root Examples.Tutorials.BoundedController --root Examples.Tutorials.ScopedPrograms \
    --root Examples.Tutorials.ScopedExecution --root Examples.Tutorials.ScopedFamily \
    --root Examples.Parliament \
    --root PolyFunParliamentMain --root PolyFunCryptol --check
  # Each executable entry point defines `main`, so the Cryptol one is swept on its own.
  lake exe polyfun-axiomsweep --root PolyFunCryptolMain --check
fi

echo ""
echo "All requested validation checks passed."
