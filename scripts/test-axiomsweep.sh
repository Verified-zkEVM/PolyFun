#!/usr/bin/env bash

# Execute falsifiable fixtures for the kernel-level axiom sweep.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FIXTURE_TMP="$(mktemp -d "${TMPDIR:-/tmp}/polyfun-axiomsweep.XXXXXX")"
trap 'rm -rf -- "$FIXTURE_TMP"' EXIT

expect_status() {
  local expected="$1"
  local label="$2"
  shift 2
  local log="$FIXTURE_TMP/${label}.log"
  local actual=0
  "$@" >"$log" 2>&1 || actual=$?
  if [[ "$actual" -ne "$expected" ]]; then
    echo "ERROR: $label returned $actual; expected $expected" >&2
    sed -n '1,160p' "$log" >&2
    return 1
  fi
}

EMPTY_BASELINE="$FIXTURE_TMP/empty.json"
NONEMPTY_BASELINE="$FIXTURE_TMP/nonempty.json"
INVALID_BASELINE="$FIXTURE_TMP/invalid.json"
MISSING_BASELINE="$FIXTURE_TMP/missing.json"
CLEAN_REPORT="$FIXTURE_TMP/clean.json"
TAINTED_REPORT="$FIXTURE_TMP/tainted.json"
TAINTED_REPORT_2="$FIXTURE_TMP/tainted-2.json"
UNIMPORTED_REPORT="$FIXTURE_TMP/unimported.json"

printf '{"sorry": [], "nonstandard": []}\n' >"$EMPTY_BASELINE"
printf '{"sorry": ["preauthorized.future"], "nonstandard": []}\n' >"$NONEMPTY_BASELINE"
printf '{not-json}\n' >"$INVALID_BASELINE"

lake build PolyFunAxiomSweepTestFixtures
lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean --out "$CLEAN_REPORT"
lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Tainted --out "$TAINTED_REPORT"
lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Tainted --out "$TAINTED_REPORT_2"
lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Unimported --out "$UNIMPORTED_REPORT"

cmp "$TAINTED_REPORT" "$TAINTED_REPORT_2"

python3 - "$CLEAN_REPORT" "$TAINTED_REPORT" "$UNIMPORTED_REPORT" <<'PY'
import json
import sys

clean_path, tainted_path, unimported_path = sys.argv[1:]

with open(clean_path, encoding="utf-8") as stream:
    clean = json.load(stream)
with open(tainted_path, encoding="utf-8") as stream:
    tainted = json.load(stream)
with open(unimported_path, encoding="utf-8") as stream:
    unimported = json.load(stream)

clean_entries = {entry["name"]: entry for entry in clean["declarations"]}
tainted_entries = {entry["name"]: entry for entry in tainted["declarations"]}
unimported_entries = {entry["name"]: entry for entry in unimported["declarations"]}

assert clean_entries
assert all(not entry["axioms"] for entry in clean_entries.values())

prefix = "PolyFunAxiomSweepTestFixtures.Tainted."
direct = tainted_entries[prefix + "directSorry"]["axioms"]
transitive = tainted_entries[prefix + "transitiveSorry"]["axioms"]
assert "sorryAx" in direct
assert "sorryAx" in transitive

axiom_in_type = tainted_entries[prefix + "axiomInType"]["axioms"]
assert prefix + "typeIndex" in axiom_in_type

mutual_right = tainted_entries[prefix + "MutualRight"]["axioms"]
assert prefix + "mutualAxiom" in mutual_right

all_axioms = {
    axiom
    for entry in tainted_entries.values()
    for axiom in entry["axioms"]
}
generated = prefix + "Generated._native.native_decide"
generated_raw = generated + ".ax_12_34"
assert generated in all_axioms
assert generated_raw not in all_axioms
assert prefix + "Collision._native.native_decide.ax_12_extra" in all_axioms
assert prefix + "Collision._native.native_decide.ax_x_34" in all_axioms
assert prefix + "Collision._native.native_decide.ax_12_34.extra" in all_axioms

hidden = "PolyFunAxiomSweepTestFixtures.Unimported.hiddenSorry"
assert hidden not in tainted_entries
assert hidden in unimported_entries
assert "sorryAx" in unimported_entries[hidden]["axioms"]
PY

expect_status 0 clean-check \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --check --baseline "$EMPTY_BASELINE"
expect_status 1 tainted-check \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Tainted \
    --check --baseline "$EMPTY_BASELINE"
expect_status 2 preauthorized-taint \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Tainted \
    --check --baseline "$NONEMPTY_BASELINE"
expect_status 2 stale-debt \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --check --baseline "$NONEMPTY_BASELINE"
expect_status 2 missing-baseline \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --check --baseline "$MISSING_BASELINE"
expect_status 2 invalid-baseline \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --check --baseline "$INVALID_BASELINE"
expect_status 2 conflicting-flags \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --check --update-baseline --baseline "$EMPTY_BASELINE"

cp "$NONEMPTY_BASELINE" "$FIXTURE_TMP/shrink.json"
expect_status 0 shrink-baseline \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Clean \
    --update-baseline --baseline "$FIXTURE_TMP/shrink.json"
cmp "$EMPTY_BASELINE" "$FIXTURE_TMP/shrink.json"

cp "$EMPTY_BASELINE" "$FIXTURE_TMP/growth.json"
cp "$FIXTURE_TMP/growth.json" "$FIXTURE_TMP/growth-before.json"
expect_status 1 reject-baseline-growth \
  lake exe polyfun-axiomsweep --root PolyFunAxiomSweepTestFixtures.Tainted \
    --update-baseline --baseline "$FIXTURE_TMP/growth.json"
cmp "$FIXTURE_TMP/growth-before.json" "$FIXTURE_TMP/growth.json"

echo "✓ Axiom sweep executable fixture matrix passed."
