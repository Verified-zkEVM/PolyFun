# External tooling and committed evidence

The official Cryptol parser, renamer, type checker and module loader, together
with the [typed-AST exporter](../exporter/README.md), are external assumptions.
Lean checks the exact artifact it receives: decoding, scopes and kinds, linking,
expression typing, and kernel-checked acceptance equations for quoted imports.
A transformation after that boundary, such as the official specializer's output,
is a candidate whose correspondence must be proved in Lean before a certificate
is reused. Retyping a candidate is insufficient.

The [evaluator survey](evaluators.md) explains the semantic anchor: Cryptol's
documented lazy reference semantics, with backend differences recorded as
versioned observations rather than changes to the model.

## Pins

[`scripts/pins.py`](../scripts/pins.py) names every external revision:

| Pin | Revision |
|---|---|
| Cryptol (exporter, reference and normal evaluators) | `61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b` |
| Upstream Cryptol (evaluator audit only) | `51405420cb90cf9959ca4349eea0ae8b77487855` |
| Foundation | `7d0528bd998682788f4e23661f2829298f9e47db` |

Drivers refuse a Foundation checkout at another revision or with modified
tracked files, and a Cryptol source tree whose diff is not exactly the reviewed
compatibility patch. Downstream bridges import `pins.py`, `frontend.py` and
`quote_reference.py` from the package checkout instead of restating them.

## Drivers and committed outputs

| Script | Inputs | Committed output |
|---|---|---|
| `export_cases.py` | Exporter, Foundation, patched Cryptol source | `artifacts/references/{numeric-cases,class-cases,import-canaries,manifest}.json`, `artifacts/modules/canaries.json`, `PolyFunCryptolTest/Translation/ImportedSource.lean` |
| `corpus.py --all` | Exporter, Foundation, patched Cryptol source | `artifacts/foundation-status.json`, `artifacts/elaboration.json` |
| `inventory_foundation.py` | Exporter, Foundation | None; the complete census goes to the report directory |
| `test_evaluators.py` | Both Cryptol binaries, Foundation | `artifacts/evaluator-audit.json` (152 observations) |
| `test_model.py` | Optionally the Cryptol binary | None; model fixtures and word-boundary cases |
| `test_source.py` | Optionally the Cryptol binary and Foundation | None; cases, typed canaries and malformed-input rejection |
| `test_modules.py` | Optionally a corpus report directory | None; module canaries, diagnoses and, with a report, Foundation module checks |

The complete corpus report and the selected Foundation module bundles are large,
so `corpus.py` writes them to a report directory instead of the tree. The
committed [Foundation status](compatibility.md) keeps the per-instance blockers
and the language features they need.

The fixtures are PolyFun's own: `fixtures/ImportCanaries.cry` exercises the typed
single-root importer, and `fixtures/{ModuleLoops,ModuleCanaries}.cry` exercise
whole-module linking, elaboration and diagnosis offline.

## Validation

Ordinary validation (`./scripts/validate.sh --test`) runs the offline tests
against the committed artifacts without GHC, Cabal, Cryptol or network access.
External validation regenerates and compares everything:

```bash
CRYPTOL_BINARY=/path/to/cryptol-3.6.0/bin/cryptol \
FOUNDATION_PATH=/path/to/Foundation \
CRYPTOL_EXPORTER=/path/to/cryptol-lean-export \
CRYPTOL_SOURCE=/path/to/patched/cryptol \
CRYPTOL_UPSTREAM_BINARY=/path/to/upstream/cryptol \
  ./scripts/validate.sh --test --cryptol-external
```

Each variable after `CRYPTOL_BINARY` enables more checks; see the validation
wrapper's usage text. `CRYPTOL_REPORT_DIR` chooses the report directory.

## What stays downstream

VCVio's `Interop/Cryptol` keeps the Foundation algorithm artifacts and their
generators: the SHA-2/SHA-3/AES/CRC reference bundles, the quoted scalar and
specialization imports, the `Imperative` module quotation, the older
`:extract-coq` extraction, and the conformance and probability theorems built
on them.
