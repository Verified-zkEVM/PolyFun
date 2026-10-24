# Importing a Cryptol function

This walk-through follows [`PolyFunCryptolTest/Tutorial/Mix.lean`](../../PolyFunCryptolTest/Tutorial/Mix.lean),
which imports two functions from [`fixtures/Tutorial.cry`](../fixtures/Tutorial.cry):

```cryptol
mix : [8] -> [8]
mix x = (x >>> 3) ^ (x >> 5)

clear : [8] -> [8]
clear x = (x >> 3) ^ (x >> 5)
```

It describes the current workflow, including the parts that are still written by
hand. VCVio's `Interop/Cryptol/Consumer/Demo.lean` continues the same route for
Foundation's `sigma_256_0`. It proves the function equal to VCVio's `ssig0`
and substitutes it inside every adaptive oracle client.

## 1. Export and quote

[`scripts/export_cases.py`](../scripts/export_cases.py) runs the
[pinned exporter](../exporter/README.md) on the requested roots. The exporter
returns the official frontend's typed AST for `mix` and `clear` and their
dependency closure as JSON (`artifacts/references/tutorial.json`). The script
then quotes that JSON as Lean constructor data in
`PolyFunCryptolTest/Tutorial/MixSource.lean`. The parser, type checker and
serializer are trusted at this step; Lean has not checked anything yet.

## 2. Check the import in the kernel

```lean
theorem mix_accepted : check bundle root0 = .ok ⟨_, mixTerm⟩ := by
  with_unfolding_all rfl
```

`SourceElaboration.check` validates scope, kinds, closed constraints and typing,
and returns a typed `Resolved.Term`. The kernel runs it on the exact quoted
bundle. Today the statement names the expected output, `mixTerm`, which is
written out by hand. Each acceptance theorem also raises `maxRecDepth`.

## 3. Prove what the import computes

```lean
def mixNative (x : BitVec 8) : BitVec 8 := x.rotateRight 3 ^^^ (x >>> 5)

theorem mix_correct (x : BitVec 8) :
    DomainResult.applyContinuous (Resolved.denote mixTerm Environment.empty)
      (.value (wordValue x)) = .value (wordValue (mixNative x))
```

The meaning is lazy and partial: `Computation` keeps divergence, errors and
suspended components distinct. On a fully defined input, the proof unfolds the
denotation with the `Resolved.denote_*` equations and the word-operation lemmas,
which is about ten lines here.

## 4. Certify a native implementation and move specifications

`mixFinite` is the same function in the total finite IR. `mixCertified :
Finite.CertifiedFunction` packages the imported source with it, and
`CertifiedFunction.contract_iff` turns any pre/post contract on the imported
source into a statement about `mixNative`. An algebraic fact, `mixNative_xor`,
is proved once on `BitVec` and transferred by rewriting with `mix_correct`.

## 5. State what only the lazy semantics sees

```lean
theorem clear_bot_zero :
    Semantics.indexAt (DomainResult.applyContinuous (Resolved.denote clearTerm Environment.empty) ⊥)
      0 = .value ⟨false⟩ := by
  rw [clearTerm, Resolved.denote_lam_apply]
  rfl
```

Right shifts fill with zeros without reading their input, so bit 0 of `clear` is
defined even when the whole input is undefined. Cryptol's reference evaluator
agrees: `:eval ((undefined : [8]) >> 3) @ 0` is `False`. The normal evaluator
packs words and reports the input's error instead. A total `BitVec` model cannot
state this distinction.

## What is still manual

These manual steps are the targets of the next milestones in the
[model guide](model.md#audited-next-milestones):

| Step | Manual today |
|---|---|
| 1 | A Python quotation of the exported JSON |
| 2 | The expected resolved term, and a recursion-depth override |
| 3 | The proof from the lazy denotation to the native function |
| 4 | The finite implementation, written separately from the source |
