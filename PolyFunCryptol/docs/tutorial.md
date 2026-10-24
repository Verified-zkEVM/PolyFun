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

## 3. Certify what the import computes

```lean
def mixNative (x : BitVec 8) : BitVec 8 := x.rotateRight 3 ^^^ (x >>> 5)

noncomputable def mixCertificate : DataCertificate (.word 8) (.word 8) :=
  Resolved.dataCertificate (.word 8) (.word 8) mixTerm mixNative (by simp [mixTerm, mixNative])

theorem mix_correct (x : BitVec 8) :
    DomainResult.applyContinuous (Resolved.denote mixTerm Environment.empty)
      (.value (wordValue x)) = .value (wordValue (mixNative x)) :=
  mixCertificate.correct x
```

The meaning is lazy and partial: `Computation` keeps divergence, errors and
suspended components distinct. The proof never unfolds it. `Resolved.native`
evaluates the same syntax in native values, and `simp` runs that evaluation on
`mix` for a symbolic input. The fundamental lemma of logical relations
(`Resolved.denote_agrees`) then says that the lazy meaning represents whatever
native evaluation returns. `Resolved.native_related` proves this one constructor
at a time, once for every program.

## 4. Move specifications

`DataCertificate` is PolyFun's generic `Control.Semantics.CertifiedMeaning` at
Cryptol's data embedding, so its `contract_iff` turns any pre/post contract on
the imported source into a statement about `mixNative`:

```lean
theorem mix_contract_iff (pre : BitVec 8 → Prop) (post : BitVec 8 → BitVec 8 → Prop) :
    DataContract (.word 8) (.word 8) (Resolved.denote mixTerm Environment.empty) pre post ↔
      ∀ x, pre x → post x (mixNative x) :=
  mixCertificate.contract_iff pre post
```

An algebraic fact, `mixNative_xor`, is proved once on `BitVec` and transferred by
rewriting with `mix_correct`.

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
| 3 | Nothing: native evaluation certifies the lazy meaning |
| 4 | Nothing: the certificate's implementation is `mixNative` itself |
