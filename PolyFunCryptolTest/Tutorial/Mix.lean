/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptolTest.Tutorial.MixSource
public import PolyFunCryptol.Translation.SourceElaboration
public import PolyFunCryptol.Translation.DataCertificate
public import PolyFunCryptol.Model.ResolvedLaws
public import PolyFunCryptol.Model.ResolvedNative
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types

/-!
# Importing a Cryptol function

`PolyFunCryptol/fixtures/Tutorial.cry` defines two 8-bit functions:

```cryptol
mix x = (x >>> 3) ^ (x >> 5)
clear x = (x >> 3) ^ (x >> 5)
```

`PolyFunCryptol/scripts/export_cases.py` exports them through the official
frontend and quotes the result as `MixSource`. This file then:

1. checks the quoted import in the kernel, against an explicitly written
   resolved term;
2. proves that `mix` computes a native `BitVec` function on every defined input;
3. packages that native function as a certified implementation and moves a
   pre/post contract and an algebraic property across;
4. proves a fact only the lazy semantics can state: bit 0 of `clear` is defined
   even when its input is undefined. Cryptol's reference evaluator agrees, while
   its normal evaluator, which packs words, reports the input's error.

The [tutorial guide](../../PolyFunCryptol/docs/tutorial.md) explains each step.
-/

public section

namespace Cryptol.Tests.Tutorial

open Translation SourceElaboration MixSource

/-! ## Checking the import -/

/-- The resolved term the checker must produce for `mix`. -/
@[expose] def mixTerm : Resolved.Term [] (.arrow (wordTy 8) (wordTy 8)) :=
  .lam (.wordLogic .xor (.shift .rotateRight (.var .zero) (.integer 3))
    (.shift .right (.var .zero) (.integer 5)))

/-- The resolved term the checker must produce for `clear`. -/
@[expose] def clearTerm : Resolved.Term [] (.arrow (wordTy 8) (wordTy 8)) :=
  .lam (.wordLogic .xor (.shift .right (.var .zero) (.integer 3))
    (.shift .right (.var .zero) (.integer 5)))

/-! Kernel reduction runs the checker over the complete quoted bundle, whose nested
constructor data exceeds the default recursion depth of the reducer. -/

set_option maxRecDepth 10000 in
/-- The exported `mix` passes scope, kind, constraint and typing checks. -/
theorem mix_accepted : check bundle root0 = .ok ⟨_, mixTerm⟩ := by
  with_unfolding_all rfl

set_option maxRecDepth 10000 in
/-- The exported `clear` passes the same checks. -/
theorem clear_accepted : check bundle root1 = .ok ⟨_, clearTerm⟩ := by
  with_unfolding_all rfl

/-! ## Certified meaning on defined inputs -/

/-- The native Lean function that `mix` should compute. -/
@[expose] def mixNative (x : BitVec 8) : BitVec 8 := x.rotateRight 3 ^^^ (x >>> 5)

/-- The imported `mix`, certified against `mixNative`. `simp` evaluates the source
natively for every input; the fundamental lemma supplies the lazy meaning. -/
@[expose] noncomputable def mixCertificate : DataCertificate (.word 8) (.word 8) :=
  Resolved.dataCertificate (.word 8) (.word 8) mixTerm mixNative (by simp [mixTerm, mixNative])

/-- On every defined input, the imported `mix` returns the native result. -/
theorem mix_correct (x : BitVec 8) :
    DomainResult.applyContinuous (Resolved.denote mixTerm Environment.empty)
      (.value (wordValue x)) = .value (wordValue (mixNative x)) :=
  mixCertificate.correct x

/-- Any pre/post contract on the imported source is a statement about `mixNative`. -/
theorem mix_contract_iff (pre : BitVec 8 → Prop) (post : BitVec 8 → BitVec 8 → Prop) :
    DataContract (.word 8) (.word 8) (Resolved.denote mixTerm Environment.empty) pre post ↔
      ∀ x, pre x → post x (mixNative x) :=
  mixCertificate.contract_iff pre post

/-- `mix` maps zero to zero. -/
example : DataContract (.word 8) (.word 8) (Resolved.denote mixTerm Environment.empty)
    (fun x : BitVec 8 => x = 0) (fun _ (r : BitVec 8) => r = 0) := by
  rw [mix_contract_iff]
  rintro x rfl
  decide

/-! ## Transporting a property -/

/-- The native function distributes over exclusive-or. -/
theorem mixNative_xor (x y : BitVec 8) : mixNative (x ^^^ y) = mixNative x ^^^ mixNative y := by
  simp only [mixNative, BitVec.ushiftRight_xor_distrib]
  rw [show (x ^^^ y).rotateRight 3 = x.rotateRight 3 ^^^ y.rotateRight 3 by
    ext i; simp [BitVec.getElem_rotateRight]; split <;> simp]
  ac_rfl

/-- So does the imported `mix`, on defined inputs. -/
theorem mix_xor (x y : BitVec 8) :
    DomainResult.applyContinuous (Resolved.denote mixTerm Environment.empty)
      (.value (wordValue (x ^^^ y))) = .value (wordValue (mixNative x ^^^ mixNative y)) := by
  rw [mix_correct, mixNative_xor]

/-! ## A fact about laziness -/

/-- Bit 0 of `clear` is defined, and false, even when its input is undefined. -/
theorem clear_bot_zero :
    Semantics.indexAt (DomainResult.applyContinuous (Resolved.denote clearTerm Environment.empty) ⊥)
      0 = .value ⟨false⟩ := by
  rw [clearTerm, Resolved.denote_lam_apply]
  rfl

end Cryptol.Tests.Tutorial
