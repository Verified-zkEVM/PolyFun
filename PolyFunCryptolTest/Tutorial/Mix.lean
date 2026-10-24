/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Import
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
frontend to `PolyFunCryptol/artifacts/references/tutorial.json`. This file then:

1. imports the export with `cryptol_import`, which checks both functions and has the
   kernel re-check that acceptance;
2. certifies `mix` against a native `BitVec` function by native evaluation, and moves
   a pre/post contract and an algebraic property across;
3. proves a fact only the lazy semantics can state: bit 0 of `clear` is defined
   even when its input is undefined. Cryptol's reference evaluator agrees, while
   its normal evaluator, which packs words, reports the input's error.

The [tutorial guide](../../PolyFunCryptol/docs/tutorial.md) explains each step.
-/

public section

namespace Cryptol.Tests.Tutorial

/-! ## Importing

`cryptol_import` decodes the export, checks every root, and declares `Imported.mix` and
`Imported.clear` with their kernel-checked acceptance theorems `Imported.mix.accepted`
and `Imported.clear.accepted`. -/

cryptol_import Imported from "PolyFunCryptol/artifacts/references/tutorial.json"

/-- The import is the resolved term one would write by hand. -/
example : Imported.mix = .lam (.wordLogic .xor (.shift .rotateRight (.var .zero) (.integer 3))
    (.shift .right (.var .zero) (.integer 5))) := rfl

/-! ## Certified meaning on defined inputs -/

/-- The native Lean function that `mix` should compute. -/
@[expose] def mixNative (x : BitVec 8) : BitVec 8 := x.rotateRight 3 ^^^ (x >>> 5)

/-- The imported `mix`, certified against `mixNative`. `simp` evaluates the source
natively for every input; the fundamental lemma supplies the lazy meaning. -/
@[expose] noncomputable def mixCertificate : DataCertificate (.word 8) (.word 8) :=
  Resolved.dataCertificate (.word 8) (.word 8) Imported.mix mixNative
    (by simp [Imported.mix, mixNative])

/-- On every defined input, the imported `mix` returns the native result. -/
theorem mix_correct (x : BitVec 8) :
    DomainResult.applyContinuous (Resolved.denote Imported.mix Environment.empty)
      (.value (wordValue x)) = .value (wordValue (mixNative x)) :=
  mixCertificate.correct x

/-- Any pre/post contract on the imported source is a statement about `mixNative`. -/
theorem mix_contract_iff (pre : BitVec 8 → Prop) (post : BitVec 8 → BitVec 8 → Prop) :
    DataContract (.word 8) (.word 8) (Resolved.denote Imported.mix Environment.empty) pre post ↔
      ∀ x, pre x → post x (mixNative x) :=
  mixCertificate.contract_iff pre post

/-- `mix` maps zero to zero. -/
example : DataContract (.word 8) (.word 8) (Resolved.denote Imported.mix Environment.empty)
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
    DomainResult.applyContinuous (Resolved.denote Imported.mix Environment.empty)
      (.value (wordValue (x ^^^ y))) = .value (wordValue (mixNative x ^^^ mixNative y)) := by
  rw [mix_correct, mixNative_xor]

/-! ## A fact about laziness -/

/-- Bit 0 of `clear` is defined, and false, even when its input is undefined. -/
theorem clear_bot_zero :
    Semantics.indexAt
      (DomainResult.applyContinuous (Resolved.denote Imported.clear Environment.empty) ⊥) 0 =
        .value ⟨false⟩ := by
  rw [Imported.clear, Resolved.denote_lam_apply]
  rfl

end Cryptol.Tests.Tutorial
