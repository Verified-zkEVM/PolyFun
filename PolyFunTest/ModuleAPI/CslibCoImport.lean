/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Cslib.Foundations.Data.PFunctor.Basic
import Cslib.Foundations.Data.PFunctor.Free.Fold
import Cslib.Foundations.Data.PFunctor.Free.W
import PolyFun.PFunctor.Basic
import PolyFun.PFunctor.Free.Basic
import ToCslib.Data.PFunctor.Free.Basic

/-!
# Co-import canaries for cslib's polynomial modules

cslib's `PFunctor.Basic` owns the monomial abbreviations, `0`, `1`, `P + Q` and `P * Q`; its
`Free.Fold` and `Free.W` own the fold `PFunctor.FreeM.foldFreeM` and the W-type equivalence
`PFunctor.FreeM.equivWOfIsEmpty`. `PolyFun.PFunctor.Basic`, `PolyFun.PFunctor.Free.Basic` and
`ToCslib.Data.PFunctor.Free.Basic` build on them without redeclaring any of these, so all six
modules import together. Each example combines a lemma from cslib with one from PolyFun or
`ToCslib` through ordinary imports.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uα uβ uγ

namespace PolyFunTest.ModuleAPI.CslibCoImport

open _root_.PFunctor

/-! ## Polynomial constructions -/

/-- cslib's `P + Q` is its named sum `PFunctor.add`, whose left directions PolyFun's
`add_B_inl` computes. -/
example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} (a : P.A) :
    PFunctor.add P Q = P + Q ∧ (P + Q).B (.inl a) = P.B a :=
  ⟨add_eq_add P Q, add_B_inl P Q a⟩

/-- cslib's `C_pempty` turns `0` into a constant polynomial, whose positions PolyFun's `C_A`
computes. -/
example : (0 : PFunctor.{uA, uB}).A = PEmpty := by
  rw [← C_pempty, C_A]

/-- Instance search unfolds cslib's reducible abbreviations to `PUnit` and `PEmpty`. -/
example (a : y.{uA, uB}.A) : Unique (y.{uA, uB}.B a) := inferInstance

example (α : Type uA) (a : (C.{uA, uB} α).A) : IsEmpty ((C.{uA, uB} α).B a) := inferInstance

/-! ## Free programs -/

/-- cslib's map-fusion law for the fold composes with `ToCslib`'s constructor-spelled node
equation. -/
example {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (f : α → β) (onValue : β → γ) (onEffect : (a : P.A) → (P.B a → γ) → γ)
    (a : P.A) (cont : P.B a → FreeM P α) :
    FreeM.foldFreeM onValue onEffect (FreeM.map f (FreeM.liftBind a cont)) =
      onEffect a fun b => FreeM.foldFreeM (onValue ∘ f) onEffect (cont b) := by
  rw [FreeM.foldFreeM_map, FreeM.foldFreeM_liftBind]

/-- cslib's W-type round trip applies to a tree transported along a lens by PolyFun's
`FreeM.mapLens`. -/
example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} (lens : Lens P Q)
    (x : FreeM P PEmpty.{uα + 1}) :
    W.toFreeM (FreeM.equivWOfIsEmpty (x.mapLens lens)) = x.mapLens lens := by
  simp

/-- The W-type image of a transported node is the W-node at the lens's position. -/
example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} (lens : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P PEmpty.{uα + 1}) :
    FreeM.toWOfIsEmpty ((FreeM.liftBind a rest).mapLens lens) =
      WType.mk (lens.toFunA a) fun d =>
        FreeM.toWOfIsEmpty ((rest (lens.toFunB a d)).mapLens lens) := by
  rw [FreeM.mapLens_liftBind]
  rfl

end PolyFunTest.ModuleAPI.CslibCoImport
