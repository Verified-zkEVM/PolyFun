/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Cslib.Foundations.Data.PFunctor.Free.Fold
import Cslib.Foundations.Data.PFunctor.Free.W
import PolyFun.PFunctor.Free.Basic
import ToCslib.Data.PFunctor.Free.Basic

/-!
# Co-import canaries for cslib's polynomial free-monad modules

cslib's `Free.Fold` and `Free.W` own the fold `PFunctor.FreeM.foldFreeM` and the W-type
equivalence `PFunctor.FreeM.equivWOfIsEmpty`. `ToCslib.Data.PFunctor.Free.Basic` and
`PolyFun.PFunctor.Free.Basic` build on them without redeclaring either, so all four modules import
together. Each example combines a lemma from cslib with one from PolyFun or `ToCslib` through
ordinary imports.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uα uβ uγ

namespace PolyFunTest.ModuleAPI.CslibCoImport

open _root_.PFunctor

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
