/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.DomainLaws
public import PolyFun.ITree.Free
public import PolyFun.ITree.WP.Basic

/-!
# One spec across program models

A per-operation spec `Φ : OpSpec F l` is read on several program models, and the readings agree
along the embeddings between them:
* **Free programs.** On a finite program both interaction-tree readings are the fold `wpFold`
  (`ITree.wpTotal_toITree`, `ITree.wpPartial_toITree`). A finite tree has no infinite run, so the
  least and greatest solutions of the one-step equations coincide on it.
* **Larger carriers.** Reading a spec lifted along `ULift` is lifting the reading
  (`ITree.wpTotal_ulift`, `ITree.wpPartial_ulift`), as for the fold.
* **Continuous algebras.** For a continuous algebra, `ITree.denote` is the total reading of the
  algebra seen as a spec (`ITree.denote_eq_wpTotal`). Both are least solutions of the same
  equations. A resumption's denotation is then the total reading of its interaction tree
  (`PFunctor.Resumption.denote_eq_wpTotal`).

Together with the sandwich `ITree.wpTotal_le_le_wpPartial`, this places each reading. Every reading
of a tree that solves the one-step equations lies between the total and partial readings, and all
of them agree with the fold on finite programs.
-/

@[expose] public section

universe uA uB uα w

open OmegaCompletePartialOrder PFunctor

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {l : Type w} [CompleteLattice l]

/-! ## Finite programs -/

section Free

variable {Φ : OpSpec F l} (hΦ : Φ.Monotone)
include hΦ

/-- On a finite program, total correctness is the fold of the spec. -/
theorem wpTotal_toITree (x : FreeM F α) (post : α → l) :
    wpTotal Φ (FreeM.toITree x) post = FreeM.wpFold Φ x post := by
  induction x with
  | pure a =>
    rw [FreeM.toITree_pure, wpTotal_pure hΦ, FreeM.wpFold_pure]
  | lift_bind a r ih =>
    rw [← FreeM.liftBind_eq, FreeM.toITree_liftBind, wpTotal_query hΦ, FreeM.wpFold_liftBind]
    exact congrArg (Φ a) (funext ih)

/-- On a finite program, partial correctness is the fold of the spec. -/
theorem wpPartial_toITree (x : FreeM F α) (post : α → l) :
    wpPartial Φ (FreeM.toITree x) post = FreeM.wpFold Φ x post := by
  induction x with
  | pure a =>
    rw [FreeM.toITree_pure, wpPartial_pure hΦ, FreeM.wpFold_pure]
  | lift_bind a r ih =>
    rw [← FreeM.liftBind_eq, FreeM.toITree_liftBind, wpPartial_query hΦ, FreeM.wpFold_liftBind]
    exact congrArg (Φ a) (funext ih)

end Free

/-! ## Lifting the carrier -/

section ULift

universe w'

variable {Φ : OpSpec F l} (hΦ : Φ.Monotone)
include hΦ

/-- Reading a lifted spec is lifting the reading, with the postcondition read through
`ULift.down`. A reading valued in a small universe, such as `Prop`, so reaches the result universe
that `MAlgOrdered` needs. -/
theorem wpTotal_ulift (t : ITree F α) (post : α → ULift.{w'} l) :
    wpTotal Φ.ulift t post = ⟨wpTotal Φ t fun a => (post a).down⟩ := by
  apply le_antisymm
  · refine wpTotal_le_of_wpStepFun_le
      (X := fun t => (⟨wpTotal Φ t fun a => (post a).down⟩ : ULift.{w'} l))
      (le_of_eq (wpStepFun_eq_self _ _ (fun r => ?_) (fun t => ?_) (fun a k => ?_))) t
    · rw [wpTotal_pure hΦ]
    · rw [wpTotal_step hΦ]
    · rw [wpTotal_query hΦ]
      rfl
  · exact wpTotal_le_of_wpStepFun_le (X := fun t => (wpTotal Φ.ulift t post).down)
      (le_of_eq (wpStepFun_eq_self _ _
        (fun r => by rw [wpTotal_pure hΦ.ulift])
        (fun t => by rw [wpTotal_step hΦ.ulift])
        (fun a k => by rw [wpTotal_query hΦ.ulift]; rfl))) t

/-- Reading a lifted spec partially is lifting the partial reading. -/
theorem wpPartial_ulift (t : ITree F α) (post : α → ULift.{w'} l) :
    wpPartial Φ.ulift t post = ⟨wpPartial Φ t fun a => (post a).down⟩ := by
  apply le_antisymm
  · exact le_wpPartial_of_le_wpStepFun (X := fun t => (wpPartial Φ.ulift t post).down)
      (le_of_eq (wpStepFun_eq_self _ _
        (fun r => by rw [wpPartial_pure hΦ.ulift])
        (fun t => by rw [wpPartial_step hΦ.ulift])
        (fun a k => by rw [wpPartial_query hΦ.ulift]; rfl)).symm) t
  · refine le_wpPartial_of_le_wpStepFun
      (X := fun t => (⟨wpPartial Φ t fun a => (post a).down⟩ : ULift.{w'} l))
      (le_of_eq (wpStepFun_eq_self _ _ (fun r => ?_) (fun t => ?_) (fun a k => ?_)).symm) t
    · rw [wpPartial_pure hΦ]
    · rw [wpPartial_step hΦ]
    · rw [wpPartial_query hΦ]
      rfl

end ULift

end ITree

/-! ## Continuous algebras -/

namespace PFunctor.Resumption.ContinuousAlgebra

variable {F : PFunctor.{uA, uB}} {l : Type w} [CompleteLattice l]

/-- A continuous algebra read as a per-operation spec. -/
def toOpSpec (alg : ContinuousAlgebra F l) : OpSpec F l :=
  fun a k => alg a k

/-- A continuous algebra, read as a per-operation spec, is monotone. -/
theorem toOpSpec_monotone (alg : ContinuousAlgebra F l) : alg.toOpSpec.Monotone :=
  fun a _ _ h => (alg a).monotone h

end PFunctor.Resumption.ContinuousAlgebra

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {l : Type w} [CompleteLattice l]

section Denote

variable (alg : Resumption.ContinuousAlgebra F l)

theorem domainStep_eq_wpStepFun (post : α → l) :
    ⇑(domainStep post alg) = wpStepFun alg.toOpSpec post := by
  funext X t
  simp only [domainStep, ContinuousHom.ofFun_apply, wpStepFun]
  rcases shape' t with ⟨head, next⟩
  cases head <;> rfl

/-- The continuous denotation is the total reading of the algebra, read as a spec: both are least
solutions of the same one-step equations. -/
theorem denote_eq_wpTotal (post : α → l) (t : ITree F α) :
    denote post alg t = wpTotal alg.toOpSpec t post := by
  rw [denote_eq_fix]
  have hfix : (domainStep post alg).fix = (wpStep alg.toOpSpec_monotone post).lfp := by
    refine (ContinuousHom.isLeast_fix (domainStep post alg)).unique ?_
    have h := OrderHom.isLeast_lfp_le (wpStep alg.toOpSpec_monotone post)
    simpa only [wpStep, OrderHom.coe_mk, ← domainStep_eq_wpStepFun] using h
  rw [hfix]
  rfl

end Denote

end ITree

namespace PFunctor.Resumption

universe uA' uB' uα' w'

variable {F : PFunctor.{uA', uB'}} {α : Type uα'} {l : Type w'} [CompleteLattice l]

/-- A resumption's continuous denotation is the total reading of its interaction tree. -/
theorem denote_eq_wpTotal (alg : ContinuousAlgebra F l) (post : α → l) (r : Resumption F α) :
    denote post alg r = ITree.wpTotal alg.toOpSpec r.toITree post := by
  rw [← ITree.denote_toITree, ITree.denote_eq_wpTotal]

end PFunctor.Resumption
