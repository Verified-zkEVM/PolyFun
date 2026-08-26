/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Resumption
public import PolyFun.PFunctor.M.WellFounded

/-!
# Well-founded resumptions

A resumption is well-founded when its underlying M-type has no infinite path.
This is precisely the image of the canonical embedding of finite free programs.
The equivalence in this file is the fixed-point bridge
`FreeM P α ≃ W (P + C α) ≃ {r : M (P + C α) // WellFounded r}`.
-/

@[expose] public section

universe uA uB uα

namespace PFunctor

attribute [local implicit_reducible] PFunctor.Obj PFunctor.W
  PFunctor.W.head PFunctor.W.children

namespace Resumption

variable {P : PFunctor.{uA, uB}} {α : Type uα}

/-- A resumption is qualitatively well-founded when every chain of visible
queries eventually reaches a return. This does not impose a uniform depth
bound across all branches. -/
abbrev WellFounded (computation : Resumption P α) : Prop :=
  M.WellFounded computation

/-- An immediate return is well-founded. -/
theorem wellFounded_pure (value : α) :
    WellFounded (pure (p := P) value) := by
  have hdest : M.dest (pure (p := P) value) =
      ⟨Sum.inr value, PEmpty.elim⟩ := by
    rw [← pack_dest, dest_pure, pack_inl]
  exact (M.wellFounded_iff_of_dest
    (pure (p := P) value) (Sum.inr value) PEmpty.elim hdest).2
      fun direction => direction.elim

/-- A query resumption is well-founded exactly when all its continuations are
well-founded. -/
theorem wellFounded_query_iff (position : P.A)
    (next : P.B position → Resumption P α) :
    WellFounded (query position next) ↔
      ∀ direction, WellFounded (next direction) := by
  apply M.wellFounded_iff_of_dest
    (query position next) (Sum.inl position) next
  rw [← pack_dest, dest_query, pack_inr]

end Resumption

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uα}

/-- The direct finite-program embedding is the canonical map from the
query-or-return W-type into its M-type. -/
theorem toResumption_eq_toM_toWWithReturn (program : FreeM P α) :
    toResumption program = W.toM (toWWithReturn program) := by
  induction program with
  | pure value =>
      apply M.eq_of_dest_eq
      rw [← Resumption.pack_dest, dest_toResumption_pure, W.dest_toM,
        toWWithReturn_pure]
      unfold Resumption.pack W.head W.children
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact direction.elim
  | lift_bind position next ih =>
      apply M.eq_of_dest_eq
      change M.dest (toResumption (FreeM.liftBind position next)) =
        M.dest (W.toM (toWWithReturn (FreeM.liftBind position next)))
      rw [← Resumption.pack_dest, dest_toResumption_liftBind,
        W.dest_toM, toWWithReturn_liftBind]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact ih direction

/-- Every finite free program embeds as a well-founded resumption. -/
theorem wellFounded_toResumption (program : FreeM P α) :
    Resumption.WellFounded (toResumption program) := by
  rw [toResumption_eq_toM_toWWithReturn]
  exact W.wellFounded_toM _

/-- Finite free programs are exactly the well-founded resumptions. -/
def equivWellFoundedResumption :
    FreeM P α ≃ {computation : Resumption P α //
      Resumption.WellFounded computation} :=
  equivWWithReturn.trans W.equivWellFoundedM

@[simp] theorem equivWellFoundedResumption_coe (program : FreeM P α) :
    (equivWellFoundedResumption program).1 = toResumption program := by
  exact (toResumption_eq_toM_toWWithReturn program).symm

@[simp] theorem equivWellFoundedResumption_symm_apply
    (computation : Resumption P α)
    (wellFounded : Resumption.WellFounded computation) :
    toResumption
        (equivWellFoundedResumption.symm ⟨computation, wellFounded⟩) =
      computation := by
  have h := equivWellFoundedResumption.apply_symm_apply
    ⟨computation, wellFounded⟩
  rw [← equivWellFoundedResumption_coe]
  exact congrArg Subtype.val h

/-- A resumption lies in the finite-program image exactly when it is
well-founded. -/
theorem exists_toResumption_iff (computation : Resumption P α) :
    (∃ program : FreeM P α, toResumption program = computation) ↔
      Resumption.WellFounded computation := by
  constructor
  · rintro ⟨program, rfl⟩
    exact wellFounded_toResumption program
  · intro wellFounded
    exact ⟨equivWellFoundedResumption.symm ⟨computation, wellFounded⟩,
      equivWellFoundedResumption_symm_apply computation wellFounded⟩

end FreeM
end PFunctor
