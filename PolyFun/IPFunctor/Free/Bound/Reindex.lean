/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Bound
public import PolyFun.IPFunctor.Free.Reindex

/-!
# Resource bounds under changes of indexed syntax

Reindexing preserves a budget read through its translated operations. The reverse
implication requires every source response to be represented: a reindexing may
otherwise prune branches. Leaves may change both their types and their universe.
-/

public section

universe uI uJ uA uB uC uD uX uY

namespace IPFunctor.IFreeM

variable {I : Type uI} {J : Type uJ} {P : Endo.{uI, uA, uB} I}
  {Q : Endo.{uJ, uC, uD} J} {f : I → J} {X : I → Type uX} {Y : J → Type uY}
  {B : Type*} {canRoll : (j : J) → Q.A j → B → Prop} {cost : (j : J) → Q.A j → B → B}

/-- Translate a bound using the same validity check and cost at the target operation. -/
theorem IsRollBound.reindex (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    {s : I} {x : IFreeM P X s} {b : B}
    (hx : x.IsRollBound b (fun s a => canRoll (f s) (h.op s a))
      (fun s a => cost (f s) (h.op s a))) :
    (x.reindex h leaf).IsRollBound b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing b with
  | pure _ _ => trivial
  | liftBind s a next ih =>
      rw [reindex_liftBind, isRollBound_liftBind_iff]
      exact ⟨hx.1, fun answer => (isRollBound_cast _ _ _).mpr (ih _ (hx.2 _))⟩

/-- If no source branch is lost, reindexing also reflects the resource bound. -/
theorem isRollBound_reindex_iff (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    (hargs : ∀ s a, Function.Surjective (h.arg s a)) {s : I} (x : IFreeM P X s) (b : B) :
    (x.reindex h leaf).IsRollBound b canRoll cost ↔
      x.IsRollBound b (fun s a => canRoll (f s) (h.op s a))
        (fun s a => cost (f s) (h.op s a)) := by
  refine ⟨?_, IsRollBound.reindex h leaf⟩
  intro hx
  induction x using IFreeM.inductionOn generalizing b with
  | pure _ _ => trivial
  | liftBind s a next ih =>
      rw [reindex_liftBind, isRollBound_liftBind_iff] at hx
      refine ⟨hx.1, fun answer => ?_⟩
      obtain ⟨target, rfl⟩ := hargs s a answer
      exact ih _ _ ((isRollBound_cast _ _ _).mp (hx.2 target))

end IPFunctor.IFreeM
