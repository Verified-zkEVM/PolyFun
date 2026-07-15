/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Events.Exception
public import PolyFun.ITree.Bisim.Bind

/-! # Laws for exception interpretation

Exact computation rules for `ITree.interpExcept` and `ITree.runExcept`.
The first exception terminates the interpretation as `Except.error`; external
events and silent steps are preserved.
-/

@[expose] public section

universe uε uEA uB uα uβ

namespace ITree

variable {ε : Type uε} {E : PFunctor.{uEA, uB}} {α : Type uα}

@[simp] theorem interpExcept_pure (r : α) :
    interpExcept (ε := ε) (E := E)
      (pure (F := (ExceptE.{uε, uB} ε + E :
        PFunctor.{max uε uEA, uB})) r) =
      pure (.ok r) := by
  have hstep : interpExceptStep
      (pure (F := (ExceptE.{uε, uB} ε + E :
        PFunctor.{max uε uEA, uB})) r) =
      ⟨.pure (.ok r), PEmpty.elim⟩ := by
    simp [interpExceptStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpExcept, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.pure
  rw [PFunctor.M.dest_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem interpExcept_step
    (t : ITree (ExceptE.{uε, uB} ε + E :
      PFunctor.{max uε uEA, uB}) α) :
    interpExcept (step t) = step (interpExcept t) := by
  have hstep : interpExceptStep (step t) =
      ⟨.step, fun _ => t⟩ := by
    simp [interpExceptStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpExcept, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.step
  rw [PFunctor.M.dest_mk]
  rfl

@[simp] theorem interpExcept_throw (e : ε)
    (k : PEmpty.{uB + 1} →
      ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :
    interpExcept (query (.inl e) k) = pure (.error e) := by
  have hstep : interpExceptStep (query (.inl e) k) =
      ⟨.pure (.error e), PEmpty.elim⟩ := by
    simp [interpExceptStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpExcept, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.pure
  rw [PFunctor.M.dest_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem interpExcept_query_external (e : E.A)
    (k : E.B e →
      ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :
    interpExcept (query (.inr e) k) =
      query e (fun b => interpExcept (k b)) := by
  have hstep : interpExceptStep (query (.inr e) k) =
      ⟨.query e, k⟩ := by
    simp [interpExceptStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpExcept, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.query
  rw [PFunctor.M.dest_mk]
  rfl

/-- Exception interpretation is the canonical exception-transformer monad
morphism: a prior error bypasses the continuation. -/
theorem interpExcept_bind
    {β : Type uβ}
    (t : ITree (ExceptE.{uε, uB} ε + E :
      PFunctor.{max uε uEA, uB}) α)
    (k : α → ITree (ExceptE.{uε, uB} ε + E :
      PFunctor.{max uε uEA, uB}) β) :
    interpExcept (bind t k) =
      bind (interpExcept t) (fun
        | .error e => pure (.error e)
        | .ok a => interpExcept (k a)) := by
  let next : Except ε α → ITree E (Except ε β)
    | .error e => pure (.error e)
    | .ok a => interpExcept (k a)
  refine PFunctor.M.bisim
    (fun (u v : ITree E (Except ε β)) =>
      u = v ∨
      ∃ t : ITree (ExceptE.{uε, uB} ε + E :
          PFunctor.{max uε uEA, uB}) α,
        u = interpExcept (bind t k) ∧
        v = bind (interpExcept t) next)
    ?_ _ _ (Or.inr ⟨t, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure r, c⟩ :
              (Poly (ExceptE.{uε, uB} ε + E :
                PFunctor.{max uε uEA, uB}) α).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst ht
        rw [bind_pure_left, interpExcept_pure, bind_pure_left]
        rcases hk : PFunctor.M.dest (interpExcept (k r)) with ⟨sh', c'⟩
        exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
    | step =>
        have ht : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          rfl
        subst ht
        rw [bind_step, interpExcept_step, interpExcept_step, bind_step]
        exact ⟨.step,
          fun _ => interpExcept (bind (c PUnit.unit) k),
          fun _ => bind (interpExcept (c PUnit.unit)) next,
          shape'_step _, shape'_step _,
          fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
    | query event =>
        cases event with
        | inl e =>
            change PEmpty.{uB + 1} → ITree
              (ExceptE.{uε, uB} ε + E :
                PFunctor.{max uε uEA, uB}) α at c
            have ht : t = query
                (Sum.inl e : (ExceptE.{uε, uB} ε + E :
                  PFunctor.{max uε uEA, uB}).A) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [bind_query, interpExcept_throw,
              interpExcept_throw, bind_pure_left]
            rcases hp : PFunctor.M.dest
                (pure (F := E) (Except.error e : Except ε β)) with ⟨sh', c'⟩
            exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
        | inr e =>
            change E.B e → ITree
              (ExceptE.{uε, uB} ε + E :
                PFunctor.{max uε uEA, uB}) α at c
            have ht : t = query
                (Sum.inr e : (ExceptE.{uε, uB} ε + E :
                  PFunctor.{max uε uEA, uB}).A) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [bind_query, interpExcept_query_external,
              interpExcept_query_external, bind_query]
            exact ⟨.query e,
              fun b => interpExcept (bind (c b) k),
              fun b => bind (interpExcept (c b)) next,
              shape'_query _ _, shape'_query _ _,
              fun b => Or.inr ⟨c b, rfl, rfl⟩⟩

@[simp] theorem runExcept_eq_interpExcept
    (t : ITree (ExceptE.{uε, uB} ε + E :
      PFunctor.{max uε uEA, uB}) α) :
    runExcept t = interpExcept t := rfl

end ITree
