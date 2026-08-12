/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Events.State
public import PolyFun.ITree.Bisim.Bind

/-! # Laws for state interpretation

Exact computation rules for `ITree.interpState` and `ITree.runState`.
State operations take one silent step, ordinary ITree steps are preserved,
and external events remain visible.
-/

@[expose] public section

attribute [local implicit_reducible] PFunctor.Obj

universe uσ uEA uα uβ

namespace ITree

variable {σ : Type uσ} {E : PFunctor.{uEA, uσ}} {α : Type uα}

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the proofs below need `(StateE σ + E).B` at `.inl`/`.inr` events to unfold
there, which goes through the sum functor's `Sum.elim` child family.
`implicit_reducible` restores that without touching simp or typeclass
resolution. -/
attribute [local implicit_reducible] Sum.elim

@[simp] theorem interpState_pure (s : σ) (r : α) :
    interpState (E := E)
      (pure (F := (StateE σ + E : PFunctor.{max uσ uEA, uσ})) r) s =
      pure (s, r) := by
  have hstep : interpStateStep
      (s, pure (F := (StateE σ + E : PFunctor.{max uσ uEA, uσ})) r) =
      ⟨.pure (s, r), PEmpty.elim⟩ := by
    simp [interpStateStep]
  apply eq_of_shape'_eq
  rw [interpState, shape'_corec_eq _ _ hstep]
  unfold ITree.pure
  rw [ITree.shape'_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem interpState_step (s : σ)
    (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :
    interpState (step t) s = step (interpState t s) := by
  have hstep : interpStateStep (s, step t) =
      ⟨.step, fun _ => (s, t)⟩ := by
    simp [interpStateStep]
  apply eq_of_shape'_eq
  rw [interpState, shape'_corec_eq _ _ hstep]
  unfold ITree.step
  rw [ITree.shape'_mk]
  rfl

@[simp] theorem interpState_get (s : σ)
    (k : σ → ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :
    interpState (query
      (Sum.inl (α := StateE.Shape σ) (β := E.A) StateE.Shape.get) k) s =
      step (interpState (k s) s) := by
  have hstep : interpStateStep (s, query
      (Sum.inl StateE.Shape.get :
        (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) k) =
      ⟨.step, fun _ => (s, k s)⟩ := by
    simp [interpStateStep]
  apply eq_of_shape'_eq
  rw [interpState, shape'_corec_eq _ _ hstep]
  unfold ITree.step
  rw [ITree.shape'_mk]
  rfl

@[simp] theorem interpState_put (s s' : σ)
    (k : PUnit.{uσ + 1} →
      ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :
    interpState (query
      (Sum.inl (α := StateE.Shape σ) (β := E.A) (StateE.Shape.put s')) k) s =
      step (interpState (k PUnit.unit) s') := by
  have hstep : interpStateStep
      (s, query
        (Sum.inl (StateE.Shape.put s') :
          (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) k) =
      ⟨.step, fun _ => (s', k PUnit.unit)⟩ := by
    simp [interpStateStep]
  apply eq_of_shape'_eq
  rw [interpState, shape'_corec_eq _ _ hstep]
  unfold ITree.step
  rw [ITree.shape'_mk]
  rfl

@[simp] theorem interpState_query_external (s : σ) (e : E.A)
    (k : E.B e →
      ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :
    interpState (query
      (Sum.inr (α := StateE.Shape σ) (β := E.A) e) k) s =
      query e (fun b => interpState (k b) s) := by
  have hstep : interpStateStep (s, query
      (Sum.inr e : (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) k) =
      ⟨.query e, fun b => (s, k b)⟩ := by
    simp [interpStateStep]
  apply eq_of_shape'_eq
  rw [interpState, shape'_corec_eq _ _ hstep]
  unfold ITree.query
  rw [ITree.shape'_mk]
  rfl

/-- State interpretation is the canonical state-transformer monad morphism. -/
theorem interpState_bind {β : Type uβ}
    (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α)
    (k : α → ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) β)
    (s : σ) :
    interpState (bind t k) s =
      bind (interpState t s) (fun p => interpState (k p.2) p.1) := by
  let next : σ × α → ITree E (σ × β) :=
    fun p => interpState (k p.2) p.1
  refine ITree.bisim
    (fun (u v : ITree E (σ × β)) =>
      u = v ∨
      ∃ (s : σ)
        (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α),
        u = interpState (bind t k) s ∧
        v = bind (interpState t s) next)
    ?_ _ _ (Or.inr ⟨s, t, rfl, rfl⟩)
  rintro u v (rfl | ⟨s, t, rfl, rfl⟩)
  · rcases h : ITree.shape' u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : ITree.shape' t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := eq_pure_of_dest h
        subst ht
        rw [bind_pure_left, interpState_pure, bind_pure_left]
        rcases hk : ITree.shape' (interpState (k r) s) with ⟨sh', c'⟩
        exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
    | step =>
        have ht : t = step (c PUnit.unit) := by
          apply eq_of_shape'_eq
          rw [h]
          rfl
        subst ht
        rw [bind_step, interpState_step, interpState_step, bind_step]
        exact ⟨.step,
          fun _ => interpState (bind (c PUnit.unit) k) s,
          fun _ => bind (interpState (c PUnit.unit) s) next,
          shape'_step _, shape'_step _,
          fun _ => Or.inr ⟨s, c PUnit.unit, rfl, rfl⟩⟩
    | query event =>
        cases event with
        | inl stateEvent =>
            cases stateEvent with
            | get =>
                change σ → ITree
                  (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α at c
                have ht : t = query
                    (Sum.inl StateE.Shape.get :
                      (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) c := by
                  apply eq_of_shape'_eq
                  rw [h]
                  rfl
                subst ht
                clear h
                let getEvent :
                    (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A :=
                  Sum.inl StateE.Shape.get
                have hLeft : ITree.shape'
                    (interpState (bind (query getEvent c) k) s) =
                    ⟨.step, fun _ => interpState (bind (c s) k) s⟩ := by
                  rw [interpState, shape'_corec_apply]
                  simp only [interpStateStep]
                  rfl
                have hState : ITree.shape'
                    (interpState (query getEvent c) s) =
                    ⟨.step, fun _ => interpState (c s) s⟩ := by
                  rw [interpState, shape'_corec_apply]
                  simp only [interpStateStep]
                  rfl
                have hRight : ITree.shape'
                    (bind (interpState (query getEvent c) s) next) =
                    ⟨.step, fun _ => bind (interpState (c s) s) next⟩ :=
                  dest_bind_step next _ _ hState
                exact ⟨.step,
                  fun _ => interpState (bind (c s) k) s,
                  fun _ => bind (interpState (c s) s) next,
                  hLeft, hRight,
                  fun _ => Or.inr ⟨s, c s, rfl, rfl⟩⟩
            | put s' =>
                change PUnit.{uσ + 1} → ITree
                  (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α at c
                have ht : t = query
                    (Sum.inl (StateE.Shape.put s') :
                      (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) c := by
                  apply eq_of_shape'_eq
                  rw [h]
                  rfl
                subst ht
                clear h
                let putEvent :
                    (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A :=
                  Sum.inl (StateE.Shape.put s')
                have hLeft : ITree.shape'
                    (interpState (bind (query putEvent c) k) s) =
                    ⟨.step, fun _ =>
                      interpState (bind (c PUnit.unit) k) s'⟩ := by
                  rw [interpState, shape'_corec_apply]
                  simp only [interpStateStep]
                  rfl
                have hState : ITree.shape'
                    (interpState (query putEvent c) s) =
                    ⟨.step, fun _ => interpState (c PUnit.unit) s'⟩ := by
                  rw [interpState, shape'_corec_apply]
                  simp only [interpStateStep]
                  rfl
                have hRight : ITree.shape'
                    (bind (interpState (query putEvent c) s) next) =
                    ⟨.step, fun _ =>
                      bind (interpState (c PUnit.unit) s') next⟩ :=
                  dest_bind_step next _ _ hState
                exact ⟨.step,
                  fun _ => interpState (bind (c PUnit.unit) k) s',
                  fun _ => bind (interpState (c PUnit.unit) s') next,
                  hLeft, hRight,
                  fun _ => Or.inr ⟨s', c PUnit.unit, rfl, rfl⟩⟩
        | inr e =>
            change E.B e → ITree
              (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α at c
            have ht : t = query
                (Sum.inr e :
                  (StateE σ + E : PFunctor.{max uσ uEA, uσ}).A) c := by
              apply eq_of_shape'_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [bind_query, interpState_query_external,
              interpState_query_external, bind_query]
            exact ⟨.query e,
              fun b => interpState (bind (c b) k) s,
              fun b => bind (interpState (c b) s) next,
              shape'_query _ _, shape'_query _ _,
              fun b => Or.inr ⟨s, c b, rfl, rfl⟩⟩

@[simp] theorem runState_eq_interpState
    (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α)
    (s : σ) :
    runState t s = interpState t s := rfl

end ITree
