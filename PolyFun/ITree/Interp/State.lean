/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Defs
public import PolyFun.Control.Monad.Iter.Instances
public import PolyFun.ITree.Events.StateFacts
public import PolyFun.ITree.Bisim.Equiv

/-!
# State events through `interp`

`StateE.handler` answers `get` and `put` in any state monad, and `StateE.stateHandler` answers
state events that way while lifting the remaining events of `StateE σ + E` into
`StateT σ (ITree E)`. Interpreting through it agrees with the direct corecursor
`interpState` up to weak bisimulation and the order of the returned pair
(`interpState_weakBisimRel_interp`): `interpState` returns `σ × α` and takes one silent step
per state operation, while `interp` into `StateT` returns `α × σ` and takes one silent step per
node of the source. The exact computation rules of `interpState` are therefore kept, and this
module supplies the bridge.
-/

@[expose] public section

universe u v

namespace ITree

namespace StateE

variable {σ : Type u} {m : Type u → Type v} [Monad m]

/-- Answer state events in a state monad. -/
def handler : PFunctor.Handler (StateT σ m) (StateE σ)
  | .get => MonadState.get
  | .put s => set s

@[simp] theorem handler_get : handler (m := m) (σ := σ) .get = MonadState.get := rfl

@[simp] theorem handler_put (s : σ) : handler (m := m) (σ := σ) (.put s) = set s := rfl

/-- Answer state events through `handler` and leave the remaining events in place. -/
def stateHandler {E : PFunctor.{u, u}} :
    PFunctor.Handler (StateT σ (ITree E)) (StateE σ + E : PFunctor.{u, u})
  | .inl e => handler e
  | .inr e => StateT.lift (lift e)

@[simp] theorem stateHandler_inl {E : PFunctor.{u, u}} (e : (StateE σ).A) :
    stateHandler (E := E) (.inl e) = handler e := rfl

@[simp] theorem stateHandler_inr {E : PFunctor.{u, u}} (e : E.A) :
    stateHandler (σ := σ) (E := E) (.inr e) = StateT.lift (lift e) := rfl

end StateE

section Bridge

variable {σ : Type u} {E : PFunctor.{u, u}} {α : Type u}

/-- `bind_pure_left` keyed on the monadic `pure`, for rewriting after `StateT` computations. -/
private theorem bind_pure_left' {β : Type u} (r : β) (k : β → ITree E α) :
    bind (Pure.pure r : ITree E β) k = k r :=
  bind_pure_left r k

/-- The paired loop body of `interp StateE.stateHandler` run at a state. -/
private abbrev stateLoop :
    ITree (StateE σ + E : PFunctor.{u, u}) α × σ →
      ITree E ((ITree (StateE σ + E : PFunctor.{u, u}) α × σ) ⊕ (α × σ)) :=
  StateT.stateBody (interpStep (StateE.stateHandler (σ := σ) (E := E)))

private theorem stateLoop_pure (r : α) (s : σ) :
    stateLoop (E := E) (pure r, s) = pure (.inr (r, s)) := by
  simp [stateLoop, StateT.stateBody, ITree.map, bind_pure_left']

private theorem stateLoop_step (t : ITree (StateE σ + E : PFunctor.{u, u}) α) (s : σ) :
    stateLoop (E := E) (step t, s) = pure (.inl (t, s)) := by
  simp [stateLoop, StateT.stateBody, ITree.map, bind_pure_left']

private theorem stateLoop_get (k : σ → ITree (StateE σ + E : PFunctor.{u, u}) α) (s : σ) :
    stateLoop (E := E) (query (.inl .get) k, s) = pure (.inl (k s, s)) := by
  simp [stateLoop, StateT.stateBody, ITree.map, StateE.stateHandler, StateE.handler,
    bind_pure_left, bind_pure_left']

private theorem stateLoop_put (k : PUnit → ITree (StateE σ + E : PFunctor.{u, u}) α)
    (s s' : σ) :
    stateLoop (E := E) (query (.inl (.put s')) k, s) = pure (.inl (k PUnit.unit, s')) := by
  have hset : (set s' : StateT σ (ITree E) PUnit).run s = Pure.pure (PUnit.unit, s') := rfl
  simp [stateLoop, StateT.stateBody, ITree.map, StateE.stateHandler, StateE.handler, hset,
    bind_pure_left, bind_pure_left']

private theorem stateLoop_external (e : E.A) (k : E.B e → ITree (StateE σ + E : PFunctor.{u, u}) α)
    (s : σ) :
    stateLoop (E := E) (query (.inr e) k, s) = query e (fun b => pure (.inl (k b, s))) := by
  simp [stateLoop, StateT.stateBody, ITree.map, StateE.stateHandler, lift, bind_query,
    bind_pure_left]

/-- Interpreting through the state handler agrees with `interpState` up to weak bisimulation
and the order of the returned pair. -/
theorem interpState_weakBisimRel_interp (t : ITree (StateE σ + E : PFunctor.{u, u}) α) (s : σ) :
    WeakBisimRel (fun (p : σ × α) (q : α × σ) => p.1 = q.2 ∧ p.2 = q.1) (interpState t s)
      ((interp (StateE.stateHandler (σ := σ) (E := E)) t).run s) := by
  rw [interp, StateT.run_iterM_eq_stateBody]
  change WeakBisimRel _ (interpState t s) (iter stateLoop (t, s))
  refine WeakBisimRel.coinduct _ (fun x y =>
      (∃ t s, x = interpState t s ∧ y = iter stateLoop (t, s)) ∨
      (∃ t s, x = interpState t s ∧ y = step (iter stateLoop (t, s))))
    ?_ (Or.inl ⟨t, s, rfl, rfl⟩)
  rintro x y hxy
  obtain ⟨t, s, rfl, hy⟩ : ∃ t s, x = interpState t s ∧ TauSteps y (iter stateLoop (t, s)) := by
    rcases hxy with ⟨t, s, rfl, rfl⟩ | ⟨t, s, rfl, rfl⟩
    · exact ⟨t, s, rfl, TauSteps.refl _⟩
    · exact ⟨t, s, rfl, TauSteps.step _ (shape'_step _) (TauSteps.refl _)⟩
  rcases ht : shape' t with ⟨sh, c⟩
  cases sh with
  | pure r =>
    obtain rfl := eq_pure_of_dest ht
    rw [iter_unfold, stateLoop_pure, bind_pure_left] at hy
    rw [interpState_pure]
    exact ⟨pure (s, r), pure (r, s), TauSteps.refl _, hy,
      MatchRel.pure (s, r) (r, s) ⟨rfl, rfl⟩ (shape'_pure _) (shape'_pure _)⟩
  | step =>
    obtain rfl := eq_step_of_dest ht
    rw [iter_unfold, stateLoop_step, bind_pure_left] at hy
    rw [interpState_step]
    exact ⟨step (interpState (c PUnit.unit) s), step (iter stateLoop (c PUnit.unit, s)),
      TauSteps.refl _, hy, MatchRel.tau _ _ (shape'_step _) (shape'_step _)
        (Or.inl ⟨c PUnit.unit, s, rfl, rfl⟩)⟩
  | query a =>
    obtain rfl := eq_query_of_dest ht
    rcases a with e | e
    · cases e with
      | get =>
        rw [iter_unfold, stateLoop_get, bind_pure_left] at hy
        rw [interpState_get]
        exact ⟨step (interpState (c s) s), step (iter stateLoop (c s, s)),
          TauSteps.refl _, hy, MatchRel.tau _ _ (shape'_step _) (shape'_step _)
            (Or.inl ⟨c s, s, rfl, rfl⟩)⟩
      | put s' =>
        rw [iter_unfold, stateLoop_put, bind_pure_left] at hy
        rw [interpState_put]
        exact ⟨step (interpState (c PUnit.unit) s'), step (iter stateLoop (c PUnit.unit, s')),
          TauSteps.refl _, hy, MatchRel.tau _ _ (shape'_step _) (shape'_step _)
            (Or.inl ⟨c PUnit.unit, s', rfl, rfl⟩)⟩
    · rw [iter_unfold, stateLoop_external, bind_query] at hy
      simp only [bind_pure_left] at hy
      rw [interpState_query_external]
      exact ⟨query e (fun b => interpState (c b) s),
        query e (fun b => step (iter stateLoop (c b, s))), TauSteps.refl _, hy,
        MatchRel.query e _ _ (shape'_query _ _) (shape'_query _ _)
          (fun b => Or.inr ⟨c b, s, rfl, rfl⟩)⟩

/-- `interpState` is interpretation through the state handler with the returned pair swapped,
up to weak bisimulation. -/
theorem interpState_weakBisim_interp (t : ITree (StateE σ + E : PFunctor.{u, u}) α) (s : σ) :
    WeakBisim (interpState t s)
      (ITree.map Prod.swap ((interp (StateE.stateHandler (σ := σ) (E := E)) t).run s)) := by
  have h := interpState_weakBisimRel_interp t s
  have h' := map_weakBisimRel (SS := Eq) (f := id) (g := Prod.swap) h fun p q hpq => by
    rcases p with ⟨s', a⟩; rcases q with ⟨a', s''⟩
    rcases hpq with ⟨h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    rfl
  simpa [ITree.map, bind_pure_right] using h'

end Bridge

end ITree
