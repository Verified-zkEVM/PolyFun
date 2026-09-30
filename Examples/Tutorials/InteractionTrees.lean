/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.State

/-!
# Interaction trees: a counter with state and ticks

A program over state events and an external `tick` event is written once as an interaction
tree and run three ways: with the direct state corecursor, through the state handler into a
state transformer over trees, and through two handlers into an option transformer over trees,
one acknowledging ticks and one refusing them. The tutorial page
`docs/tutorials/interaction-trees.md` walks through this module.
-/

@[expose] public section

namespace PolyFunExamples.InteractionTrees

-- BEGIN PROGRAM
open ITree

/-- One external event, a tick, acknowledged with no payload. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- The program's signature: state events on a natural number, plus ticks. -/
abbrev Sig : PFunctor.{0, 0} := StateE Nat + Tick

/-- Read the counter, tick once, store the incremented value, and return the value read. -/
def bump : ITree Sig Nat := do
  let n : Nat ← lift (F := Sig) (.inl .get)
  let _ ← lift (F := Sig) (.inr ())
  let _ ← lift (F := Sig) (.inl (.put (n + 1)))
  ITree.pure n
-- END PROGRAM

/-- As a tree, `bump` is its three events in sequence. -/
theorem bump_eq : bump = query (F := Sig) (.inl .get) fun (n : Nat) => query (.inr ()) fun _ =>
    query (.inl (.put (n + 1))) fun _ => ITree.pure n := by
  simp only [bump, lift, bind_eq_bind, bind_query, bind_pure_left]
  rfl

/-- The direct state corecursor: each state operation becomes one silent step, the tick stays
visible, and the final state is returned first. -/
theorem runState_bump (s : Nat) :
    runState bump s = step (query () fun _ => step (ITree.pure (s + 1, s))) := by
  rw [runState, bump_eq, interpState_get, interpState_query_external]
  congr 2
  funext _
  rw [interpState_put, interpState_pure]

/-- Through the state handler, the same program runs in `StateT Nat (ITree Tick)`. The result
agrees with the corecursor up to weak bisimulation and the order of the returned pair. -/
example (s : Nat) :
    WeakBisim (interpState bump s)
      (ITree.map Prod.swap ((interp StateE.stateHandler bump).run s)) :=
  interpState_weakBisim_interp bump s

/-- Ticks are acknowledged; state events are left in place, lifted into the option layer. -/
def acknowledge : PFunctor.Handler (OptionT (ITree (StateE Nat))) Sig
  | .inl e => liftHandler e
  | .inr () => Pure.pure ()

/-- Ticks are refused with `failure`; state events are left in place, as by `acknowledge`. -/
def refuse : PFunctor.Handler (OptionT (ITree (StateE Nat))) Sig
  | .inl e => liftHandler e
  | .inr () => failure

/-- The two handlers agree on state events. -/
example (e : (StateE Nat).A) : acknowledge (.inl e) = refuse (.inl e) := rfl

/-- On the tick, `acknowledge` answers and `refuse` fails. -/
example : acknowledge (.inr ()) = Pure.pure () ∧ refuse (.inr ()) = failure :=
  ⟨rfl, rfl⟩

/-- Acknowledging ticks, the run reads the counter, writes the incremented value, and returns
the value read. The loop of `interp` takes a silent step each time it moves to the next node. -/
theorem run_interp_acknowledge_bump :
    (interp acknowledge bump).run =
      query (F := StateE Nat) .get fun (n : Nat) => step (step (query (.put (n + 1)) fun _ =>
        step (ITree.pure (some n)))) := by
  rw [interp, OptionT.run_iterM, iterM_eq_iter, bump_eq]
  simp [iter_unfold _ (query _ _), iter_unfold _ (ITree.pure _), OptionT.optionBody, acknowledge,
    ITree.map, lift, pure_eq_pure, bind_query, bind_pure_left]

/-- Refusing ticks, the run reads the counter and ends with `none` at the tick: the write never
happens. -/
theorem run_interp_refuse_bump :
    (interp refuse bump).run = query (F := StateE Nat) .get fun _ => step (ITree.pure none) := by
  rw [interp, OptionT.run_iterM, iterM_eq_iter, bump_eq]
  simp [iter_unfold _ (query _ _), OptionT.optionBody, refuse, ITree.map, lift, pure_eq_pure,
    bind_query, bind_pure_left]

end PolyFunExamples.InteractionTrees
