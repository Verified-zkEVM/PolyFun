/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.State
public import PolyFun.ITree.Interp.Laws

/-!
# Interaction trees: a counter with state and ticks

A program over state events and an external `tick` event is written once as an interaction
tree and run three ways: with the direct state corecursor, through the state handler into a
state transformer over trees, and through a handler that refuses ticks. The tutorial page
`docs/tutorials/interaction-trees.md` walks through this module.
-/

@[expose] public section

namespace PolyFunExamples.InteractionTrees

open ITree

-- BEGIN PROGRAM
/-- One external event, a tick, acknowledged with no payload. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- The program's signature: state events on a natural number, plus ticks. -/
abbrev Sig : PFunctor.{0, 0} := StateE Nat + Tick

/-- Read the counter, tick once, store the incremented value, and return the value read. -/
def bump : ITree Sig Nat := do
  let n ← (query (F := Sig) (.inl .get) ITree.pure : ITree Sig Nat)
  let _ ← query (F := Sig) (.inr ()) ITree.pure
  let _ ← query (F := Sig) (.inl (.put (n + 1))) ITree.pure
  ITree.pure n
-- END PROGRAM

/-- The direct state corecursor: each state operation becomes one silent step, the tick stays
visible, and the final state is returned first. -/
theorem runState_bump (s : Nat) :
    runState bump s = step (query () fun _ => step (ITree.pure (s + 1, s))) := by
  simp only [bump, runState, bind_eq_bind, bind_query, bind_pure_left]
  rw [interpState_get, interpState_query_external]
  congr 2
  funext _
  rw [interpState_put, interpState_pure]

/-- Through the state handler, the same program runs in `StateT Nat (ITree Tick)`. The result
agrees with the corecursor up to weak bisimulation and the order of the returned pair. -/
example (s : Nat) :
    WeakBisim (interpState bump s)
      (ITree.map Prod.swap ((interp StateE.stateHandler bump).run s)) :=
  interpState_weakBisim_interp bump s

/-- Ticks are answered by acknowledging them; state events are lifted into the option layer. -/
def acknowledge : PFunctor.Handler (OptionT (ITree (StateE Nat))) Sig
  | .inl e => OptionT.lift (lift e)
  | .inr () => Pure.pure ()

/-- Ticks are refused: the interpretation fails at the first tick. -/
def refuse : PFunctor.Handler (OptionT (ITree (StateE Nat))) Sig
  | .inl e => OptionT.lift (lift e)
  | .inr () => failure

/-- Both handlers agree on state events; they differ exactly on the tick. -/
example (e : (StateE Nat).A) : acknowledge (.inl e) = refuse (.inl e) := rfl

example : refuse (.inr ()) = failure := rfl

/-- Interpreting a single tick through the refusing handler is the failure itself, up to the
option transformer's run. -/
example : (interpStep refuse (lift (F := Sig) (.inr ()))) =
    (fun b => .inl (ITree.pure b)) <$> refuse (.inr ()) :=
  interpStep_query refuse (.inr ()) ITree.pure

end PolyFunExamples.InteractionTrees
