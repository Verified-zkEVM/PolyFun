/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Machine
import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-!
# Ordinary-import canaries for interaction trees as machines

`ITree.withSilentSteps` adapts a visible-event handler to the `F + y` interface of
`ITree.toDynComputation`. These examples check, through ordinary imports, that its body is the
public sum with a unit acknowledgement, that its routing laws rewrite the summands as they are
elaborated against `F + y`, and that positions, responses and the target monad keep independent
universes.
-/

universe uA uB uM

namespace PolyFunTest.ModuleAPI.ITreeMachine

open _root_.PFunctor

variable {F : PFunctor.{uA, uB}} {m : Type uB → Type uM} [Monad m] (handler : Handler m F)

/-- The body is part of the public contract: a sum with a unit acknowledgement. -/
example : ITree.withSilentSteps handler = Handler.sum handler fun _ => pure PUnit.unit := rfl

example (operation : F.A) :
    ITree.withSilentSteps handler (.inl operation) = handler operation := by
  rw [ITree.withSilentSteps_visible]

example : ITree.withSilentSteps handler (.inr PUnit.unit) = pure PUnit.unit := by
  rw [ITree.withSilentSteps_silent]

/-! The routing laws also fire under plain `simp` and under `simp only`, including inside a bind. -/

example (operation : F.A) :
    ITree.withSilentSteps handler (.inl operation) = handler operation := by
  simp

example : ITree.withSilentSteps handler (.inr PUnit.unit) = pure PUnit.unit := by
  simp

example (operation : F.A) :
    ITree.withSilentSteps handler (.inl operation) = handler operation := by
  simp only [ITree.withSilentSteps_visible]

example : ITree.withSilentSteps handler (.inr PUnit.unit) = pure PUnit.unit := by
  simp only [ITree.withSilentSteps_silent]

example {β : Type uB} (k : PUnit.{uB + 1} → m β) :
    (ITree.withSilentSteps handler (.inr PUnit.unit) >>= k) = (pure PUnit.unit >>= k) := by
  simp only [ITree.withSilentSteps_silent]

/-- A silent step never reaches the visible handler, whatever that handler does. -/
example (other : Handler m F) (step : PFunctor.y.{uA, uB}.A) :
    ITree.withSilentSteps handler (.inr step) = ITree.withSilentSteps other (.inr step) := rfl

/-- The adapted handler interprets the tree-as-machine interface. -/
example {α : Type uB} (t : ITree F α) (fuel : Nat) :
    m (Option α) := ((ITree.toDynComputation (F := F)).run fuel t).liftM
      (ITree.withSilentSteps handler)

end PolyFunTest.ModuleAPI.ITreeMachine
