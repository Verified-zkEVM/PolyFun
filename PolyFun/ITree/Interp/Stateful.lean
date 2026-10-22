/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Defs
public import PolyFun.Control.Monad.Iter.Instances
public import PolyFun.ITree.Bisim.Bind

/-!
# Exact equations for stateful interaction-tree interpretation

The existing `interp` iterator carries the source residual and private state as
its loop state. Return, silent step and query equations expose this execution
without assuming a lawful equality-based monad structure on interaction trees.
Target operation and answer universes are independent of the caller universe.
-/

public section

namespace ITree

universe u uQA uQB
variable {P : PFunctor.{u, u}} {Q : PFunctor.{uQA, uQB}} {S A : Type u}
  (h : PFunctor.Handler (StateT S (ITree Q)) P)

/-- The interpretation loop returns the value and unchanged service state at a leaf. -/
theorem stateBody_interpStep_pure (a : A) (s : S) :
    StateT.stateBody (interpStep h) (ITree.pure a, s) = ITree.pure (.inr (a, s)) := by
  simp [StateT.stateBody, ITree.map, bind_pure_left, pure_eq_pure]

/-- A silent source step continues with the same private state. -/
theorem stateBody_interpStep_step (tree : ITree P A) (s : S) :
    StateT.stateBody (interpStep h) (ITree.step tree, s) = ITree.pure (.inl (tree, s)) := by
  simp [StateT.stateBody, ITree.map, bind_pure_left, pure_eq_pure]

/-- A query passes its answer and updated state to the next source residual. -/
theorem stateBody_interpStep_query (a : P.A) (next : P.B a → ITree P A) (s : S) :
    StateT.stateBody (interpStep h) (query a next, s) =
      (h a s >>= fun out => ITree.pure (.inl (next out.1, out.2))) := by
  simp [StateT.stateBody, ITree.map, bind_assoc, bind_pure_left]
  rfl

/-- Stateful interpretation is the existing iteration over paired residual and service state. -/
theorem interp_run_eq_iter (tree : ITree P A) (s : S) :
    (interp h tree).run s = iter (StateT.stateBody (interpStep h)) (tree, s) := rfl

/-- A return leaf produces its value and current service state without an extra guard. -/
theorem interp_run_pure (a : A) (s : S) :
    (interp h (ITree.pure a)).run s = ITree.pure (a, s) := by
  rw [interp_run_eq_iter, iter_unfold, stateBody_interpStep_pure, bind_pure_left]

/-- A silent source step becomes one silent step of the stateful execution. -/
theorem interp_run_step (tree : ITree P A) (s : S) :
    (interp h (ITree.step tree)).run s = ITree.step ((interp h tree).run s) := by
  rw [interp_run_eq_iter, iter_unfold, stateBody_interpStep_step, bind_pure_left]
  rfl

/-- The handler runs once, then a silent guard precedes the selected continuation. -/
theorem interp_run_query (a : P.A) (next : P.B a → ITree P A) (s : S) :
    (interp h (query a next)).run s =
      (h a s >>= fun out => step ((interp h (next out.1)).run out.2)) := by
  rw [interp_run_eq_iter, iter_unfold, stateBody_interpStep_query, bind_eq_bind, bind_assoc]
  simp only [bind_pure_left]
  rfl

end ITree
