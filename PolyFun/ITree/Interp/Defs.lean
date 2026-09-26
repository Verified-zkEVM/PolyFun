/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Sim.Defs
public import PolyFun.PFunctor.Handler
public import PolyFun.Control.Monad.Iter

/-!
# Interpreting interaction trees into iterative monads

`ITree.interp h t` runs the tree `t` in a monad `m`, answering each event through the handler
`h : PFunctor.Handler m E`. The definition is Coq's `interp` (`Interp/Interp.v`): iterate one node
at a time with `MonadIter.iterM`, returning at a leaf, continuing past a silent step, and asking
the handler at a query. Interpreting into another interaction tree is `ITree.simulate`, by
definition (`interp_eq_simulate`); the point of the general form is that `StateT σ (ITree F)`,
`OptionT (ITree F)`, or any other iterative monad is a target as well.

The universe of the loop state forces one universe: `E : PFunctor.{u, u}`, `α : Type u`, and
`m : Type u → Type v`. `simulate` keeps its independent universes and remains the interpreter to
use when the target is an interaction tree at a different universe.

`liftHandler` is the handler that runs each event as the corresponding lifted tree; it is the
identity interpretation up to a monad lift, used to leave some events uninterpreted.
-/

@[expose] public section

universe u v uFA uFB

namespace ITree

variable {E : PFunctor.{u, u}} {m : Type u → Type v} [Monad m] {α : Type u}

/-- One loop step of `interp`: return at a leaf, continue past a silent step, and answer a query
through the handler, continuing with the chosen branch. -/
def interpStep (h : PFunctor.Handler m E) (t : ITree E α) : m (ITree E α ⊕ α) :=
  match shape' t with
  | .mk (.pure r) _ => Pure.pure (.inr r)
  | .mk .step c => Pure.pure (.inl (c PUnit.unit))
  | .mk (.query a) c => (fun b => .inl (c b)) <$> h a

@[simp] theorem interpStep_pure (h : PFunctor.Handler m E) (r : α) :
    interpStep h (pure r) = Pure.pure (.inr r) := by
  simp [interpStep]

@[simp] theorem interpStep_step (h : PFunctor.Handler m E) (t : ITree E α) :
    interpStep h (step t) = Pure.pure (.inl t) := by
  simp [interpStep]

@[simp] theorem interpStep_query (h : PFunctor.Handler m E) (a : E.A) (k : E.B a → ITree E α) :
    interpStep h (query a k) = (fun b => .inl (k b)) <$> h a := by
  simp [interpStep]

section Interp

variable [MonadIter m]

/-- Interpret an interaction tree in an iterative monad, answering events through `h`. -/
def interp (h : PFunctor.Handler m E) (t : ITree E α) : m α :=
  iterM (interpStep h) t

theorem interp_eq_iterM (h : PFunctor.Handler m E) (t : ITree E α) :
    interp h t = iterM (interpStep h) t :=
  rfl

end Interp

/-- The handler that answers each event by the corresponding lifted tree. Interpreting through
it leaves every event in place, up to the monad lift. -/
def liftHandler {n : Type u → Type v} [MonadLiftT (ITree E) n] : PFunctor.Handler n E :=
  fun a => monadLift (lift a)

@[simp] theorem liftHandler_apply {n : Type u → Type v} [MonadLiftT (ITree E) n] (a : E.A) :
    (liftHandler (n := n) : PFunctor.Handler n E) a = monadLift (lift a) :=
  rfl

/-- Interpreting into an interaction tree is simulation, by definition. -/
theorem interp_eq_simulate {F : PFunctor.{uFA, uFB}} (h : PFunctor.Handler (ITree F) E)
    (t : ITree E α) :
    interp h t = simulate h t :=
  rfl

end ITree
