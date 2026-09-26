/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Laws
public import PolyFun.ITree.Interp.Sim
public import PolyFun.ITree.Interp.State
public import PolyFun.Control.Monad.Iter.Instances

/-!
# Interpreting interaction trees into monads

Canaries for `ITree.interp`: interpreting into a tree is simulation by definition, the generic
laws instantiate at a state transformer over a tree, the state handler agrees with the direct
state corecursor up to weak bisimulation and pair order, and a handler into an option
transformer turns an event into a failure.
-/

@[expose] public section

universe u

namespace PolyFunTest.Interp

open ITree

/-- A signature with one acknowledged request. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- Read the count, tick once, and increment. -/
def counter : ITree (StateE Nat + Tick : PFunctor.{0, 0}) Nat := do
  let n ← (ITree.query (F := StateE Nat + Tick) (.inl .get) ITree.pure :
    ITree (StateE Nat + Tick : PFunctor.{0, 0}) Nat)
  let _ ← ITree.query (F := StateE Nat + Tick) (.inr ()) ITree.pure
  let _ ← ITree.query (F := StateE Nat + Tick) (.inl (.put (n + 1))) ITree.pure
  ITree.pure n

/-- Interpreting into a tree is simulation, definitionally. -/
example {E F : PFunctor.{0, 0}} (h : PFunctor.Handler (ITree F) E) (t : ITree E Nat) :
    interp h t = simulate h t :=
  interp_eq_simulate h t

/-- The generic laws instantiate at a state transformer over a tree, up to its equivalence. -/
example (h : PFunctor.Handler (StateT Nat (ITree Tick)) Tick) (t : ITree Tick Nat)
    (k : Nat → ITree Tick Bool) :
    LawfulMonadIter.Eqv (interp h (t >>= k)) (interp h t >>= fun a => interp h (k a)) :=
  interp_bind h k t

example (h : PFunctor.Handler (StateT Nat (ITree Tick)) Tick) (a : Tick.A) :
    LawfulMonadIter.Eqv (interp h (lift a)) (h a) :=
  interp_lift h a

/-- The state handler agrees with the direct state corecursor up to weak bisimulation and the
order of the returned pair. -/
example (s : Nat) :
    WeakBisimRel (fun (p : Nat × Nat) (q : Nat × Nat) => p.1 = q.2 ∧ p.2 = q.1)
      (interpState counter s) ((interp StateE.stateHandler counter).run s) :=
  interpState_weakBisimRel_interp counter s

example (t : ITree (StateE Nat + Tick : PFunctor.{0, 0}) Nat) (s : Nat) :
    WeakBisim (interpState t s)
      (ITree.map Prod.swap ((interp StateE.stateHandler t).run s)) :=
  interpState_weakBisim_interp t s

/-- Answering the tick by failure: interpreting into an option transformer over a tree. The
option transformer is iterative, so `interp` targets it; its loop step asks the handler. -/
def failingTick : PFunctor.Handler (OptionT (ITree Tick)) Tick := fun _ => failure

example : OptionT (ITree Tick) Unit := interp failingTick (lift ())

example : interpStep failingTick (lift ()) = (fun b => .inl (ITree.pure b)) <$> failingTick () :=
  interpStep_query failingTick () ITree.pure

/-- The construction elaborates at a higher universe. -/
example {E : PFunctor.{1, 1}} {σ : Type 1} (h : PFunctor.Handler (StateT σ (ITree E)) E)
    (t : ITree E σ) : StateT σ (ITree E) σ :=
  interp h t

end PolyFunTest.Interp
