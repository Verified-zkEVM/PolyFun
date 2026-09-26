/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Iter.Instances
public import PolyFun.ITree.Bisim.Iter

/-!
# Iteration through monad transformers

Canaries for the transformer `MonadIter` instances: a state loop over an interaction tree
unfolds to the paired base loop, the lawful instances are found by instance search over an
iterative base, the option and exception loops turn early exits into loop results, and the
constructions live at independent universes.
-/

@[expose] public section

universe u

namespace PolyFunTest.IterInstances

open ITree

/-- A signature with one silent-answer request. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- Count down in the state, ticking once per step, and return the number of ticks. -/
def countdown : Nat → StateT Nat (ITree Tick) (Nat ⊕ Nat) := fun ticks => do
  let n ← get
  if n = 0 then
    pure (.inr ticks)
  else
    set (n - 1)
    let _ ← (lift () : ITree Tick Unit)
    pure (.inl (ticks + 1))

/-- The state loop is the base loop on the paired body, definitionally. -/
example (s : Nat) :
    (iterM countdown 0).run s =
      iterM (fun p : Nat × Nat =>
        (fun q => Sum.map (·, q.2) (·, q.2) q.1) <$> (countdown p.1).run p.2) (0, s) :=
  rfl

/-- The lawful instances are available over any lawful iterative base. -/
example : LawfulMonadIter (StateT Nat (ITree Tick)) := inferInstance

example : LawfulMonadIter (ReaderT Bool (ITree Tick)) := inferInstance

example : MonadIter (OptionT (ITree Tick)) := inferInstance

example : MonadIter (ExceptT String (ITree Tick)) := inferInstance

/-- Uniformity at the state transformer: relabelling the loop state through `φ` is invisible
when the two bodies agree up to `φ` at every state. -/
example (φ : Nat → Nat) (f : Nat → StateT Nat (ITree Tick) (Nat ⊕ Bool))
    (g : Nat → StateT Nat (ITree Tick) (Nat ⊕ Bool))
    (h : ∀ b s, WeakBisim ((g (φ b)).run s) ((Sum.map φ id <$> f b).run s)) (init : Nat)
    (s : Nat) :
    WeakBisim ((iterM f init).run s) ((iterM g (φ init)).run s) :=
  LawfulMonadIter.iter_uniform φ f g (fun b s => h b s) init s

/-- The option and exception loops run in the base monad through their public `run` equations,
whose right-hand sides are base loops that the base iteration laws apply to. -/
example (f : Unit → OptionT (ITree Tick) (Unit ⊕ Nat)) := OptionT.run_iterM f ()

example (f : Unit → ExceptT String (ITree Tick) (Unit ⊕ Nat)) := ExceptT.run_iterM f ()

/-- The constructions elaborate at a higher universe. -/
example {σ : Type 1} {F : PFunctor.{1, 1}} : MonadIter (StateT σ (ITree F)) := inferInstance

example {σ : Type 1} {F : PFunctor.{1, 1}} : LawfulMonadIter (StateT σ (ITree F)) :=
  inferInstance

end PolyFunTest.IterInstances
