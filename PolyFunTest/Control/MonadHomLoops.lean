/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Hom.Loops
public import PolyFun.Control.Monad.Hom.Writer

/-!
# Monad morphisms through loops

`simp` pushes a bundled morphism into the body of every loop combinator, and `grind` closes
goals that need the list forms as rewrite rules.
-/

public section

universe v w

variable {m : Type → Type v} {n : Type → Type w} [Monad m] [Monad n]

example (F : m →ᵐ n) (l : List Nat) (init : Nat) (f : Nat → Nat → m (ForInStep Nat)) :
    F (forIn l init f) = forIn l init fun a b => F (f a b) := by
  simp

/-- Stated with the class method `forM`, the simp normal form of `List.forM`. -/
example (F : m →ᵐ n) (l : List Nat) (f : Nat → m PUnit) :
    F (forM l f) = forM l fun a => F (f a) := by
  grind

example (F : m →ᵐ n) (l : List Nat) (init : Nat) (f : Nat → Nat → m Nat) :
    F (l.foldlM f init) = l.foldlM (fun s a => F (f s a)) init := by
  simp

example [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (l : List Nat) (f : Nat → m Nat) :
    F (l.mapM f) = l.mapM fun a => F (f a) := by
  simp

/-- Arrays iterate over their list, so the container lemma applies through `PureForIn`. -/
example (F : m →ᵐ n) (xs : Array Nat) (init : Nat) (f : Nat → Nat → m (ForInStep Nat)) :
    F (forIn xs init f) = forIn xs init fun a b => F (f a b) := by
  simp
