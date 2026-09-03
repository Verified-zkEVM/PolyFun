/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.Structural
public import PolyFun.Control.Monad.Support.Instances

/-!
# One-tactic gates for the structural support laws

Each example is closed by a single call to the automation the corresponding lemma is tagged
for: `simp` for the judgment-level rules and the `CanReturn` rules on `ite` / `dite` / `<*` /
`*>`, `grind` for the `CanReturn` rules on `Option.elim` / `Sum.elim`, which it can index.
-/

public section

open MonadAttach

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- `if` pushes through every judgment. -/
example (c : Prop) [Decidable c] (x y : Option Nat) (p : Nat → Prop) (hx : AllOutputs p x)
    (hy : AllOutputs p y) : AllOutputs p (if c then x else y) := by
  simp [hx, hy]

/-- `if h :` too. -/
example (c : Prop) [Decidable c] (x : c → Option Nat) (y : ¬ c → Option Nat) (p : Nat → Prop)
    (hx : ∀ h, SomeOutput p (x h)) (hy : ∀ h, SomeOutput p (y h)) :
    SomeOutput p (if h : c then x h else y h) := by
  simp [hx, hy]

/-- Reachability through `<*` is the conjunction of both sides. -/
example (x : Option Nat) (y : Option Bool) (a : Nat) (h : CanReturn (x <* y) a) :
    CanReturn x a := by
  simp only [canReturn_seqLeft_iff] at h
  exact h.1

/-- `*>` forgets its first operand's value but not its reachability. -/
example (x : Option Nat) (y : Option Bool) (p : Bool → Prop) (hy : AllOutputs p y) :
    AllOutputs p (x *> y) := by
  simp [hy]

/-- Mapping is transparent to the "always" judgment (stated over a generic monad: on `Option`,
`simp` first turns `<$>` into `Option.map`). -/
example {α β : Type u} (x : m α) (f : α → β) (p : β → Prop)
    (h : AllOutputs (fun a => p (f a)) x) : AllOutputs p (f <$> x) := by
  simp [h]

/-- Applicative sequencing nests the judgment. -/
example {α β : Type u} (f : m (α → β)) (x : m α) (p : β → Prop)
    (h : AllOutputs (fun g => AllOutputs (fun a => p (g a)) x) f) : AllOutputs p (f <*> x) := by
  simp [h]

/-- `match` on an option, through `Option.elim`, is indexed by `grind`. -/
example (o : Option Bool) (x : Option Nat) (f : Bool → Option Nat) (a : Nat)
    (hx : o = none → CanReturn x a) (hf : ∀ b, o = some b → CanReturn (f b) a) :
    CanReturn (o.elim x f) a := by
  grind

/-- `match` on a sum, through `Sum.elim`, likewise. -/
example (s : Bool ⊕ Nat) (f : Bool → Option Nat) (g : Nat → Option Nat) (a : Nat)
    (hf : ∀ b, s = .inl b → CanReturn (f b) a) (hg : ∀ n, s = .inr n → CanReturn (g n) a) :
    CanReturn (s.elim f g) a := by
  grind

/-- The judgment forms of the case splits reduce by `simp` on a concrete scrutinee. -/
example (x : Option Nat) (f : Bool → Option Nat) (p : Nat → Prop) (h : AllOutputs p (f true)) :
    AllOutputs p ((some true).elim x f) := by
  simp [h]
