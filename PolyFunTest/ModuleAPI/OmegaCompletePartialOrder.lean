/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import ToCslib.Order.Admissible
import ToCslib.Order.PrefixRecursion

/-!
# Ordinary-import canaries for omega-CPO fixed points

Discrete, lifted, and disjoint-sum carriers are omega-CPOs, and least fixed points,
admissibility, and prefix recursion are usable through ordinary imports. The lazy value
domain `WithBot (DiscreteOrder Bool ⊕ DiscreteOrder Nat)` has an undefined result, a
Boolean flag, or a natural number. Fixed-point induction accepts an `Admissible` proof
for its closure hypothesis by unfolding, as downstream logical relations use it.
-/

open OmegaCompletePartialOrder

example : OmegaCompletePartialOrder (DiscreteOrder Nat) := inferInstance
example : Nonempty (OmegaCompletePartialOrder (DiscreteOrder Bool ⊕ DiscreteOrder Nat)) :=
  ⟨inferInstance⟩
example : Nonempty (OmegaCompletePartialOrder (WithBot (DiscreteOrder Bool ⊕ DiscreteOrder Nat))) :=
  ⟨inferInstance⟩
example : OrderBot (WithBot (DiscreteOrder Bool ⊕ DiscreteOrder Nat)) := inferInstance

example (a b : DiscreteOrder Nat) : a ≤ b ↔ a = b := DiscreteOrder.le_iff_eq a b

/-- Admissibility closes under the lifted sum used for lazy values. -/
example (p : DiscreteOrder Bool → Prop) (q : DiscreteOrder Nat → Prop) :
    Admissible (WithBot.recBotCoe True (Sum.elim p q)) :=
  (Admissible.sum (admissible_discrete p) (admissible_discrete q)).withBot

example {ι : Type} (p : ι → DiscreteOrder Nat → Prop) : Admissible (fun x => ∀ i, p i x) :=
  Admissible.forall fun i => admissible_discrete (p i)

section Fix

variable (f : WithBot (DiscreteOrder Nat) →𝒄 WithBot (DiscreteOrder Nat))

/-- A constant body has its value as the least fixed point. -/
example (v : WithBot (DiscreteOrder Nat)) :
    (ContinuousHom.const v : WithBot (DiscreteOrder Nat) →𝒄 _).fix = v :=
  (ContinuousHom.const v).map_fix.symm

example (n : ℕ) : f.approximants n ≤ f.fix := f.approximants_le_fix n

example {x : WithBot (DiscreteOrder Nat)} (h : f x ≤ x) : f.fix ≤ x := f.fix_le h

example : f f.fix = f.fix := f.map_fix

example : f.fix = ωSup (fixedPoints.iterateChain f ⊥ bot_le) := f.fix_eq_ωSup_iterateChain

/-- The closure hypothesis of `fix_induction` accepts an admissibility proof. -/
example (p : DiscreteOrder Nat → Prop) (hp : Admissible p)
    (hstep : ∀ x, WithBot.recBotCoe True p x → WithBot.recBotCoe True p (f x)) :
    WithBot.recBotCoe True p f.fix :=
  f.fix_induction _ trivial hstep hp.withBot

example (p : DiscreteOrder Nat → Prop) (hp : Admissible p)
    (hstep : ∀ x, WithBot.recBotCoe True p x → WithBot.recBotCoe True p (f x)) :
    WithBot.recBotCoe True p f.fix :=
  hp.withBot.fix_induction f trivial hstep

/-- Strict continuous maps commuting with recursive bodies preserve least fixed points. -/
example (g h : WithBot (DiscreteOrder Nat) →𝒄 WithBot (DiscreteOrder Nat))
    (hbot : h ⊥ = ⊥) (hcomm : ∀ x, h (f x) = g (h x)) : h f.fix = g.fix :=
  ContinuousHom.fix_fusion f g h hbot hcomm

end Fix

/-- Function types carry their pointwise omega-CPO instance; leastness still identifies
`fix` with the lattice least fixed point. -/
example (f : (Nat → Prop) →𝒄 (Nat → Prop)) : f.fix = OrderHom.lfp f.toOrderHom :=
  f.isLeast_fix.unique (OrderHom.isLeast_lfp_le _)

example (f : Prop →𝒄 Prop) : f.fix = OrderHom.lfp f.toOrderHom := f.fix_eq_lfp

example (f : DiscreteOrder Nat →𝒄 WithBot (DiscreteOrder Bool)) : WithBot.extend f ⊥ = ⊥ := rfl

example (f : Nat → WithBot (DiscreteOrder Bool)) (n : Nat) :
    DiscreteOrder.continuousMap f ⟨n⟩ = f n := rfl

/-- Finite prefix equations: the least fixed point is the well-founded solution. -/
example {n : Nat} (step : (i : Fin n) →
      (Fin i.val → WithBot (DiscreteOrder Nat)) →𝒄 WithBot (DiscreteOrder Nat)) :
    (ContinuousHom.prefixMap step).fix = Function.prefixRecursion (fun i => step i) :=
  ContinuousHom.prefixMap_fix step
