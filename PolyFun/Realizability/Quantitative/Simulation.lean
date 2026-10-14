/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import ToCslib.Algebra.Polynomial

/-!
# Polynomial simulation between quantitative backends

`Q₁.SimulatedBy Q₂ str` translates every piece of `Q₁` code into `Q₂` code realizing the same
function, so `Q₂` simulates `Q₁`. It controls representation sizes in both directions, and its
cost polynomial may depend on the translated code, as in machine simulations whose overhead
depends on tape count. Simulations compose (`SimulatedBy.id`, `SimulatedBy.comp`) and transport
each `PolyRealizer`; family transport additionally requires uniform canonical-time and
description bounds.
-/

public section

universe u v w v' w' v'' w''

open Complexity

namespace PFunctor.QuantitativeStepClass

/-- A polynomial simulation of the backend `Q₁` by the backend `Q₂`: every `Q₁` code translates
to `Q₂` code realizing the same function along the representation map `str`. -/
structure SimulatedBy {C₁ : StepClass.{u, v}} {C₂ : StepClass.{u, v'}}
    (Q₁ : QuantitativeStepClass.{u, v, w} C₁) (Q₂ : QuantitativeStepClass.{u, v', w'} C₂)
    (str : ∀ {A : Type u}, C₁.Str A → C₂.Str A) where
  /-- Translate code. -/
  code : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B},
    Q₁.Realizer a b f → Q₂.Realizer (str a) (str b) f
  /-- Polynomial upper bound on translated sizes. -/
  sizeBound : Polynomial ℕ
  /-- Translated sizes obey the bound. -/
  size_le : ∀ {A : Type u} (a : C₁.Str A) (x : A), Q₂.size (str a) x ≤ sizeBound.eval (Q₁.size a x)
  /-- Source sizes are polynomially recoverable from translated sizes. -/
  sizeLower : Polynomial ℕ
  /-- Lower size comparison, needed to state bounds in target input size. -/
  size_ge : ∀ {A : Type u} (a : C₁.Str A) (x : A),
    Q₁.size a x ≤ sizeLower.eval (Q₂.size (str a) x)
  /-- Cost polynomial for each fixed code. It may depend on the code, for example on the number
  of tapes of a simulated machine. -/
  costBound : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B},
    Q₁.Realizer a b f → Polynomial ℕ
  /-- Translated cost obeys the bound. -/
  cost_le : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B} (r : Q₁.Realizer a b f)
    (x : A), Q₂.cost (code r) x ≤ (costBound r).eval (Q₁.size a x + Q₁.cost r x)

namespace SimulatedBy

variable {C₁ : StepClass.{u, v}} {C₂ : StepClass.{u, v'}} {C₃ : StepClass.{u, v''}}
  {Q₁ : QuantitativeStepClass.{u, v, w} C₁} {Q₂ : QuantitativeStepClass.{u, v', w'} C₂}
  {Q₃ : QuantitativeStepClass.{u, v'', w''} C₃}
  {str : ∀ {A : Type u}, C₁.Str A → C₂.Str A}

/-- Every backend simulates itself by the identity translation. -/
protected noncomputable def id (Q : QuantitativeStepClass.{u, v, w} C₁) :
    Q.SimulatedBy Q (fun a ↦ a) where
  code r := r
  sizeBound := Polynomial.X
  size_le _ _ := by simp
  sizeLower := Polynomial.X
  size_ge _ _ := by simp
  costBound _ := Polynomial.X
  cost_le _ _ := by
    simp only [Polynomial.eval_X]
    omega

/-- Simulations compose: translate along `S₁`, then along `S₂`. The composite cost polynomial
evaluates `S₂`'s polynomial for the translated code at `S₁`'s size bound plus its cost bound. -/
protected noncomputable def comp {str₂ : ∀ {A : Type u}, C₂.Str A → C₃.Str A}
    (S₁ : Q₁.SimulatedBy Q₂ str) (S₂ : Q₂.SimulatedBy Q₃ str₂) :
    Q₁.SimulatedBy Q₃ (fun a ↦ str₂ (str a)) where
  code r := S₂.code (S₁.code r)
  sizeBound := S₂.sizeBound.comp S₁.sizeBound
  size_le a x := by
    rw [Polynomial.eval_comp]
    exact (S₂.size_le (str a) x).trans (Polynomial.eval_le_eval (S₁.size_le a x))
  sizeLower := S₁.sizeLower.comp S₂.sizeLower
  size_ge a x := by
    rw [Polynomial.eval_comp]
    exact (S₁.size_ge a x).trans (Polynomial.eval_le_eval (S₂.size_ge (str a) x))
  costBound r := (S₂.costBound (S₁.code r)).comp (S₁.sizeBound + S₁.costBound r)
  cost_le r x := by
    rw [Polynomial.eval_comp, Polynomial.eval_add]
    exact (S₂.cost_le (S₁.code r) x).trans <| Polynomial.eval_le_eval <| Nat.add_le_add
      ((S₁.size_le _ x).trans (Polynomial.eval_le_eval (Nat.le_add_right _ _)))
      (S₁.cost_le r x)

/-- Translate a polynomial certificate using both size comparisons and the fixed code's
cost overhead. This construction alone provides no uniform bound for a family of codes. -/
noncomputable def polyRealizer (S : Q₁.SimulatedBy Q₂ str)
    {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B} (r : Q₁.PolyRealizer a b f) :
    Q₂.PolyRealizer (str a) (str b) f where
  code := S.code r.code
  work := FirstOrderPolynomial.comp (FirstOrderPolynomial.ofNatPolynomial (S.costBound r.code))
    (FirstOrderPolynomial.add (FirstOrderPolynomial.ofNatPolynomial S.sizeLower)
      (FirstOrderPolynomial.comp r.work (FirstOrderPolynomial.ofNatPolynomial S.sizeLower)))
  outputSize := FirstOrderPolynomial.comp (FirstOrderPolynomial.ofNatPolynomial S.sizeBound)
    (FirstOrderPolynomial.comp r.outputSize (FirstOrderPolynomial.ofNatPolynomial S.sizeLower))
  work_le x := by
    have h1 := S.cost_le r.code x
    have h2 : Q₁.size a x + Q₁.cost r.code x ≤
        S.sizeLower.eval (Q₂.size (str a) x) +
          r.work.eval (S.sizeLower.eval (Q₂.size (str a) x)) := by
      have hs := S.size_ge a x
      have hw := (r.work_le x).trans (r.work.eval_monotone hs)
      omega
    simp only [FirstOrderPolynomial.eval_comp, FirstOrderPolynomial.eval_add,
      FirstOrderPolynomial.eval_ofNatPolynomial]
    exact h1.trans (Polynomial.eval_le_eval h2)
  outputSize_le x := by
    have h1 := S.size_le b (f x)
    have h2 : Q₁.size b (f x) ≤ r.outputSize.eval (S.sizeLower.eval (Q₂.size (str a) x)) :=
      (r.outputSize_le x).trans (r.outputSize.eval_monotone (S.size_ge a x))
    simp only [FirstOrderPolynomial.eval_comp, FirstOrderPolynomial.eval_ofNatPolynomial]
    exact h1.trans (Polynomial.eval_le_eval h2)

end SimulatedBy

end PFunctor.QuantitativeStepClass
