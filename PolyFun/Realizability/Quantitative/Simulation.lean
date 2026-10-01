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

A simulation preserves the realized function and controls representation sizes in both
directions. Its cost polynomial may depend on the translated code, as in machine simulations
whose overhead depends on tape count. This transports each `PolyRealizer`; family transport
additionally requires uniform canonical-time and description bounds.
-/

public section

universe u v w v' w'

open Complexity

namespace PFunctor.QuantitativeStepClass

/-- A polynomial simulation of one quantitative backend by another. -/
structure Simulates {C₁ : StepClass.{u, v}} {C₂ : StepClass.{u, v'}}
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
  /-- Cost overhead for each fixed code; this can depend on its tape or state count. -/
  costBound : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B},
    Q₁.Realizer a b f → Polynomial ℕ
  /-- Translated cost obeys the bound. -/
  cost_le : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B} (r : Q₁.Realizer a b f)
    (x : A), Q₂.cost (code r) x ≤ (costBound r).eval (Q₁.size a x + Q₁.cost r x)

namespace Simulates

variable {C₁ : StepClass.{u, v}} {C₂ : StepClass.{u, v'}}
  {Q₁ : QuantitativeStepClass.{u, v, w} C₁} {Q₂ : QuantitativeStepClass.{u, v', w'} C₂}
  {str : ∀ {A : Type u}, C₁.Str A → C₂.Str A}

/-- Translate a polynomial certificate using both size comparisons and the fixed code's
cost overhead. This construction alone provides no uniform bound for a family of codes. -/
noncomputable def polyRealizer (S : Q₁.Simulates Q₂ str)
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

end Simulates

end PFunctor.QuantitativeStepClass

