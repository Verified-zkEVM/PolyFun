/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Simulation
public import PolyFun.Realizability.Quantitative.Family

/-!
# Uniform bounds for backend simulations

A fixed-code simulation need not preserve polynomial advice or uniformly bounded canonical time.
`DescriptionBound` supplies the former. `FamilyBound` also controls the target's selected time
envelope, allowing polynomial dependence on the source description size. Together they transport
`FamRealizer` without assuming a single overhead constant for machines with arbitrarily many tapes.
-/

public section

universe u v w v' w' x x'

namespace PFunctor.QuantitativeStepClass.Simulates

variable {C₁ : StepClass.{u, v}} {C₂ : StepClass.{u, v'}}
  {Q₁ : QuantitativeStepClass.{u, v, w} C₁} {Q₂ : QuantitativeStepClass.{u, v', w'} C₂}
  {str : ∀ {A : Type u}, C₁.Str A → C₂.Str A}
  {faithful₁ : ∀ {A : Type u}, C₁.Str A → Prop}
  {faithful₂ : ∀ {A : Type u}, C₂.Str A → Prop}

/-- Uniform control of translated code size, separate from operational cost. -/
structure DescriptionBound (S : Q₁.Simulates Q₂ str)
    (M₁ : Q₁.DescriptionMeasure.{u, v, w, x} faithful₁)
    (M₂ : Q₂.DescriptionMeasure.{u, v', w', x'} faithful₂) where
  /-- A polynomial in source description size. -/
  polynomial : Polynomial ℕ
  /-- Translated descriptions obey this polynomial. -/
  desc_le : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B}
    (r : Q₁.Realizer a b f), M₂.descSize (S.code r) ≤ polynomial.eval (M₁.descSize r)

variable [Q₁.HasComposition] [Q₂.HasComposition]
  {M₁ : Q₁.DescriptionMeasure.{u, v, w, x} faithful₁}
  {M₂ : Q₂.DescriptionMeasure.{u, v', w', x'} faithful₂}

/-- Uniform canonical-time and advice control for a simulation. Operational cost control alone
cannot constrain an arbitrarily widened target canonical envelope. -/
structure FamilyBound (S : Q₁.Simulates Q₂ str)
    (PB₁ : M₁.PolynomialBackend) (PB₂ : M₂.PolynomialBackend)
    extends DescriptionBound S M₁ M₂ where
  /-- A polynomial in input length, source canonical time and source code size. -/
  time : Polynomial ℕ
  /-- The target canonical envelope obeys the uniform polynomial at every length. -/
  time_le : ∀ {A B : Type u} {a : C₁.Str A} {b : C₁.Str B} {f : A → B}
    (r : Q₁.Realizer a b f) (k : ℕ),
    (PB₂.timeOf (S.code r)).eval k ≤
      time.eval (k + (PB₁.timeOf r).eval (S.sizeLower.eval k) + M₁.descSize r)

/-- Translate a whole family using uniform canonical-time and description comparisons. -/
noncomputable def FamilyBound.famRealizer {S : Q₁.Simulates Q₂ str}
    {PB₁ : M₁.PolynomialBackend} {PB₂ : M₂.PolynomialBackend}
    (h : FamilyBound S PB₁ PB₂)
    {A B : ℕ → Type u} {a : ∀ n, C₁.Str (A n)} {b : ∀ n, C₁.Str (B n)}
    {f : ∀ n, A n → B n} (F : M₁.FamRealizer PB₁ a b f) :
    M₂.FamRealizer PB₂ (fun n ↦ str (a n)) (fun n ↦ str (b n)) f where
  wit n := S.code (F.wit n)
  time := h.time.comp (Polynomial.X + F.time.comp (Polynomial.X + S.sizeLower) + F.desc)
  time_le n k := by
    have hk : k ≤ n + k := Nat.le_add_left k n
    have hn : n ≤ n + k := Nat.le_add_right n k
    have hi : n + S.sizeLower.eval k ≤ n + k + S.sizeLower.eval (n + k) :=
      Nat.add_le_add hn (Polynomial.eval_le_eval hk)
    have ht := (F.time_le n (S.sizeLower.eval k)).trans (Polynomial.eval_le_eval hi)
    have hd := (F.desc_le n).trans (Polynomial.eval_le_eval hn)
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
    exact (h.time_le (F.wit n) k).trans
      (Polynomial.eval_le_eval (Nat.add_le_add (Nat.add_le_add hk ht) hd))
  desc := h.polynomial.comp F.desc
  desc_le n := by
    rw [Polynomial.eval_comp]
    exact (h.desc_le (F.wit n)).trans (Polynomial.eval_le_eval (F.desc_le n))

end PFunctor.QuantitativeStepClass.Simulates
