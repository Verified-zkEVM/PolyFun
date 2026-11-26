/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Uses
public import ToCslib.MeasureTheory.Integral.Marginal
public import Mathlib.Probability.UniformOn

/-!
# Scoped terms over a product of random tapes

An interpretation that depends on a tape `x : ∀ j, X j` makes the meaning of a term a function of
the tape. Suppose that the interpretation of every head the term uses ignores coordinate `i` of
the tape. Then so does the meaning of the term (`Term.denote_update_eq`), by
`Term.denote_congr_of_agreeOn_heads` and without an induction over the term.

Under a finite product of probability measures on tapes, such a meaning therefore takes the value
of coordinate `i` with probability at most the largest mass that the law of coordinate `i` gives
a point (`Term.pi_setOf_denote_eq_apply_le`). For a uniform coordinate over a finite type the
bound is the inverse of its cardinality (`Term.pi_setOf_denote_eq_apply_le_inv_card`).
-/

public section

universe u v w z

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IPFunctor.ScopedSignature.Term

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {V : S → Type z} {Γ : List S} {a : S}
  {ι : Type*} {X : ι → Type*}

/-- If the interpretation of every head a term uses ignores coordinate `i` of the tape, then so
does the meaning of the term. -/
theorem denote_update_eq [DecidableEq ι] (alg : (∀ j, X j) → Interpretation σ V)
    (t : σ.Term Γ a) {i : ι}
    (hi : ∀ h ∈ t.heads, ∀ x y, alg (Function.update x i y) h.op = alg x h.op)
    (x : ∀ j, X j) (y : X i) :
    t.denote (alg (Function.update x i y)) = t.denote (alg x) :=
  denote_congr_of_agreeOn_heads t fun h hh => hi h hh x y

/-- Suppose that the interpretation of every head a term uses ignores coordinate `i` of a random
tape, and that the law of coordinate `i` gives each point mass at most `p`. Then an observation
`obs` of the term's meaning equals coordinate `i` with probability at most `p`. -/
theorem pi_setOf_denote_eq_apply_le [Fintype ι] [DecidableEq ι] [∀ j, MeasurableSpace (X j)]
    (μ : ∀ j, Measure (X j)) [∀ j, IsProbabilityMeasure (μ j)] {i : ι} [MeasurableEq (X i)]
    (alg : (∀ j, X j) → Interpretation σ V) (t : σ.Term Γ a) (η : Env V Γ) (obs : V a → X i)
    (hmeas : Measurable fun x => obs (t.denote (alg x) η))
    (hi : ∀ h ∈ t.heads, ∀ x y, alg (Function.update x i y) h.op = alg x h.op)
    {p : ℝ≥0∞} (hp : ∀ y, μ i {y} ≤ p) :
    Measure.pi μ {x | obs (t.denote (alg x) η) = x i} ≤ p :=
  Measure.pi_setOf_eq_apply_le μ hmeas (fun x y => by rw [denote_update_eq alg t hi]) hp

/-- Over countable tape coordinates with measurable points, a term whose heads are interpreted
independently of a uniform coordinate `i` gives a meaning whose observation equals that
coordinate with probability at most `1 / |X i|`. -/
theorem pi_setOf_denote_eq_apply_le_inv_card [Fintype ι] [DecidableEq ι]
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)] [∀ j, Countable (X j)]
    (μ : ∀ j, Measure (X j)) [∀ j, IsProbabilityMeasure (μ j)] {i : ι} [Fintype (X i)]
    (hμ : μ i = uniformOn Set.univ)
    (alg : (∀ j, X j) → Interpretation σ V) (t : σ.Term Γ a) (η : Env V Γ) (obs : V a → X i)
    (hi : ∀ h ∈ t.heads, ∀ x y, alg (Function.update x i y) h.op = alg x h.op) :
    Measure.pi μ {x | obs (t.denote (alg x) η) = x i} ≤ (Fintype.card (X i) : ℝ≥0∞)⁻¹ :=
  pi_setOf_denote_eq_apply_le μ alg t η obs (measurable_of_countable _) hi fun y => by
    rw [hμ, uniformOn_univ, Measure.count_singleton, one_div]

end IPFunctor.ScopedSignature.Term
