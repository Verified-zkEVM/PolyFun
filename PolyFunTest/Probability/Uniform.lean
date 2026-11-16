/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Uniform
public import Mathlib.Data.ZMod.Defs

/-!
# Uniform measures and uniform draws

Regression tests for the uniform-measure layer. The measure tests count events of the uniform
measure on `Fin 4` and on a finite set. They push the uniform measure through a translation of
`ZMod n` and through a measurable equivalence. The draw tests check that the uniform draws of
`EvalDist.IsUniform` stay uniform under bijections, never fail, and have counting event
probabilities. A fair die and a fair coin over free programs supply concrete uniform draws. A die
roll shifted by a bijection is uniform, and the exclusive or of two coin flips is a fair coin. A
generic interface with uniform answers states the same facts for every operation, and the
predicate is instantiated at outputs in `Type 1`.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor EvalDist
open scoped ENNReal

namespace PolyFunTest.Probability.Uniform

/-! ## The uniform measure -/

example : (uniformOn Set.univ : Measure (Fin 4)) {0} = 4⁻¹ := by simp

example : (uniformOn Set.univ : Measure (Fin 4)) {x | x.val < 3} = 3 / 4 := by
  rw [uniformOn_univ_apply_setOf]
  rfl

example : (uniformOn ({0, 1} : Finset (Fin 4)) : Measure (Fin 4)) {1} = 2⁻¹ := by
  rw [uniformOn_finset_apply_singleton]
  rfl

example : (uniformOn ({0, 1} : Finset (Fin 4)) : Measure (Fin 4)) {2} = 0 := by
  rw [uniformOn_finset_apply_singleton]
  rfl

/-- Translation is a bijection of `ZMod n`, so it preserves the uniform measure. -/
example (n : ℕ) [NeZero n] (k : ZMod n) :
    (uniformOn Set.univ : Measure (ZMod n)).map (· + k) = uniformOn Set.univ :=
  uniformOn_univ_map_equiv (Equiv.addRight k)

/-- A measurable equivalence preserves the uniform measure on any set, finite or not. -/
example (s : Set (ℕ × Bool)) :
    (uniformOn s).map MeasurableEquiv.prodComm = uniformOn (MeasurableEquiv.prodComm '' s) :=
  MeasurableEquiv.map_uniformOn _ s

/-- An injective map carries the uniform measure on a set to the uniform measure on its image. -/
example (s : Set ℕ) :
    (uniformOn s).map Nat.succ = uniformOn (Nat.succ '' s) :=
  map_uniformOn_of_injOn Measurable.of_discrete Nat.succ_injective.injOn

example : (uniformOn Set.univ : Measure (Bool × Bool)) =
    (uniformOn Set.univ : Measure Bool).prod (uniformOn Set.univ) :=
  uniformOn_univ_prod

example (f : Fin 4 → ℝ≥0∞) : ∫⁻ x, f x ∂uniformOn Set.univ = (∑ x, f x) / 4 := by
  rw [lintegral_uniformOn_univ]
  rfl

/-! ## Uniform draws in an abstract lawful monad -/

section Abstract

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- Translating a uniform residue gives a uniform residue that never fails, and each residue is
returned with probability `1 / n`. -/
example (n : ℕ) [NeZero n] (k : ZMod n) {mx : m (ZMod n)} (h : IsUniform mx) :
    IsUniform ((· + k) <$> mx) ∧ prFail ((· + k) <$> mx) = 0 ∧
      prEvent ((fun x ↦ x = 0) <$> ((· + k) <$> mx)) = (n : ℝ≥0∞)⁻¹ := by
  have hk : IsUniform ((· + k) <$> mx) := h.map_equiv (Equiv.addRight k)
  refine ⟨hk, hk.prFail_eq_zero, ?_⟩
  rw [hk.prEvent_eq_singleton, ZMod.card]

/-- An injection makes a uniform draw uniform on its range, which is a finite set here. -/
example {mx : m (Fin 2)} (h : IsUniform mx) :
    IsUniformOn (Fin.castSucc <$> mx) (Set.range Fin.castSucc) :=
  h.map_of_injective (Fin.castSucc_injective 2)

/-- Events of a uniform draw from a finite set are counting statements. -/
example {mx : m (Fin 4)} (h : IsUniformOn mx ({0, 1} : Finset (Fin 4))) :
    prEvent ((fun x ↦ x = 0) <$> mx) = 2⁻¹ ∧ prFail mx = 0 := by
  refine ⟨?_, h.prFail_eq_zero (Finset.finite_toSet _) ⟨0, by simp⟩⟩
  rw [h.prEvent_eq_singleton]
  rfl

/-- Two uniform draws from the same type are equal in distribution, and a bijection between two
uniform types transports events. -/
example {mx my : m Bool} (hx : IsUniform mx) (hy : IsUniform my) :
    EvalDistEq mx my ∧ prEvent ((fun b ↦ (!b) = true) <$> mx) = prEvent ((· = true) <$> my) :=
  ⟨hx.evalDistEq hy, hx.prEvent_comp_of_bijective hy Bool.involutive_not.bijective (· = true)⟩

/-- Reindexing a uniform draw by a bijection does not change any continuation. -/
example {mx : m Bool} (h : IsUniform mx) (f : Bool → m ℕ) :
    EvalDistEq (mx >>= fun b ↦ f !b) (mx >>= f) :=
  h.evalDistEq_bind_comp h Bool.involutive_not.bijective f

/-- An event of a uniform draw is certain exactly when every output satisfies it. -/
example {mx : m Bool} (h : IsUniform mx) : prEvent ((fun b ↦ b = b) <$> mx) = 1 :=
  (h.prEvent_eq_one_iff _).mpr fun _ ↦ rfl

end Abstract

/-! ## Uniform draws as free programs -/

/-- A die: one operation whose answer is a face. -/
@[expose, reducible] def Die : PFunctor.{0, 0} := ⟨Unit, fun _ => Fin 6⟩

/-- A fair die. -/
noncomputable instance : Die.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Die

/-- One roll. -/
@[expose] def roll : FreeM Die (Fin 6) := FreeM.lift (P := Die) ()

theorem isUniform_roll : IsUniform roll := FreeM.isUniform_lift (P := Die) () rfl

/-- A roll shifted by a bijection is uniform and never fails. Its events have counting
probabilities. -/
example (k : Fin 6) :
    IsUniform ((· + k) <$> roll) ∧ prFail ((· + k) <$> roll) = 0 ∧
      prEvent ((fun x ↦ x.val < 2) <$> ((· + k) <$> roll)) = 2 / 6 := by
  have hk : IsUniform ((· + k) <$> roll) := isUniform_roll.map_equiv (Equiv.addRight k)
  refine ⟨hk, hk.prFail_eq_zero, ?_⟩
  rw [hk.prEvent_eq]
  rfl

/-- A coin: one operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

theorem isUniform_flip : IsUniform flip := FreeM.isUniform_lift (P := Coin) () rfl

/-- Two independent flips are a uniform pair. -/
theorem isUniform_flip_pair : IsUniform (do let x ← flip; let y ← flip; return (x, y)) :=
  isUniform_flip.pair isUniform_flip

/-- The pair of a flip and its exclusive or with a second flip is a bijective image of two flips,
so it is uniform. Its second component is a fair coin. -/
example : IsUniform ((fun p : Bool × Bool ↦ (p.1, xor p.1 p.2)) <$>
    (do let x ← flip; let y ← flip; return (x, y))) :=
  isUniform_flip_pair.map_of_bijective <| Function.Involutive.bijective fun ⟨a, b⟩ ↦ by
    cases a <;> cases b <;> rfl

example : prEvent ((fun p : Bool × Bool ↦ xor p.1 p.2 = true) <$>
    (do let x ← flip; let y ← flip; return (x, y))) = 2 / 4 := by
  rw [isUniform_flip_pair.prEvent_eq]
  rfl

/-! ## A generic interface with uniform answers -/

section Generic

variable {P : PFunctor.{0, 0}} [∀ a, MeasurableSpace (P.B a)] [∀ a, DiscreteMeasurableSpace (P.B a)]
  [P.AnswerMeasure]

/-- A call with uniform answers, post-processed by a bijection, is a uniform draw that never fails,
and its events have counting probabilities. -/
example (a : P.A) (h : AnswerMeasure.toMeasure a = uniformOn Set.univ) {β : Type} [Fintype β]
    {f : P.B a → β} (hf : f.Bijective) (p : β → Prop) [DecidablePred p] :
    IsUniform (f <$> FreeM.lift a) ∧ prFail (f <$> FreeM.lift a) = 0 ∧
      prEvent (p <$> (f <$> FreeM.lift a)) =
        ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card β := by
  have hf' : IsUniform (f <$> FreeM.lift a) := (FreeM.isUniform_lift a h).map_of_bijective hf
  have := AnswerMeasure.finite_of_toMeasure_eq_uniformOn h
  have := AnswerMeasure.nonempty a
  have : Nonempty β := ⟨f (Classical.arbitrary _)⟩
  exact ⟨hf', hf'.prFail_eq_zero, hf'.prEvent_eq p⟩

/-- Under the uniform answer measures of `uniformOfFiniteNonempty`, every call is a uniform
draw. -/
example [∀ a, Finite (P.B a)] [∀ a, Nonempty (P.B a)] (a : P.A) :
    letI := AnswerMeasure.uniformOfFiniteNonempty P
    IsUniform (FreeM.lift a : FreeM P (P.B a)) :=
  letI := AnswerMeasure.uniformOfFiniteNonempty P
  FreeM.isUniform_lift a rfl

end Generic

/-! ## Universes -/

section Universes

variable {m : Type 1 → Type 1} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- The predicate and its map and failure laws apply at outputs in `Type 1`. -/
example {mx : m (ULift.{1} Bool)} (h : IsUniform mx) :
    IsUniform ((fun b ↦ ULift.up (!b.down)) <$> mx) ∧ prFail mx = 0 :=
  ⟨h.map_of_bijective (Function.Involutive.bijective fun _ ↦ by simp), h.prFail_eq_zero⟩

end Universes

end PolyFunTest.Probability.Uniform
