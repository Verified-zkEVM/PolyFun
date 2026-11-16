/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Relational.Algebra
public import PolyFun.Control.Monad.Measure.Relational.Deterministic
public import PolyFun.PFunctor.Free.Measure.Support

/-!
# Couplings and relational reasoning

Regression tests for measure couplings, the coupling predicates `ExpectationWP.CouplingPost` and
`ExpectationWP.RelWP`, countable support, and the relational algebra
`ExpectationWP.couplingAlgebra`. They cover equality in distribution to and from the diagonal
coupling, graph couplings, couplings concentrated on a graph, the trivial relation on equal
masses, deterministic carriers, and a relational proof about a fair coin through PolyFun's generic
relational triple rules.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor ExpectationWP

namespace PolyFunTest.Probability.Coupling

/-! ## Measure couplings -/

section Measures

variable {α : Type} [MeasurableSpace α]

/-- A coupling concentrated on the diagonal has equal marginals. -/
example {μ ν : Measure α} (h : CouplingPost μ ν (· = ·)) : μ = ν := h.eq

/-- Finite measures of equal total mass are related by the trivial relation. -/
example (x y : Bool) :
    CouplingPost (2 • Measure.dirac x) (2 • Measure.dirac y) fun _ _ ↦ True :=
  couplingPost_true_iff.2 (by simp)

/-- Measures of different total mass have no coupling. -/
example (x : Bool) : ¬CouplingPost (Measure.dirac x) (0 : Measure Bool) fun _ _ ↦ True := by
  rw [couplingPost_true_iff]
  simp

/-- A coupling composes with the graph coupling of a measurable map. -/
example {μ ν : Measure Bool} (h : CouplingPost μ ν (· = ·)) :
    CouplingPost μ (ν.map not) fun a b ↦ b = !a :=
  h.trans_graph measurable_from_top ⟨⟨_, Measure.IsCoupling.graph ν measurable_from_top⟩,
    (ae_map_iff (measurable_id.prodMk measurable_from_top).aemeasurable
      MeasurableSet.of_discrete).2 (Filter.Eventually.of_forall fun _ ↦ rfl)⟩
    MeasurableSet.of_discrete fun _ _ h ↦ h ▸ rfl

/-- A coupling concentrated on the graph of `not` is the graph coupling of its first marginal. -/
example {μ ν : Measure Bool} {c : Measure (Bool × Bool)} (h : c.IsCoupling μ ν)
    (hc : ∀ᵐ z ∂c, z.2 = !z.1) : c = μ.map fun a ↦ (a, !a) :=
  h.joint_eq_map_of_ae_eq measurable_from_top hc

/-- The diagonal coupling of `ν` composes with the graph coupling of `not`, which is concentrated
on the graph of `not`. -/
example (ν : Measure Bool) :
    ((ν.map fun a ↦ (a, a)).map fun z ↦ (z.1, !z.2)).IsCoupling ν (ν.map not) :=
  (Measure.IsCoupling.refl ν).trans_of_ae_eq (Measure.IsCoupling.graph ν measurable_from_top)
    measurable_from_top
    ((ae_map_iff (measurable_id.prodMk measurable_from_top).aemeasurable
      MeasurableSet.of_discrete).2 (Filter.Eventually.of_forall fun _ ↦ rfl))

end Measures

/-! ## Deterministic carriers -/

example : CountableEvalDist Id := inferInstance

example : CountableEvalDist Option := inferInstance

example : CountableEvalDist (Except String) := inferInstance

example (a b : ℕ) : RelWP (some a) (some b) (· ≤ ·) ↔ a ≤ b := by simp

example : RelWP (none : Option ℕ) (none : Option ℕ) fun _ _ ↦ False :=
  ⟨⟨0, by constructor <;> simp⟩, by simp⟩

/-- A failure and a success have different masses, so no relation holds between them. -/
example (R : ℕ → ℕ → Prop) : ¬RelWP (none : Option ℕ) (some 0) R :=
  not_relWP_of_mass_ne _ _ (by simp) R

/-- A coupling of two output measures concentrated on the diagonal gives equality in
distribution. -/
example {mx : Option ℕ} {my : Id ℕ} {c : Measure (ℕ × ℕ)}
    (hc : c.IsCoupling (evalDist mx) (evalDist my)) (hdiag : ∀ᵐ z ∂c, z.1 = z.2) :
    EvalDistEq mx my :=
  EvalDistEq.of_coupling hc hdiag

/-- Equality in distribution across carriers is the diagonal coupling. -/
example (n : ℕ) : EvalDistEq (some n) (pure n : Id ℕ) :=
  (evalDistEq_iff_relWP_eq (α := ℕ)).2
    ((relWP_pure_pure_iff (m₁ := Option) (m₂ := Id) n n _).2 rfl)

/-! ## A fair coin -/

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Bool⟩

/-- A fair coin: uniform answers on the two-point type. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

example : CountableEvalDist (FreeM Coin) := inferInstance

/-- Every coin program is related to itself by equality. -/
example (program : FreeM Coin ℕ) : RelWP program program (· = ·) :=
  relWP_refl_of_countableEvalDist program

/-- Two lossless programs are related by the trivial relation. -/
example (program : FreeM Coin ℕ) (program' : FreeM Coin Bool) :
    RelWP program program' fun _ _ ↦ True :=
  (relWP_true_iff _ _).2 (by simp only [measure_univ])

/-- A program is related to its image under a map by the graph of the map. -/
example (program : FreeM Coin Bool) (f : Bool → Bool) :
    RelWP program (f <$> program) fun a b ↦ b = f a := by
  rw [RelWP, evalDist_map_of_discrete]
  exact ⟨⟨_, Measure.IsCoupling.graph _ measurable_from_top⟩,
    (ae_map_iff (measurable_id.prodMk measurable_from_top).aemeasurable
      MeasurableSet.of_discrete).2 (Filter.Eventually.of_forall fun _ ↦ rfl)⟩

/-- The generic relational rules of `MAlgRelOrdered` apply to coupling judgments: two coin
programs combining their flips in opposite orders are related by equality, step by step. -/
theorem xor_comm_triple :
    letI := couplingAlgebra (FreeM Coin) (FreeM Coin)
    MAlgRelOrdered.Triple True
      (do let a ← flip; let b ← flip; pure (xor a b))
      (do let a ← flip; let b ← flip; pure (xor b a)) (· = ·) := by
  let := couplingAlgebra (FreeM Coin) (FreeM Coin)
  have hflip : MAlgRelOrdered.Triple True flip flip (· = ·) := fun _ ↦
    (couplingAlgebra_relWP_iff flip flip _).2 (relWP_refl_of_countableEvalDist flip)
  refine MAlgRelOrdered.triple_bind hflip fun a a' ↦ ?_
  refine MAlgRelOrdered.triple_bind (cut := fun b b' ↦ a = a' ∧ b = b') (fun ha ↦ ?_)
    fun b b' ↦ MAlgRelOrdered.triple_pure fun ⟨ha, hb⟩ ↦ by subst ha hb; exact Bool.xor_comm _ _
  exact (couplingAlgebra_relWP_iff flip flip _).2
    (relWP_mono (relWP_refl_of_countableEvalDist flip) fun _ _ hb ↦ ⟨ha, hb⟩)

/-- The relational proof gives equality in distribution. -/
example :
    EvalDistEq (do let a ← flip; let b ← flip; pure (xor a b))
      (do let a ← flip; let b ← flip; pure (xor b a)) :=
  EvalDistEq.of_relWP_eq ((couplingAlgebra_relWP_iff _ _ _).1 (xor_comm_triple trivial))

/-! ## Universes -/

section Universes

variable {P : PFunctor.{0, 1}} [∀ a, MeasurableSpace (P.B a)] [∀ a, DiscreteMeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [P.AnswerMeasure]

example : CountableEvalDist (FreeM.{0, 0, 1} P) := inferInstance

example : CountableEvalDist (FreeM.{2, 0, 1} P) := inferInstance

/-- The relational algebra applies to programs whose answers live in `Type 1`. -/
noncomputable example : MAlgRelOrdered (FreeM.{0, 0, 1} P) (FreeM.{0, 0, 1} P) Prop :=
  couplingAlgebra _ _

end Universes

end PolyFunTest.Probability.Coupling
