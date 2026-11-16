/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Free.Measure.Path
public import PolyFun.PFunctor.Free.Measure.Lintegral

/-!
# Expected charge of free programs

`PFunctor.OpSpec.expectedCharge ν c` reads a call at `a` as costing `c a`, followed by the expected
value of its continuation under the answer measure `ν a`: `c a + ∫⁻ b, k b ∂ν a`. Its fold at the
zero leaf cost, `wpFold (OpSpec.expectedCharge ν c) x fun _ => 0`, is the expected charge of `x`.
The spec is the worst-case reading `OpSpec.charge c`, whose fold is `FreeM.cost c x`, with the
integral in place of the supremum.

## Main statements

* `FreeM.wpFold_expectedCharge_eq_add`: over discrete answers the leaf costs split off, so the
  expected charge-to-go is the expected charge plus the expectation of the leaf costs, which is
  their integral under the measure fold (`FreeM.wpFold_expectedCharge_eq_add_lintegral`).
* `FreeM.wpFold_expectedCharge_le_costWith`: under subprobability answers the expected charge is
  at most the worst-case charge.
* `FreeM.lintegral_measureFold_withPathCharge`: under probability answers over discrete answer
  types, the expected charge is the integral of the charge of the completed path under the
  measure fold of `withPathCharge c x`. The charge of a call is paid before the call, so the
  identity needs answer measures of total mass one. `FreeM.expectedQueryCount_eq_wpFold` is the
  unit charge under `PFunctor.AnswerMeasure`.
* `FreeM.wpFold_expectedCharge_liftM_le`: **expected-cost transfer**. If each implementation of a
  free handler has expected charge at most `c a`, the simulated program has expected charge at most
  the source program's expected charge under `c`, with each call answered by the measure fold of
  its implementation. It is an instance of `FreeM.wpFold_liftM_le`, and
  `FreeM.wpFold_expectedCharge_liftM` is the exact form.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe uA uB uA₂ uB₂ v w

namespace PFunctor

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]

/-! ## The expected-charge spec -/

/-- The expected-charge reading of answer measures `ν`: a call at `a` costs `c a`, followed by the
expected value of its continuation under `ν a`. -/
noncomputable def OpSpec.expectedCharge (ν : (a : P.A) → Measure (P.B a)) (c : P.A → ℝ≥0∞) :
    OpSpec P ℝ≥0∞ :=
  fun a k => c a + ∫⁻ b, k b ∂ν a

@[simp]
theorem OpSpec.expectedCharge_apply (ν : (a : P.A) → Measure (P.B a)) (c : P.A → ℝ≥0∞) (a : P.A)
    (k : P.B a → ℝ≥0∞) : OpSpec.expectedCharge ν c a k = c a + ∫⁻ b, k b ∂ν a :=
  rfl

/-- The expected-charge reading is monotone in the continuation. -/
theorem OpSpec.expectedCharge_mono (ν : (a : P.A) → Measure (P.B a)) (c : P.A → ℝ≥0∞) :
    (OpSpec.expectedCharge ν c).Monotone :=
  fun _ _ _ hk => add_le_add_right (MeasureTheory.lintegral_mono hk) _

/-- Under subprobability answers, the expected charge of a call is at most its worst-case
charge. -/
theorem OpSpec.expectedCharge_le_charge (ν : (a : P.A) → Measure (P.B a))
    [∀ a, IsSubprobabilityMeasure (ν a)] (c : P.A → ℝ≥0∞) (a : P.A) (k : P.B a → ℝ≥0∞) :
    OpSpec.expectedCharge ν c a k ≤ OpSpec.charge c a k := by
  refine add_le_add_right ?_ _
  calc ∫⁻ b, k b ∂ν a ≤ ∫⁻ _, ⨆ b, k b ∂ν a := MeasureTheory.lintegral_mono (le_iSup k)
    _ = (⨆ b, k b) * ν a Set.univ := lintegral_const _
    _ ≤ ⨆ b, k b := mul_le_of_le_one_right' (measure_univ_le (ν a))

namespace FreeM

/-! ## Expected and worst-case charge -/

section Expected

variable (ν : (a : P.A) → Measure (P.B a)) (c : P.A → ℝ≥0∞) {α : Type v}

/-- Over discrete answers, the leaf costs split off: the expected charge-to-go is the expected
charge plus the expectation of the leaf costs. Integration is additive on the measurable
continuations that discrete answers give. -/
theorem wpFold_expectedCharge_eq_add [∀ a, DiscreteMeasurableSpace (P.B a)] (x : FreeM P α)
    (post : α → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge ν c) x post =
      wpFold (OpSpec.expectedCharge ν c) x (fun _ => 0) + wpFold (OpSpec.lintegral ν) x post := by
  induction x with
  | pure _ => exact (zero_add _).symm
  | lift_bind a cont ih =>
      change c a + ∫⁻ b, wpFold (OpSpec.expectedCharge ν c) (cont b) post ∂ν a =
        (c a + ∫⁻ b, wpFold (OpSpec.expectedCharge ν c) (cont b) (fun _ => 0) ∂ν a) +
          ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) post ∂ν a
      simp only [ih]
      rw [lintegral_add_left Measurable.of_discrete, add_assoc]

/-- Over discrete answers, the expected charge-to-go of a measurable leaf cost is the expected
charge plus the integral of the leaf cost under the measure fold. -/
theorem wpFold_expectedCharge_eq_add_lintegral [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace α] (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) :
    wpFold (OpSpec.expectedCharge ν c) x post =
      wpFold (OpSpec.expectedCharge ν c) x (fun _ => 0) + ∫⁻ r, post r ∂measureFold ν x := by
  rw [wpFold_expectedCharge_eq_add, lintegral_measureFold_eq_wpFold ν x hpost]

/-- Under subprobability answers, the expected charge-to-go is at most the worst-case
charge-to-go. -/
theorem wpFold_expectedCharge_le_costWith [∀ a, IsSubprobabilityMeasure (ν a)] (x : FreeM P α)
    (post : α → ℝ≥0∞) : wpFold (OpSpec.expectedCharge ν c) x post ≤ costWith c x post :=
  wpFold_le_wpFold_of_le (OpSpec.charge_mono c) (OpSpec.expectedCharge_le_charge ν c) x post

/-- Under subprobability answers, the expected charge is at most the worst-case charge. -/
theorem wpFold_expectedCharge_le_cost [∀ a, IsSubprobabilityMeasure (ν a)] (x : FreeM P α) :
    wpFold (OpSpec.expectedCharge ν c) x (fun _ => 0) ≤ cost c x :=
  wpFold_expectedCharge_le_costWith ν c x _

end Expected

/-! ## The charge of the completed path -/

section PathCharge

variable (ν : (a : P.A) → Measure (P.B a)) {α : Type v}

/-- Under probability answers, folding the integration spec over a program run with the charge of
its path, read through an additive map `φ` into `ℝ≥0∞`, gives the expected charge `φ ∘ c` of the
program. The charge of a call is paid before the call in the expected-charge reading and on the
completed path in `withPathCharge`, so the two agree because every answer measure has total mass
one. -/
theorem wpFold_lintegral_withPathCharge [∀ a, IsProbabilityMeasure (ν a)] {ω : Type w}
    [AddZeroClass ω] (φ : ω →+ ℝ≥0∞) (c : P.A → ω) (x : FreeM P α) :
    wpFold (OpSpec.lintegral ν) (withPathCharge c x) φ =
      wpFold (OpSpec.expectedCharge ν (φ ∘ c)) x fun _ => 0 := by
  induction x with
  | pure _ => exact map_zero φ
  | lift_bind a cont ih =>
      change wpFold (OpSpec.lintegral ν) (withPathCharge c (FreeM.liftBind a cont)) φ =
        φ (c a) + ∫⁻ b, wpFold (OpSpec.expectedCharge ν (φ ∘ c)) (cont b) (fun _ => 0) ∂ν a
      rw [withPathCharge_liftBind]
      change ∫⁻ b, wpFold (OpSpec.lintegral ν) ((c a + ·) <$> withPathCharge c (cont b)) φ ∂ν a = _
      simp only [wpFold_map, map_add, wpFold_lintegral_const_add, ih]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Expected charge.** Under probability answers over discrete answer types, the expected charge
of a program is the integral of the charge of its completed path under the measure fold of
`withPathCharge c x`. -/
theorem lintegral_measureFold_withPathCharge [∀ a, DiscreteMeasurableSpace (P.B a)]
    [∀ a, IsProbabilityMeasure (ν a)] (c : P.A → ℝ≥0∞) (x : FreeM P α) :
    ∫⁻ s, s ∂measureFold ν (withPathCharge c x) =
      wpFold (OpSpec.expectedCharge ν c) x fun _ => 0 := by
  rw [lintegral_measureFold_eq_wpFold ν _ (post := fun s => s) measurable_id]
  exact wpFold_lintegral_withPathCharge ν (AddMonoidHom.id ℝ≥0∞) c x

/-- The expected number of calls on a completed path is the expected charge of the unit charge. -/
theorem expectedQueryCount_eq_wpFold [P.AnswerMeasure] [∀ a, DiscreteMeasurableSpace (P.B a)]
    (x : FreeM P α) :
    expectedQueryCount x =
      wpFold (OpSpec.expectedCharge AnswerMeasure.toMeasure fun _ => 1) x fun _ => 0 := by
  have h := wpFold_lintegral_withPathCharge AnswerMeasure.toMeasure (Nat.castAddMonoidHom ℝ≥0∞)
    (fun _ => 1) x
  rw [show ((Nat.castAddMonoidHom ℝ≥0∞) ∘ fun _ : P.A => (1 : ℕ)) = fun _ => 1 from
    funext fun _ => Nat.cast_one] at h
  rw [expectedQueryCount, queryCountMeasure, denote, withPathLength_eq_withPathCharge,
    lintegral_measureFold_eq_wpFold _ _ Measurable.of_discrete]
  exact h

end PathCharge

/-! ## Expected-cost transfer -/

section Transfer

variable [∀ a, DiscreteMeasurableSpace (P.B a)] {Q : PFunctor.{uA₂, uB₂}}
  [∀ b, MeasurableSpace (Q.B b)] [∀ b, DiscreteMeasurableSpace (Q.B b)]
  (ν : (b : Q.A) → Measure (Q.B b)) (d : Q.A → ℝ≥0∞) (handler : (a : P.A) → FreeM Q (P.B a))
  {α : Type uB}

/-- **Expected-cost transfer.** If each implementation of a free handler has expected charge at
most `c a`, then the simulated program's expected charge-to-go is at most the source program's
under the charge `c`, with each call answered by the measure fold of its implementation. Discrete
answers on both interfaces make the leaf costs split off each implementation
(`wpFold_expectedCharge_eq_add_lintegral`), which gives the per-call obligation of
`wpFold_liftM_le`. -/
theorem wpFold_expectedCharge_liftM_le (c : P.A → ℝ≥0∞)
    (hcall : ∀ a, wpFold (OpSpec.expectedCharge ν d) (handler a) (fun _ => 0) ≤ c a)
    (x : FreeM P α) (post : α → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge ν d) (x.liftM handler) post ≤
      wpFold (OpSpec.expectedCharge (fun a => measureFold ν (handler a)) c) x post :=
  wpFold_liftM_le handler (OpSpec.expectedCharge_mono _ c)
    (fun a _ => (wpFold_expectedCharge_eq_add_lintegral ν d (handler a)
      Measurable.of_discrete).trans_le (add_le_add_left (hcall a) _)) x post

/-- **Expected-cost transfer, exact form.** The simulated program's expected charge-to-go is the
source program's, with each call charged the expected charge of its implementation and answered by
the measure fold of its implementation. -/
theorem wpFold_expectedCharge_liftM (x : FreeM P α) (post : α → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge ν d) (x.liftM handler) post =
      wpFold (OpSpec.expectedCharge (fun a => measureFold ν (handler a))
        fun a => wpFold (OpSpec.expectedCharge ν d) (handler a) fun _ => 0) x post := by
  rw [wpFold_liftM]
  congr 1
  funext a _
  exact wpFold_expectedCharge_eq_add_lintegral ν d (handler a) Measurable.of_discrete

end Transfer

end FreeM

end PFunctor
