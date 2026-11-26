/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge
public import PolyFun.PFunctor.Resumption.Domain
public import PolyFun.PFunctor.Resumption.Truncate
import PolyFun.PFunctor.Resumption.DomainLaws
import PolyFun.PFunctor.Resumption.DomainTruncate

/-!
# Expected charges of resumptions

A resumption can accumulate charges without returning. Its expected charge is the supremum of the
folds of its finite query prefixes. A cutoff receives zero terminal credit. The step equation
follows by monotone convergence on the joint answer-and-state kernel. It assumes countable answers
with measurable singletons and state-measurable prices and terminal credit. Over other answer spaces
the supremum can lie below the fold of a finite program.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder
open scoped ENNReal

namespace PFunctor.Resumption

universe uA uB uS uR

variable {P : PFunctor.{uA, uB}} {S : Type uS} {α : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
  (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞)

/-- Expected incurred charge plus terminal credit on returned results. -/
@[expose] noncomputable def expectedCharge (tree : Resumption P α) (post : α → S → ℝ≥0∞)
    (s : S) : ℝ≥0∞ :=
  ⨆ n, FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate n tree)
    (fun result => result.elim (fun _ => 0) post) s

theorem expectedCharge_eq_iSup (tree : Resumption P α) (post : α → S → ℝ≥0∞) (s : S) :
    expectedCharge K c tree post s = ⨆ n,
      FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate n tree)
        (fun result => result.elim (fun _ => 0) post) s := rfl

@[simp] theorem expectedCharge_pure (x : α) (post : α → S → ℝ≥0∞) :
    expectedCharge K c (pure x) post = post x := by
  funext s
  simp [expectedCharge_eq_iSup]

/-- Increasing prefix depth increases the expected cost and nonnegative terminal credit. -/
theorem monotone_wpFold_expectedCharge_truncate (tree : Resumption P α) (post : α → S → ℝ≥0∞) :
    Monotone fun n => FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate n tree)
      (fun result => result.elim (fun _ => 0) post) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing tree with
  | zero =>
    rw [truncate_zero, truncate_succ]
    rcases dest tree with x | ⟨a, next⟩
    · rfl
    · exact fun _ => bot_le
  | succ n ih =>
    rw [truncate_succ, truncate_succ (n + 1)]
    rcases dest tree with x | ⟨a, next⟩
    · rfl
    · simp only [FreeM.wpFold_liftBind]
      intro s
      simp only [OpSpec.statefulExpectedCharge_apply]
      exact add_le_add_right (lintegral_mono fun z : P.B a × S => ih (next z.1) z.2) _

/-- A per-operation potential bounds incurred costs through the limit. Unfinished prefixes
carry zero terminal credit, so their nonnegative residual potential may be discarded. -/
theorem expectedCharge_le_of_potential (d : P.A → S → ℝ≥0∞) (I : S → Prop)
    (V : S → ℝ≥0∞) (hV : Measurable V) (hI : ∀ a s, I s → ∀ᵐ z ∂K a s, I z.2)
    (hstep : ∀ a s, I s → d a s + ∫⁻ z, V z.2 ∂K a s ≤ c a s + V s)
    (tree : Resumption P α) (post : α → S → ℝ≥0∞) {s : S} (hs : I s) :
    expectedCharge K d tree (fun r t => post r t + V t) s ≤
      expectedCharge K c tree post s + V s := by
  rw [expectedCharge_eq_iSup]
  apply iSup_le
  intro n
  let f (r : Option α) := r.elim (fun _ : S => (0 : ℝ≥0∞)) post
  refine le_trans ?_ ((FreeM.wpFold_statefulExpectedCharge_le_of_potential K c d I V hV hI
    hstep (truncate n tree) f hs).trans (add_le_add_left ?_ _))
  · apply FreeM.wpFold_mono (OpSpec.statefulExpectedCharge_mono K d) _ _ s
    rintro (_ | r) t
    · exact bot_le
    · rfl
  · exact le_iSup
      (fun m => FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate m tree) f s) n

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- Nonnegative measurable functions of the private state, ordered pointwise. -/
abbrev MeasurableExpectation (S : Type*) [MeasurableSpace S] := {f : S → ℝ≥0∞ // Measurable f}

noncomputable instance MeasurableExpectation.instOmegaCompletePartialOrder :
    OmegaCompletePartialOrder (MeasurableExpectation S) :=
  OmegaCompletePartialOrder.subtype _ fun f hf =>
    Measurable.iSup fun n => hf (f n) ⟨n, rfl⟩

instance MeasurableExpectation.instOrderBot : OrderBot (MeasurableExpectation S) where
  bot := ⟨fun _ => 0, measurable_const⟩
  bot_le _ _ := bot_le

/-- The continuous query algebra for incurred costs and joint state transitions. -/
@[expose] noncomputable def statefulExpectedChargeAlgebra (hc : ∀ a, Measurable (c a)) :
    ContinuousAlgebra P (MeasurableExpectation S) :=
  fun a => .ofFun (fun k => ⟨OpSpec.statefulExpectedCharge K c a (fun b => (k b).1),
    (hc a).add (measurable_from_prod_countable_right fun b => (k b).2).lintegral_kernel⟩) (by
      refine ωScottContinuous.of_monotone_map_ωSup ⟨?_, ?_⟩
      · intro f g h s
        exact add_le_add_right (lintegral_mono fun z : P.B a × S => h z.1 z.2) _
      · intro ch
        apply Subtype.ext
        funext s
        change (c a s + ∫⁻ z, ⨆ n, ((ch n) z.1).1 z.2 ∂K a s) =
          ⨆ n, c a s + ∫⁻ z, ((ch n) z.1).1 z.2 ∂K a s
        rw [lintegral_iSup, ENNReal.add_iSup]
        · exact fun n => measurable_from_prod_countable_right fun b => ((ch n) b).2
        · exact fun i j h z => ch.monotone h z.1 z.2)

@[simp] theorem statefulExpectedChargeAlgebra_apply (hc : ∀ a, Measurable (c a)) (a : P.A)
    (k : P.B a → MeasurableExpectation S) (s : S) :
    (statefulExpectedChargeAlgebra K c hc a k).1 s =
      c a s + ∫⁻ z, (k z.1).1 z.2 ∂K a s := by
  exact OpSpec.statefulExpectedCharge_apply K c a (fun b => (k b).1) s

private theorem foldAlg_eq (hc : ∀ a, Measurable (c a)) {β : Type*}
    (ret : β → MeasurableExpectation S) (x : FreeM P β) :
    (FreeM.foldFreeM ret (fun a => statefulExpectedChargeAlgebra K c hc a) x).1 =
      FreeM.wpFold (OpSpec.statefulExpectedCharge K c) x (fun b => (ret b).1) := by
  induction x with
  | pure x => simp
  | lift_bind a next ih =>
    change (FreeM.foldFreeM ret (fun a => statefulExpectedChargeAlgebra K c hc a)
      (FreeM.liftBind a next)).1 =
      FreeM.wpFold _ (FreeM.liftBind a next) _
    rw [FreeM.foldFreeM_liftBind, FreeM.wpFold_liftBind]
    exact congrArg (OpSpec.statefulExpectedCharge K c a) (funext ih)

/-- Prefix expectations compute the least continuous-algebra interpretation of the tree. -/
theorem expectedCharge_eq_denote (hc : ∀ a, Measurable (c a)) (tree : Resumption P α)
    (post : α → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) :
    expectedCharge K c tree post =
      (denote (fun x => ⟨post x, hpost x⟩) (statefulExpectedChargeAlgebra K c hc) tree).1 := by
  rw [denote_eq_ωSup]
  funext s
  unfold expectedCharge
  congr 1
  funext n
  change _ = (FreeM.foldFreeM (fun r : Option α => r.elim ⊥ (fun x => ⟨post x, hpost x⟩))
    (fun a => statefulExpectedChargeAlgebra K c hc a) (truncate n tree)).1 s
  rw [foldAlg_eq]
  apply congrArg (fun q => FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate n tree) q s)
  funext r
  cases r <;> rfl

/-- The expected cost-to-go from a state is measurable. -/
theorem measurable_expectedCharge (hc : ∀ a, Measurable (c a)) (tree : Resumption P α)
    (post : α → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) :
    Measurable (expectedCharge K c tree post) := by
  rw [expectedCharge_eq_denote K c hc tree post hpost]
  exact Subtype.property _

/-- A request contributes its charge immediately, including when its kernel has zero mass. -/
theorem expectedCharge_query (hc : ∀ a, Measurable (c a)) (a : P.A)
    (next : P.B a → Resumption P α) (post : α → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x))
    (s : S) : expectedCharge K c (query a next) post s =
      c a s + ∫⁻ z, expectedCharge K c (next z.1) post z.2 ∂K a s := by
  simp only [expectedCharge_eq_denote K c hc _ post hpost, denote_query]
  rfl

/-- On a well-founded tree, the finite program's fold gives its entire expected charge. -/
theorem expectedCharge_toResumption (hc : ∀ a, Measurable (c a)) (x : FreeM P α)
    (post : α → S → ℝ≥0∞) (hpost : ∀ y, Measurable (post y)) :
    expectedCharge K c (FreeM.toResumption x) post =
      FreeM.wpFold (OpSpec.statefulExpectedCharge K c) x post := by
  rw [expectedCharge_eq_denote K c hc _ post hpost, denote_toResumption, foldAlg_eq]

/-- Sequencing a resumption substitutes the exact expected cost of its continuation. -/
theorem expectedCharge_bind (hc : ∀ a, Measurable (c a)) {β : Type*} (tree : Resumption P α)
    (next : α → Resumption P β) (post : β → S → ℝ≥0∞) (hpost : ∀ y, Measurable (post y)) :
    expectedCharge K c (bind tree next) post =
      expectedCharge K c tree (fun x => expectedCharge K c (next x) post) := by
  rw [expectedCharge_eq_denote K c hc _ post hpost, denote_bind,
    expectedCharge_eq_denote K c hc _ _
      (fun x => measurable_expectedCharge K c hc (next x) post hpost)]
  congr 2
  funext x
  exact Subtype.ext (expectedCharge_eq_denote K c hc (next x) post hpost).symm

end PFunctor.Resumption
