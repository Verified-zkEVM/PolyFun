/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.ExpectedCharge
public import PolyFun.PFunctor.Free.Measure.Kernel.Handler
public import PolyFun.PFunctor.Handler.Stateful.Link

/-!
# Stateful expected charges

A call incurs its charge in the incoming state and then samples an answer and a successor state
jointly. A fold with measurable terminal postcost splits into the charge incurred by the program
and the integral of the postcost against its result-and-state kernel. The first summand includes
work on branches on which the kernel subsequently loses mass.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uA uB uQ uT uS v

namespace PFunctor

variable {P : PFunctor.{uA, uB}} {S : Type uS} [∀ a, MeasurableSpace (P.B a)]
  [MeasurableSpace S]

/-- Charge a request in its incoming state and integrate the continuation against the joint
answer-and-state kernel. -/
@[expose] noncomputable def OpSpec.statefulExpectedCharge (K : KernelHandler P S)
    (c : P.A → S → ℝ≥0∞) : OpSpec P (S → ℝ≥0∞) :=
  fun a k s => c a s + ∫⁻ z, k z.1 z.2 ∂K a s

@[simp] theorem OpSpec.statefulExpectedCharge_apply (K : KernelHandler P S)
    (c : P.A → S → ℝ≥0∞) (a : P.A) (k : P.B a → S → ℝ≥0∞) (s : S) :
    statefulExpectedCharge K c a k s = c a s + ∫⁻ z, k z.1 z.2 ∂K a s := rfl

/-- The one-call expected charge is monotone in its continuation. -/
theorem OpSpec.statefulExpectedCharge_mono (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) :
    (statefulExpectedCharge K c).Monotone :=
  fun a _ _ hk _ =>
    add_le_add_right (MeasureTheory.lintegral_mono fun z : P.B a × S => hk z.1 z.2) _

namespace FreeM

section Kernel

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) {α : Type v}

/-- Expected charges and continuation costs are measurable in the incoming state when the
charges and each leaf's postcost are measurable there. -/
theorem measurable_wpFold_statefulExpectedCharge (hc : ∀ a, Measurable (c a)) (x : FreeM P α)
    {post : α → S → ℝ≥0∞} (hpost : ∀ r, Measurable (post r)) :
    Measurable (wpFold (OpSpec.statefulExpectedCharge K c) x post) := by
  induction x using FreeM.rec with
  | pure r => exact hpost r
  | liftBind a next ih =>
    exact (hc a).add
      (Measurable.lintegral_kernel (κ := K a) (measurable_from_prod_countable_right ih))

/-- Expected cost-to-go is the sum of incurred expected cost and the value of the terminal
observation under the whole-program kernel. -/
theorem wpFold_statefulExpectedCharge_eq_add_lintegral [MeasurableSpace α]
    (x : FreeM P α) {post : α × S → ℝ≥0∞}
    (hpost : Measurable post) (s : S) :
    wpFold (OpSpec.statefulExpectedCharge K c) x (fun r t => post (r, t)) s =
      wpFold (OpSpec.statefulExpectedCharge K c) x (fun _ _ => 0) s +
        ∫⁻ z, post z ∂runKernel K x s := by
  induction x using FreeM.rec generalizing s with
  | pure r => simp [lintegral_dirac' _ hpost]
  | liftBind a next ih =>
    simp only [wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, runKernel_liftBind,
      Measure.lintegral_bind (measurable_runKernel_continuation K next).aemeasurable
        hpost.aemeasurable, ih]
    rw [lintegral_add_right _ (measurable_from_prod_countable_right fun b =>
      hpost.lintegral_kernel (κ := runKernel K (next b))), add_assoc]

end Kernel

section Potential

variable (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) {α : Type v}

/-- Amortized transfer on reachable states. A local charge may use some of the incoming
potential. The integral accounts for the potential retained upon return, including when the
answer kernel is subprobabilistic. -/
theorem wpFold_statefulExpectedCharge_le_of_potential (d : P.A → S → ℝ≥0∞)
    (I : S → Prop) (V : S → ℝ≥0∞) (hV : Measurable V)
    (hI : ∀ a s, I s → ∀ᵐ z ∂K a s, I z.2)
    (hstep : ∀ a s, I s → d a s + ∫⁻ z, V z.2 ∂K a s ≤ c a s + V s)
    (x : FreeM P α) (post : α → S → ℝ≥0∞) {s : S} (hs : I s) :
    wpFold (OpSpec.statefulExpectedCharge K d) x (fun r t => post r t + V t) s ≤
      wpFold (OpSpec.statefulExpectedCharge K c) x post s + V s := by
  induction x using FreeM.rec generalizing s with
  | pure _ => exact le_rfl
  | liftBind a next ih =>
    simp only [wpFold_liftBind, OpSpec.statefulExpectedCharge_apply]
    refine (add_le_add_right (lintegral_mono_ae <| (hI a s hs).mono
      (fun z hz => ih z.1 hz)) _).trans ?_
    rw [lintegral_add_right _ (show Measurable (fun z : P.B a × S => V z.2) from
      hV.comp measurable_snd)]
    calc
      _ = (d a s + ∫⁻ z, V z.2 ∂K a s) +
          ∫⁻ z, wpFold (OpSpec.statefulExpectedCharge K c) (next z.1) post z.2 ∂K a s := by ac_rfl
      _ ≤ _ := by simpa only [add_assoc, add_comm, add_left_comm] using
        add_le_add_left (hstep a s hs) (∫⁻ z,
          wpFold (OpSpec.statefulExpectedCharge K c) (next z.1) post z.2 ∂K a s)

end Potential

section Transfer

variable {Q : PFunctor.{uQ, uT}} [∀ a, MeasurableSpace (Q.B a)]
  [∀ a, DiscreteMeasurableSpace (Q.B a)]
  {σ : Type uB} [MeasurableSpace σ] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] {α : Type uB}
  (ν : (a : Q.A) → Measure (Q.B a)) (d : Q.A → ℝ≥0∞)
  (h : Handler.Stateful (FreeM Q) σ P)

/-- The exact expected charge of one stateful implementation, including branches on which the
implementation fails to return. -/
@[expose] noncomputable def _root_.PFunctor.Handler.Stateful.expectedCharge
    (handler : Handler.Stateful (FreeM Q) σ P) (ν : (a : Q.A) → Measure (Q.B a))
    (d : Q.A → ℝ≥0∞) (a : P.A) (s : σ) : ℝ≥0∞ :=
  wpFold (OpSpec.expectedCharge ν d) ((handler a).run s) (fun _ => 0)

/-- The joint kernel of a stateful implementation, given measurability of its terminal law
in its incoming state. -/
@[expose] noncomputable def _root_.PFunctor.Handler.Stateful.toKernelHandler
    (handler : Handler.Stateful (FreeM Q) σ P) (ν : (a : Q.A) → Measure (Q.B a))
    (hK : ∀ a, Measurable fun s => measureFold ν ((handler a).run s)) : KernelHandler P σ :=
  fun a => ⟨fun s => measureFold ν ((handler a).run s), hK a⟩

/-- A stateful simulation preserves its joint terminal law, even at infinite expected cost. -/
theorem measureFold_run_eq_runKernel [MeasurableSpace α]
    (hK : ∀ a, Measurable fun s => measureFold ν ((h a).run s)) (x : FreeM P α) (s : σ) :
    measureFold ν (h.run x s) = runKernel (h.toKernelHandler ν hK) x s := by
  induction x using FreeM.rec generalizing s with
  | pure r => simp
  | liftBind a next ih =>
    rw [Handler.Stateful.run_liftBind, runKernel_liftBind]
    change measureFold ν (FreeM.bind _ _) = _
    have hcont : Measurable (fun z : P.B a × σ => measureFold ν (h.run (next z.1) z.2)) := by
      simpa only [ih] using (measurable_runKernel_continuation (h.toKernelHandler ν hK) next)
    rw [measureFold_bind _ _ _ hcont]
    exact Measure.bind_congr_right (.of_forall fun z => ih z.1 z.2)

/-- Exact transfer through a stateful handler. The implementation may choose its target program
from arbitrary private state provided its expected charge and terminal law are measurable there. -/
theorem wpFold_expectedCharge_run (hK : ∀ a, Measurable fun s => measureFold ν ((h a).run s))
    (hc : ∀ a, Measurable (h.expectedCharge ν d a)) (x : FreeM P α) (post : α → σ → ℝ≥0∞)
    (hpost : ∀ r, Measurable (post r)) (s : σ) :
    wpFold (OpSpec.expectedCharge ν d) (h.run x s) (fun z => post z.1 z.2) =
      wpFold (OpSpec.statefulExpectedCharge (h.toKernelHandler ν hK) (h.expectedCharge ν d))
        x post s := by
  induction x using FreeM.rec generalizing s with
  | pure r => simp
  | liftBind a next ih =>
    rw [Handler.Stateful.run_liftBind, wpFold_bind, wpFold_liftBind]
    simp only [ih, OpSpec.statefulExpectedCharge_apply]
    exact wpFold_expectedCharge_eq_add_lintegral ν d ((h a).run s)
      (measurable_from_prod_countable_right fun b =>
        measurable_wpFold_statefulExpectedCharge _ _ hc (next b) (post := post) hpost)

/-- Expected-cost transfer from per-call upper bounds. This pointwise version works on arbitrary
measurable state spaces when the exact cost and the kernel of the implementation are measurable. -/
theorem wpFold_expectedCharge_run_le (hK : ∀ a, Measurable fun s => measureFold ν ((h a).run s))
    (hc : ∀ a, Measurable (h.expectedCharge ν d a)) (c : P.A → σ → ℝ≥0∞)
    (hcall : ∀ a s, h.expectedCharge ν d a s ≤ c a s)
    (x : FreeM P α) (post : α → σ → ℝ≥0∞) (hpost : ∀ r, Measurable (post r)) (s : σ) :
    wpFold (OpSpec.expectedCharge ν d) (h.run x s) (fun z => post z.1 z.2) ≤
      wpFold (OpSpec.statefulExpectedCharge (h.toKernelHandler ν hK) c) x post s := by
  rw [wpFold_expectedCharge_run ν d h hK hc x post hpost s]
  exact wpFold_le_wpFold_of_le (OpSpec.statefulExpectedCharge_mono _ _)
    (fun a _ t => add_le_add_left (hcall a t) _) x post s

/-- Over discrete private state, a pointwise cost bound suffices. Every continuation family is
jointly measurable, so the generic stateful fold inequality applies directly. -/
theorem wpFold_expectedCharge_run_le_of_discrete [DiscreteMeasurableSpace σ]
    (c : P.A → σ → ℝ≥0∞) (hcall : ∀ a s, h.expectedCharge ν d a s ≤ c a s)
    (x : FreeM P α) (post : α → σ → ℝ≥0∞) (s : σ) :
    wpFold (OpSpec.expectedCharge ν d) (h.run x s) (fun z => post z.1 z.2) ≤
      wpFold (OpSpec.statefulExpectedCharge
        (h.toKernelHandler ν (fun _ => Measurable.of_discrete)) c)
        x post s :=
  wpFold_run_liftM_le h (OpSpec.expectedCharge_mono ν d) (fun a k t =>
    (wpFold_expectedCharge_eq_add_lintegral ν d ((h a).run t)
      (post := fun z => k z.1 z.2) (measurable_from_prod_countable_right
        fun _ => Measurable.of_discrete)).trans_le (add_le_add_left (hcall a t) _)) x post s

/-- Running a linked package charges the outer program at the exact cost of each inner
implementation. The inner state threads through the entire run, including repeated calls. -/
theorem wpFold_expectedCharge_run_link {E : PFunctor.{uS, uB}} {T : Type uB}
    (outer : Handler.Stateful (FreeM P) T E)
    (hK : ∀ a, Measurable fun s => measureFold ν ((h a).run s))
    (hc : ∀ a, Measurable (h.expectedCharge ν d a))
    (x : FreeM E α) (post : α → T → σ → ℝ≥0∞) (hpost : ∀ r t, Measurable (post r t))
    (t : T) (s : σ) :
    wpFold (OpSpec.expectedCharge ν d) ((outer.link h).run x (t, s))
        (fun z => post z.1 z.2.1 z.2.2) =
      wpFold (OpSpec.statefulExpectedCharge (h.toKernelHandler ν hK) (h.expectedCharge ν d))
        (outer.run x t) (fun z => post z.1 z.2) s := by
  rw [Handler.Stateful.run_link, wpFold_map]
  exact wpFold_expectedCharge_run ν d h hK hc (outer.run x t) (fun z : α × T => post z.1 z.2)
    (fun z => hpost z.1 z.2) s

end Transfer

section Stateless

variable (ν : (a : P.A) → Measure (P.B a)) (c : P.A → ℝ≥0∞) [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Giving stateless answer measures a unit state recovers the ordinary expected charge. -/
theorem wpFold_statefulExpectedCharge_ofMeasure {α : Type v} (x : FreeM P α) (post : α → ℝ≥0∞)
    (s : PUnit.{uS + 1}) :
    wpFold (OpSpec.statefulExpectedCharge (KernelHandler.ofMeasure ν) (fun a _ => c a))
        x (fun r _ => post r) s =
      wpFold (OpSpec.expectedCharge ν c) x post := by
  induction x using FreeM.rec generalizing s with
  | pure _ => rfl
  | liftBind a next ih =>
    simp only [wpFold_liftBind, OpSpec.expectedCharge_apply,
      OpSpec.statefulExpectedCharge_apply, ih]
    congr 1
    change ∫⁻ z, wpFold (OpSpec.expectedCharge ν c) (next z.1) post
        ∂(ν a).map (fun b => (b, PUnit.unit)) = _
    exact lintegral_map (show Measurable (fun z : P.B a × PUnit.{uS + 1} =>
      wpFold (OpSpec.expectedCharge ν c) (next z.1) post) from
        (Measurable.of_discrete
          (f := fun b => wpFold (OpSpec.expectedCharge ν c) (next b) post)).comp
          measurable_fst) (measurable_id.prodMk measurable_const)

end Stateless

end FreeM
end PFunctor
