/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.ExpectedCharge

/-!
# Incurred charges on an infinite sequence of requests

The same deterministic client can pay a finite setup cost or an infinite per-request bill.
Even infinite terminal credit has no effect on this client because it never returns. A potential
bounds the setup cost of every client. An adaptive client pays for its second request in the state
left by its first.

Agreement with the fold of a finite program needs answers with measurable singletons. Over a
coarser answer space, a client that always returns can lose its whole terminal payoff.
-/

public section

open PFunctor PFunctor.Resumption MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Probability.ResumptionCharge

/-- The interface of the repeated unit request. -/
abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

private noncomputable def ticks : Resumption Tick Unit :=
  Resumption.corec (fun _ : Unit => .inr ⟨(), fun _ => ()⟩) ()

private theorem ticks_unfold : ticks = query () (fun _ => ticks) := by
  apply Resumption.eq_of_dest_eq
  rw [dest_query]
  simp [ticks, PFunctor.map]
  rfl

private noncomputable def service : KernelHandler Tick Bool :=
  KernelHandler.ofFun (fun _ _ => ((), true)) (fun _ => measurable_const)

private noncomputable def setup (_ : Tick.A) (ready : Bool) : ℝ≥0∞ :=
  if ready then 0 else 1

private noncomputable def prefixCost (price : Tick.A → Bool → ℝ≥0∞)
    (post : Unit → Bool → ℝ≥0∞) (n : ℕ) (s : Bool) : ℝ≥0∞ :=
  FreeM.wpFold (OpSpec.statefulExpectedCharge service price) (truncate n ticks)
    (fun result => result.elim (fun _ => 0) post) s

private theorem prefix_zero (price : Tick.A → Bool → ℝ≥0∞) (post : Unit → Bool → ℝ≥0∞)
    (s : Bool) : prefixCost price post 0 s = 0 := by
  rw [prefixCost, ticks_unfold, truncate_query_zero]
  rfl

private theorem prefix_succ (price : Tick.A → Bool → ℝ≥0∞) (post : Unit → Bool → ℝ≥0∞)
    (n : ℕ) (s : Bool) :
    prefixCost price post (n + 1) s = price () s + prefixCost price post n true := by
  unfold prefixCost
  conv_lhs => rw [ticks_unfold, truncate_query_succ, FreeM.wpFold_liftBind,
    OpSpec.statefulExpectedCharge_apply (P := Tick) service price]
  simp [service, KernelHandler.ofFun, Kernel.deterministic_apply]

private theorem ready_prefix (post : Unit → Bool → ℝ≥0∞) (n : ℕ) :
    prefixCost setup post n true = 0 := by
  induction n with
  | zero => exact prefix_zero ..
  | succ n ih => simp [prefix_succ, setup, ih]

/-- The first request costs one, subsequent requests are free, and no cutoff earns credit. -/
private theorem expectedCharge_setup_ticks (post : Unit → Bool → ℝ≥0∞) :
    expectedCharge service setup ticks post false = 1 := by
  change (⨆ n, prefixCost setup post n false) = 1
  have h (n : ℕ) : prefixCost setup post (n + 1) false = 1 := by
    simp [prefix_succ, ready_prefix, setup]
  apply le_antisymm
  · apply iSup_le
    rintro (_ | n)
    · simp [prefix_zero]
    · exact (h n).le
  · exact le_iSup_of_le 1 (h 0).ge

/-- At one per request the finite prefixes cost exactly their depth, so the total is infinite. -/
example (post : Unit → Bool → ℝ≥0∞) (s : Bool) :
    expectedCharge service (fun _ _ => 1) ticks post s = ⊤ := by
  change (⨆ n, prefixCost (fun _ _ => 1) post n s) = ⊤
  have h (n : ℕ) (t : Bool) : prefixCost (fun _ _ => 1) post n t = n := by
    induction n generalizing t with
    | zero => simp [prefix_zero]
    | succ n ih => simp [prefix_succ, ih, Nat.cast_succ, add_comm]
  simp [h, ENNReal.iSup_natCast]

/-- A zero-mass request incurs its charge even when terminal credit is infinite. -/
example (next : Unit → Resumption Tick Unit) :
    expectedCharge (P := Tick) (fun _ => 0) (fun _ (_ : Unit) => 7)
      (query () next) (fun _ _ => ⊤) () = 7 := by
  rw [expectedCharge_query (P := Tick) (S := Unit) _ _ (fun _ => measurable_const) _ _ _
    (fun _ => measurable_const)]
  simp

/-- A finite program still receives its terminal credit at the state where it returns. -/
example (program : FreeM Tick Unit) (post : Unit → Bool → ℝ≥0∞) :
    expectedCharge service setup program.toResumption post =
      FreeM.wpFold (OpSpec.statefulExpectedCharge service setup) program post :=
  expectedCharge_toResumption service setup (fun _ => Measurable.of_discrete) program post
    (fun _ => Measurable.of_discrete)

/-! ## Potential bounds -/

/-- The setup charge that remains to be paid. -/
private noncomputable def credit (ready : Bool) : ℝ≥0∞ := if ready then 0 else 1

/-- The potential pays for the setup of any client. A return before setup keeps the credit. -/
example (tree : Resumption Tick Unit) (post : Unit → Bool → ℝ≥0∞) (s : Bool) :
    expectedCharge service setup tree (fun r t => post r t + credit t) s ≤
      expectedCharge service (fun _ _ => 0) tree post s + credit s := by
  refine expectedCharge_le_of_potential service (fun _ _ => 0) setup (fun _ => True) credit
    Measurable.of_discrete (fun _ _ _ => .of_forall fun _ => trivial) ?_ tree post trivial
  rintro ⟨⟩ (_ | _) _ <;>
    simp [service, setup, credit, KernelHandler.ofFun, Kernel.deterministic_apply]

/-- The client that never returns attains this bound from the state before setup. -/
example (post : Unit → Bool → ℝ≥0∞) :
    expectedCharge service setup ticks (fun r t => post r t + credit t) false =
      expectedCharge service (fun _ _ => 0) ticks post false + credit false := by
  have h (n : ℕ) (t : Bool) : prefixCost (fun _ _ => 0) post n t = 0 := by
    induction n generalizing t with
    | zero => exact prefix_zero ..
    | succ n ih => simp [prefix_succ, ih]
  rw [expectedCharge_setup_ticks]
  change 1 = (⨆ n, prefixCost (fun _ _ => 0) post n false) + credit false
  simp [h, credit]

/-- Without credit, the price premise fails in the state before setup. -/
example : ¬ setup () false ≤ 0 := by simp [setup]

/-- Setup is free in the ready state, which the service never leaves. -/
example (tree : Resumption Tick Unit) :
    expectedCharge service setup tree (fun _ _ => 0) true ≤
      expectedCharge service (fun _ _ => 0) tree (fun _ _ => 0) true := by
  have h := expectedCharge_le_of_potential service (fun _ _ => 0) setup (fun ready => ready = true)
    (fun _ => 0) measurable_const ?_ ?_ tree (fun _ _ => 0) (s := true) rfl
  · simpa using h
  · rintro ⟨⟩ s _
    simp [service, KernelHandler.ofFun, Kernel.deterministic_apply]
  · rintro ⟨⟩ s rfl
    simp [setup]

/-! ## Sequencing -/

/-- A request answered by a Boolean. -/
abbrev Ask : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

private noncomputable def toggle : KernelHandler Ask Bool :=
  KernelHandler.ofFun (fun _ s => (s, !s)) (fun _ => Measurable.of_discrete)

private noncomputable def price (_ : Ask.A) (s : Bool) : ℝ≥0∞ := if s then 3 else 2

private noncomputable def ask : Resumption Ask Bool := Resumption.lift (p := Ask) ()

private noncomputable def askTwice : Resumption Ask Bool :=
  Resumption.bind ask fun b => if b then .pure b else ask

private theorem expectedCharge_ask (post : Bool → Bool → ℝ≥0∞) (s : Bool) :
    expectedCharge toggle price ask post s = price () s + post s (!s) := by
  rw [ask, Resumption.lift, expectedCharge_query (P := Ask) _ _ (fun _ => Measurable.of_discrete)
    _ _ _ (fun _ => Measurable.of_discrete)]
  simp [toggle, KernelHandler.ofFun, Kernel.deterministic_apply]

/-- The second request is priced in the state that the first one leaves. -/
example (post : Bool → Bool → ℝ≥0∞) :
    expectedCharge toggle price askTwice post false = 2 + (3 + post true false) := by
  rw [askTwice, expectedCharge_bind (P := Ask) toggle price (fun _ => Measurable.of_discrete)
    _ _ _ (fun _ => Measurable.of_discrete), expectedCharge_ask]
  simp [expectedCharge_ask, price]

/-- A `true` answer returns without a second request. -/
example (post : Bool → Bool → ℝ≥0∞) :
    expectedCharge toggle price askTwice post true = 3 + post true false := by
  rw [askTwice, expectedCharge_bind (P := Ask) toggle price (fun _ => Measurable.of_discrete)
    _ _ _ (fun _ => Measurable.of_discrete), expectedCharge_ask]
  simp [price]

/-! ## Answers without measurable singletons -/

/-- A natural number whose measurable structure does not distinguish its values. -/
structure CoarseNat where
  /-- The underlying value, which the measurable structure does not expose. -/
  down : ℕ

instance : MeasurableSpace CoarseNat := ⊥

/-- Measurable functions of a coarse number are constant, so one zero of `f` makes its integral
vanish. -/
private theorem lintegral_coarse_eq_zero (μ : Measure (CoarseNat × Unit))
    {f : CoarseNat × Unit → ℝ≥0∞} {z : CoarseNat × Unit} (hz : f z = 0) : ∫⁻ w, f w ∂μ = 0 := by
  obtain ⟨g, hg, hgf, heq⟩ := exists_measurable_le_lintegral_eq μ f
  have hgz : g z = 0 := le_antisymm ((hgf z).trans hz.le) bot_le
  have hconst (w : CoarseNat × Unit) : g w = 0 := by
    have hm : Measurable fun n => g (n, ()) := hg.comp measurable_prodMk_right
    rcases MeasurableSpace.measurableSet_bot_iff.mp (hm (measurableSet_singleton 0)) with h | h
    · exact absurd hgz (Set.eq_empty_iff_forall_notMem.mp h z.1)
    · exact Set.eq_univ_iff_forall.mp h w.1
  simp [heq, hconst]

/-- One operation with coarse natural-number answers. -/
abbrev Pick : PFunctor.{0, 0} := ⟨Unit, fun _ => CoarseNat⟩

private noncomputable def zeroes : KernelHandler Pick Unit :=
  KernelHandler.ofFun (fun _ _ => (⟨0⟩, ())) (fun _ => measurable_const)

private noncomputable abbrev free : OpSpec Pick (Unit → ℝ≥0∞) :=
  OpSpec.statefulExpectedCharge (P := Pick) zeroes (fun _ _ => 0)

private theorem free_const (x : ℝ≥0∞) (s : Unit) : free () (fun _ _ => x) s = x := by
  simp [free, zeroes, KernelHandler.ofFun, Kernel.deterministic_apply]

/-- Make `n` requests and return. -/
private def wait : ℕ → FreeM Pick Unit
  | 0 => .pure ()
  | n + 1 => .liftBind () fun _ => wait n

/-- The first answer chooses the number of further requests. -/
private def pickThenWait : FreeM Pick Unit := .liftBind () fun n => wait n.down

private theorem wpFold_wait (n : ℕ) (s : Unit) :
    FreeM.wpFold free (wait n) (fun _ _ => 1) s = 1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [wait, FreeM.wpFold_liftBind, funext ih, free_const]

private theorem wpFold_truncate_wait (n : ℕ) (s : Unit) :
    FreeM.wpFold free (truncate n (wait (n + 1)).toResumption)
      (fun result => result.elim (fun _ => 0) fun _ _ => 1) s = 0 := by
  induction n generalizing s with
  | zero => rw [wait, FreeM.toResumption_liftBind, truncate_query_zero]; rfl
  | succ n ih =>
    rw [wait, FreeM.toResumption_liftBind, truncate_query_succ, FreeM.wpFold_liftBind, funext ih]
    exact free_const 0 s

/-- Every branch of the finite program returns, so its fold gives the whole terminal payoff. -/
example : FreeM.wpFold free pickThenWait (fun _ _ => 1) () = 1 := by
  simp only [pickThenWait, FreeM.wpFold_liftBind, funext (wpFold_wait _), free_const]

/-- No truncation depth bounds every branch, and each truncation integrates to zero. The measure
puts all its mass at the immediate return, but the coarse answers do not distinguish that branch
from the ones that are cut off. -/
example : expectedCharge zeroes (fun _ _ => 0) pickThenWait.toResumption (fun _ _ => 1) () = 0 := by
  rw [expectedCharge_eq_iSup (P := Pick), ENNReal.iSup_eq_zero]
  rintro (_ | n)
  · rw [pickThenWait, FreeM.toResumption_liftBind, truncate_query_zero]; rfl
  · rw [pickThenWait, FreeM.toResumption_liftBind, truncate_query_succ, FreeM.wpFold_liftBind,
      OpSpec.statefulExpectedCharge_apply (P := Pick) zeroes, zero_add]
    exact lintegral_coarse_eq_zero _ (z := (⟨n + 1⟩, ())) (wpFold_truncate_wait n ())

end PolyFunTest.Probability.ResumptionCharge
