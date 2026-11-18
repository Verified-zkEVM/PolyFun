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
Even infinite terminal credit has no effect on this client because it never returns.
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
example (post : Unit → Bool → ℝ≥0∞) :
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

end PolyFunTest.Probability.ResumptionCharge
