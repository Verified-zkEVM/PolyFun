/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.PPoly
public import PolyFun.Realizability.Quantitative.Resource

/-!
# From P/poly certificates to per-parameter program witnesses

A `PPoly.Witness` is nonuniform in the security parameter: one machine per `n`, with
polynomially bounded state count, rounds and time. PolyFun's generic `PolynomialProgramWitness`
is uniform in the input: one realization whose resources are bounded by second-order polynomials
in the encoded input size. This module shows that the first yields the second at every parameter,
with the *constant* resource polynomial `runBoundCost` (total time, rounds, rounds times the
per-step traffic, the state-length bound, and the head-width bound), the total-answer contract
(every admitted response model allows every typed reply, with the index width as the response
modulus), and tag-bit output recovery.

So a P/poly certificate is "a generic witness at each `n` with polynomial-in-`n` constants, plus an
advice bound": the uniformity in `n` that the family adds is exactly that those constants are
polynomials. The one extra hypothesis is that every position admits an answer, which
`TraceProgressUnder` needs against the total contract.
-/

public section

open PFunctor PFunctor.DynSystem.DynComputation

namespace ComplexityBackends.CslibSingleTape.PPoly

variable {p : ℕ → PFunctor.{0, 0}} {input output : ℕ → Type}
  {bd : Boundary p input output}

/-! ## Pointwise size bounds at one parameter -/

/-- Encoded positions are bounded by the position width bound. -/
theorem size_pos_le (n : ℕ) (position : (p n).A) :
    Backend.quantitative.size (bd.toGeneric n).pos position ≤ bd.position.widBound.eval n := by
  rw [Boundary.toGeneric_pos, Backend.size_eq_length, bd.position.len_eq]
  exact bd.position.wid_le n

/-- Encoded indices are bounded by the index width bound. -/
theorem size_idx_le (n : ℕ) (index : (p n).Idx) :
    Backend.quantitative.size (bd.toGeneric n).idx index ≤ bd.index.widBound.eval n := by
  rw [Boundary.toGeneric_idx, Backend.size_eq_length, bd.index.len_eq]
  exact bd.index.wid_le n

/-- Encoded readouts are bounded by one tag bit plus the larger of the output and position
width bounds. -/
theorem size_head_le (n : ℕ) (value : output n ⊕ (p n).A) :
    Backend.quantitative.size (bd.toGeneric n).head value ≤
      1 + (bd.output.widBound.eval n + bd.position.widBound.eval n) := by
  cases value with
  | inl v =>
      simp only [DynSystem.DynComputation.Boundary.head, Backend.sum_inl,
        Boundary.toGeneric_out, List.length_cons, bd.output.len_eq]
      have := bd.output.wid_le n
      omega
  | inr q =>
      simp only [DynSystem.DynComputation.Boundary.head, Backend.sum_inr,
        Boundary.toGeneric_pos, List.length_cons, bd.position.len_eq]
      have := bd.position.wid_le n
      omega

variable [∀ n, DecidableEq (p n).A]

/-- Encoded hidden states are bounded by the state-length bound. -/
theorem size_state_le (R : Realization bd) (n : ℕ) (state : (R.machine n).State) :
    Backend.quantitative.size (R.toQuantitative n).state state ≤ R.state.bound.eval n := by
  rw [Realization.toQuantitative_state, Backend.size_eq_length]
  exact R.state.len_le n state

/-! ## The per-parameter generic witness -/

/-- Returned payload size from the tagged readout size: the tag costs one bit. -/
noncomputable def outputRecovery (n : ℕ) :
    Backend.quantitative.PolyOutputSizeRecovery (bd.toGeneric n) where
  polynomial := Complexity.FirstOrderPolynomial.input
  output_le value := by
    simp only [Complexity.FirstOrderPolynomial.eval_input, DynSystem.DynComputation.Boundary.head,
      Backend.sum_inl, Boundary.toGeneric_out, List.length_cons]
    omega

/-- The total-answer contract: admitted response models allow every typed reply, with the index
width bound as the constant response-size envelope. -/
noncomputable def totalContract (n : ℕ) :
    ResponseResourceContract Backend.quantitative (bd.toGeneric n).interface PUnit where
  labelOf _ := PUnit.unit
  admissible model := ∀ position answer, model.allows position answer
  model_nonempty :=
    ⟨{ allows := fun _ _ ↦ True
       responseSize := fun _ _ ↦ bd.index.widBound.eval n
       responseSize_monotone := fun _ ↦ monotone_const
       responseSize_le := fun position answer _ ↦ by
         simpa using size_idx_le (bd := bd) n ⟨position, answer⟩ },
      fun _ _ ↦ trivial⟩

/-- The constant resource bound at parameter `n` read off a P/poly realization: total time,
rounds, rounds times the per-step traffic, the state-length bound, and the head-width bound. -/
@[expose] noncomputable def runBoundCost (R : Realization bd) (n : ℕ) : ExecutionCost where
  work := R.totalTime.eval n
  queries := R.rounds.eval n
  traffic := R.rounds.eval n * (bd.position.widBound.eval n + bd.index.widBound.eval n)
  peakStateSize := R.state.bound.eval n
  peakHeadSize := 1 + (bd.output.widBound.eval n + bd.position.widBound.eval n)

variable {program : (n : ℕ) → input n → FreeM (p n) (output n)}

/-- Every execution prefix of a certified program stays within the constant bound. -/
theorem executionCost_le (witness : Witness bd program) (n : ℕ) (value : input n)
    {finish : (witness.realization.toQuantitative n).machine.State}
    (trace : (witness.realization.toQuantitative n).ExecutionTrace
      ((witness.realization.toQuantitative n).machine.init value) finish) :
    (witness.realization.toQuantitative n).executionCost value trace ≤
      runBoundCost witness.realization n := by
  have hlen := trace.length_le_of_resolvesIn (witness.resolvesIn n value)
  have hwork := witness.executionWork_le_totalTime n value trace
  have htraffic := trace.traffic_cost_le _ _ (size_pos_le (bd := bd) n) (size_idx_le (bd := bd) n)
  have hstate := trace.peakStateSize_cost_le _ (size_state_le witness.realization n)
  have hhead := trace.peakHeadSize_cost_le _ (fun state ↦ size_head_le (bd := bd) n _)
  have hfinishState : ((witness.realization.toQuantitative n).state finish).length ≤
      witness.realization.state.bound.eval n :=
    size_state_le witness.realization n finish
  have hfinishHead : ((bd.toGeneric n).head
      ((witness.realization.toQuantitative n).machine.head finish)).length ≤
      1 + (bd.output.widBound.eval n + bd.position.widBound.eval n) :=
    size_head_le (bd := bd) n _
  have hq : trace.cost.queries = trace.length :=
    QuantitativeRealization.ExecutionTrace.queries_cost trace
  refine ⟨hwork, ?_, ?_, ?_, ?_⟩
  · simp only [QuantitativeRealization.executionCost, ExecutionCost.queries_add,
      ExecutionCost.queries_ofWork, ExecutionCost.queries_observe, runBoundCost]
    omega
  · simp only [QuantitativeRealization.executionCost, ExecutionCost.traffic_add,
      ExecutionCost.traffic_ofWork, ExecutionCost.traffic_observe, runBoundCost]
    have := Nat.mul_le_mul_right
      (bd.position.widBound.eval n + bd.index.widBound.eval n) hlen
    omega
  · have h0 : ∀ w, (ExecutionCost.ofWork w).peakStateSize = 0 := fun _ ↦ rfl
    simp only [QuantitativeRealization.executionCost, ExecutionCost.peakStateSize_add,
      ExecutionCost.peakStateSize_observe, h0, runBoundCost]
    omega
  · have h0 : ∀ w, (ExecutionCost.ofWork w).peakHeadSize = 0 := fun _ ↦ rfl
    simp only [QuantitativeRealization.executionCost, ExecutionCost.peakHeadSize_add,
      ExecutionCost.peakHeadSize_observe, h0, runBoundCost]
    omega

/-- **A P/poly certificate is a generic program witness at every parameter.** The resource
polynomial is the constant `runBoundCost`; the contract is the total-answer contract; output
recovery is the tag bit. The hypothesis that every position admits an answer is what
`TraceProgressUnder` needs against the total contract. -/
@[expose]
noncomputable def Witness.toPolynomialProgramWitness [∀ n position, Nonempty ((p n).B position)]
    (witness : Witness bd program) (n : ℕ) :
    PolynomialProgramWitness Backend.quantitative (bd.toGeneric n) (totalContract n)
      (program n) where
  realization := witness.realization.toQuantitative n
  implements :=
    ((implementsWithin_iff_implements_and_bound (witness.realization.machine n) (program n)
      (witness.realization.rounds.eval n)).mp (witness.implements.apply n)).1
  outputRecovery := outputRecovery n
  runBound :=
    { polynomial := ExecutionCostPolynomial.const (runBoundCost witness.realization n)
      runsWithin := fun model ↦ by
        refine ⟨?_, ?_, ?_⟩
        · intro value finish trace _
          simp only [ExecutionCostPolynomial.eval_const]
          exact executionCost_le witness n value trace
        · intro value
          simp only [ExecutionCostPolynomial.eval_const]
          exact resolvesInUnder_of_resolvesIn _ _ _ _ (witness.resolvesIn n value)
        · intro value state trace _ position next _
          exact ⟨Classical.choice inferInstance, model.2 position _⟩ }

/-- The bridge keeps the certificate's realization at the chosen parameter. -/
@[simp] theorem Witness.toPolynomialProgramWitness_realization
    [∀ n position, Nonempty ((p n).B position)] (witness : Witness bd program) (n : ℕ) :
    (witness.toPolynomialProgramWitness n).realization = witness.realization.toQuantitative n :=
  rfl

/-- The bridge's second-order polynomial is the constant `runBoundCost`. -/
@[simp] theorem Witness.toPolynomialProgramWitness_polynomial
    [∀ n position, Nonempty ((p n).B position)] (witness : Witness bd program) (n : ℕ) :
    (witness.toPolynomialProgramWitness n).runBound.polynomial =
      ExecutionCostPolynomial.const (runBoundCost witness.realization n) :=
  rfl

end ComplexityBackends.CslibSingleTape.PPoly
