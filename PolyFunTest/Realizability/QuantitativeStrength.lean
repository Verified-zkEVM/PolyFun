/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Realizability.QuantitativeBoundedClosure
public import PolyFun.Realizability.Quantitative.Strength

/-!
# Machine-level strength checks

The constant-cost fixture of `PolyFunTest.Realizability.QuantitativeBoundedClosure` charges one
unit for every executable map and gives every encoding size one, so constant envelopes satisfy
every structural cost law.

On it:
- the one-query realization's exact bound transfers to its input-retaining version, with the
  law-derived carry;
- the carry leaves the query count unchanged, and its work is a concrete number;
- the input-retaining machine attaches the carried input to returned values only;
- a strong bind whose second phase reads both the first answer and the original input assembles
  and denotes the resumption bind.
-/

public section

namespace PFunctor.QuantitativeStrengthTest

open DynSystem.DynComputation QuantitativeBoundedClosureTest

instance : unitCostBackend.HasCompositionCost where
  overhead _ := 1
  monotone_overhead := monotone_const
  cost_identity_le _ _ := le_rfl
  composeOverhead_le _ _ _ := Nat.zero_le _

instance : unitCostBackend.HasProdCost where
  sizeOverhead := 0
  size_prod_le _ _ _ _ := by
    change 1 ≤ 1 + 1 + 0
    omega
  overhead _ := 1
  monotone_overhead := monotone_const
  cost_fst_le _ _ _ := le_rfl
  cost_snd_le _ _ _ := le_rfl
  cost_pair_le _ _ _ := by
    change 1 ≤ 1 + 1 + 1
    omega

instance : unitCostBackend.HasSumCost where
  sizeOverhead := 0
  size_inl_le _ _ _ := le_rfl
  size_inr_le _ _ _ := le_rfl
  le_size_inl _ _ _ := le_rfl
  le_size_inr _ _ _ := le_rfl
  overhead _ := 1
  monotone_overhead := monotone_const
  cost_inl_le _ _ _ := le_rfl
  cost_inr_le _ _ _ := le_rfl
  cost_elim_le _ _ z := by
    cases z <;>
      · change 1 ≤ 1 + 1
        omega

instance : unitCostBackend.HasOptionCost where
  sizeOverhead := 0
  size_some_le _ _ := le_rfl
  overhead _ := 1
  monotone_overhead := monotone_const
  cost_some_le _ _ := le_rfl
  cost_bindContext_le _ _ := Nat.le_add_left _ _

instance : unitCostBackend.IsDistributiveCost where
  overhead _ := 1
  monotone_overhead := monotone_const
  cost_distribute_le _ _ _ _ := le_rfl

/-- The law-derived carry of the one-query bound on the constant-cost fixture. -/
abbrev firstQueryCarry (input : PUnit.{1}) : Carry :=
  QuantitativeRealization.lawCarry (Q := unitCostBackend) oneQueryBound
    (unitCostBackend.size firstQueryBoundary.input input)

/-- The one-query realization's exact bound transfers to its input-retaining version. -/
theorem firstQueryWithInputRunsWithin :
    firstQueryRealization.withInput.RunsWithinUnder allowsBool fun input ↦
      oneQueryBound.withCarry oneQueryBound.queries (firstQueryCarry input) :=
  firstQueryRunsWithin.withInput_of_laws

/- Retaining the input adds no query, and the law-derived work is concrete: the source's four
units, two for initialization, two readouts of `11 · 5` and one transition of `17 · 5`. -/
example : (oneQueryBound.withCarry oneQueryBound.queries (firstQueryCarry PUnit.unit)).queries =
    1 := rfl

example : (oneQueryBound.withCarry oneQueryBound.queries (firstQueryCarry PUnit.unit)).work =
    201 := rfl

/- The input-retaining machine exposes the underlying query unchanged and attaches the carried
input only to a returned value. -/
example : firstQueryMachine.withInput.head (none, PUnit.unit) = Sum.inr PUnit.unit := by
  rw [head_withInput]
  rfl

example : firstQueryMachine.withInput.head (some true, PUnit.unit) =
    Sum.inl (true, PUnit.unit) := by
  rw [head_withInput]
  rfl

example : firstQueryRealization.withInput.machine.denote PUnit.unit =
    Resumption.map (fun value ↦ (value, PUnit.unit)) (firstQueryMachine.denote PUnit.unit) :=
  denote_withInput firstQueryMachine PUnit.unit

/-- A second phase that reads both the first phase's answer and the original input. -/
def answerAndInput :
    QuantitativeRealization unitCostBackend (firstQueryBoundary.strongMid natOutputRep) :=
  QuantitativeRealization.ofFn (f := fun x : Bool × PUnit ↦ if x.1 then (1 : Nat) else 0)
    PUnit.unit

example (input : PUnit.{1}) :
    (firstQueryRealization.seqCompWithInput answerAndInput).machine.denote input =
      Resumption.bind (firstQueryMachine.denote input)
        (fun value ↦ answerAndInput.machine.denote (value, input)) :=
  QuantitativeRealization.denote_seqCompWithInput _ _ input

end PFunctor.QuantitativeStrengthTest
