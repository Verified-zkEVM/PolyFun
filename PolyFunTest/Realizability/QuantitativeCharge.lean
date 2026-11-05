/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Charge
public import PolyFun.Realizability.Quantitative.Reference
public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Interface charges on quantitative realizations

Checks for `PolyFun.Realizability.Quantitative.Charge` on the machine of a two-call program,
realized with no backend cost:

* every execution prefix from the initial state charges at most the program's budget;
* the unit charge counts the calls, and counting the calls to one interface is its indicator
  charge;
* a run bound gives a charge bound on the program through the scaling map `n ↦ n • K`.
-/

public section

namespace PolyFunTest.QuantitativeCharge

open PFunctor PFunctor.FreeM PFunctor.DynSystem.DynComputation QuantitativeRealization

/-- Coin flips, each with a Boolean answer. -/
abbrev Coin : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- Two flips, returning the second. -/
def flipTwice : FreeM Coin Bool := do
  let _ ← FreeM.lift (P := Coin) PUnit.unit
  FreeM.lift (P := Coin) PUnit.unit

/-- The machine of `flipTwice`, realized under the cost-free reference backend. -/
def flipRealization : QuantitativeRealization QuantitativeStepClass.Reference.zero
    (Boundary.unconstrained Coin PUnit Bool) where
  machine := ofFreeM fun _ => flipTwice
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit

variable {finish : flipRealization.machine.State}
  (trace : ExecutionTrace flipRealization (flipRealization.machine.init PUnit.unit) finish)

/-- At price `3` per call, every execution prefix charges at most `6`. -/
example : trace.charge (fun _ => (3 : ℕ)) ≤ 6 := by
  have h := trace.charge_le_of_isChargeBound (c := fun _ => (3 : ℕ)) (B := 6) (s := 0)
    ((Implements.isChargeBound_init_iff (implements_ofFreeM _) PUnit.unit).2
      (by cost_bound [flipTwice]))
  simpa using h

example : trace.length = trace.charge (fun _ => 1) :=
  trace.length_eq_charge_one

example : trace.queryCount id PUnit.unit = trace.charge fun a => if a = PUnit.unit then 1 else 0 :=
  trace.queryCount_eq_charge id PUnit.unit

/-- A run bound scales to a charge bound on the program. -/
example {bound : PUnit → ExecutionCost} (h : flipRealization.RunsWithin bound) :
    flipTwice.IsChargeBound (fun _ => (3 : ℕ)) ((bound PUnit.unit).queries • 3) :=
  h.isChargeBound (implements_ofFreeM _) (fun _ => le_rfl) PUnit.unit

/-- The scaling map is `n ↦ n • K`. -/
example (n : ℕ) : OrderAddMonoidHom.multiples (3 : ℕ) (Nat.zero_le 3) n = n * 3 := by
  simp

end PolyFunTest.QuantitativeCharge
