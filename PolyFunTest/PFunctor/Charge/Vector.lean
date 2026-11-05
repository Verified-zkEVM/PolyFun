/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Handler.CertifiedVec
public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Vector charges

Checks for `PolyFun.PFunctor.Handler.CertifiedVec` on a program that makes two hash calls and one
compression call:

* its use vector over the two resources is `(2, 1)`, and the components of its worst-case vector
  cost are the worst-case costs at the component charges;
* at prices `1` per hash and `5` per compression it costs at most `7`;
* a hash call implemented by two steps and a compression call by three steps are demands
  `(2, 3)`; the program then runs within `2 * 2 + 1 * 3 = 7` steps;
* with each step implemented by four gates, the composite demands give `28` gates.
-/

public section

open PFunctor PFunctor.FreeM PFunctor.Handler

namespace PolyFunTest.ChargeVector

/-- Hash calls (`false`) and compression calls (`true`), each with a Boolean answer. -/
abbrev Ops : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩
/-- Machine steps and gates, each with a Boolean answer. -/
abbrev Step : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩
abbrev Gate : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Each call uses one unit of the resource it names. -/
@[expose] def count (a : Bool) : Bool → ℕ := fun i => if i = a then 1 else 0

/-- The same charge in `ℕ∞`, for worst-case costs. -/
@[expose] def countENat (a : Bool) : Bool → ℕ∞ := fun i => if i = a then 1 else 0

/-- Two hash calls and one compression call. -/
def prog : FreeM Ops Bool :=
  FreeM.liftBind false fun _ => FreeM.liftBind true fun _ => FreeM.liftBind false FreeM.pure

/-- The use vector: two hash calls and one compression call. -/
@[expose] def use : Bool → ℕ := fun i => if i then 1 else 2

theorem prog_isChargeBound : prog.IsChargeBound count use := by
  cost_bound [prog]
  simp only [Pi.le_def, Pi.add_apply, count, use]
  decide

/-! ## Components -/

/-- The hash component of the worst-case vector cost is the worst-case hash count. -/
example : cost countENat prog false = cost (fun a => countENat a false) prog :=
  cost_pi_apply countENat prog false

/-- The worst-case vector cost is at most `(2, 1)`, component by component. -/
example : cost countENat prog ≤ fun i => if i then 1 else 2 := by
  rw [cost_le_pi_iff]
  intro i
  cases i <;> cost_bound [prog, countENat]

/-! ## Prices -/

/-- One unit per hash call and five per compression call. -/
@[expose] def prices : Bool → ℕ := fun i => if i then 5 else 1

/-- At these prices the program costs at most `7`. -/
example : prog.IsChargeBound (fun a => ∑ i, prices i * count a i) 7 := by
  have h := prog_isChargeBound.price prices (fun i => Nat.zero_le _)
  simpa [prices, use] using h

/-! ## Demands -/

/-- A hash call is two steps and a compression call three. -/
@[expose] def stepDemand : Bool → Unit → ℕ := fun i _ => if i then 3 else 2

/-- The implementation of each call by steps. -/
def bySteps : Handler (FreeM Step) Ops := fun a =>
  if a then
    FreeM.liftBind () fun _ => FreeM.liftBind () fun _ => FreeM.liftBind () FreeM.pure
  else
    FreeM.liftBind () fun _ => FreeM.liftBind () FreeM.pure

theorem bySteps_isChargeBound (a : Bool) :
    (bySteps a).IsChargeBound (fun _ _ => 1) (∑ i, count a i • stepDemand i) := by
  cases a <;> cost_bound [bySteps]
  all_goals simp only [Pi.le_def, Pi.add_apply]
  all_goals decide

/-- The program runs within `7` steps. -/
example : (prog.liftM bySteps).IsChargeBound (fun (_ : Unit) (_ : Unit) => 1) fun _ => 7 := by
  have h := isChargeBound_liftM_demand (fun _ _ => Nat.zero_le _)
    bySteps_isChargeBound prog_isChargeBound
  refine h.mono fun j => ?_
  cases j
  decide

/-- Each step is four gates. -/
@[expose] def gateDemand : Unit → Unit → ℕ := fun _ _ => 4

/-- The implementation of each step by gates. -/
def byGates : Handler (FreeM Gate) Step := fun _ =>
  FreeM.liftBind () fun _ => FreeM.liftBind () fun _ => FreeM.liftBind () fun _ =>
    FreeM.liftBind () FreeM.pure

theorem byGates_isChargeBound (b : Unit) :
    (byGates b).IsChargeBound (fun _ _ => 1) (∑ j, (1 : ℕ) • gateDemand j) := by
  cost_bound [byGates]
  all_goals simp only [Pi.le_def, Pi.add_apply, gateDemand]
  all_goals decide

/-- Through both handlers the program runs within `28` gates. -/
example : (prog.liftM (byGates.comp bySteps)).IsChargeBound (fun (_ : Unit) (_ : Unit) => 1)
    fun _ => 28 := by
  have h := isChargeBound_liftM_demand_comp (fun _ _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) bySteps_isChargeBound byGates_isChargeBound prog_isChargeBound
  refine h.mono fun j => ?_
  cases j
  decide

end PolyFunTest.ChargeVector
