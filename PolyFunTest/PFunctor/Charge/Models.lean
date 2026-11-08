/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic
public import PolyFun.ITree.Charge
public import PolyFun.IPFunctor.Free.Bound.Charge
public import PolyFun.Interaction.Basic.TypeTree
public import PolyFun.Realizability.Quantitative

/-!
# Charges across models of computation

Checks that one notion of charge bound covers the models PolyFun connects to free programs:

* a protocol shape (`TypeTree`) is a free program over move types, so a unit charge counts its
  rounds;
* a machine built from a free program has the bound of the program, and implements it within a
  charge;
* a resumption embedding a free program has the program's bound, and indexed programs have a
  worst-case cost that unfolds call by call;
* free silent steps of an interaction tree do not change its bound, and charged ones spend;
* resource records (`ExecutionCost`) serve as a cost type.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeModels

/-- Two rounds: a bit, then one of three messages. -/
def twoRounds : Interaction.TypeTree.{0} :=
  .node Bool fun _ => .node (Fin 3) fun _ => .done

example : twoRounds.IsChargeBound (fun _ => (1 : ℕ)) 2 := by
  cost_bound [twoRounds]

example : ¬ twoRounds.IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  cost_bound [twoRounds]

abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

def flipTwice : FreeM Coin Bool := do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

/-- The machine of a free program has the bound of the program. -/
example : (DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).IsChargeBound
    (fun _ => (1 : ℕ)) 2 ((DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).init ()) :=
  (DynSystem.DynComputation.isChargeBound_ofFreeM_iff _ ()).2 (by cost_bound [flipTwice])

/-- Bounded implementation with a charge in place of a call count, and the bound it gives on the
machine from every initial state. -/
example : (DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).ImplementsWithinCharge
    (fun _ : Unit => flipTwice) (fun _ => (3 : ℕ)) 6 :=
  ⟨DynSystem.DynComputation.implements_ofFreeM _, fun _ => by cost_bound [flipTwice]⟩

example (h : (DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).ImplementsWithinCharge
    (fun _ : Unit => flipTwice) (fun _ => (3 : ℕ)) 6) :
    (DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).IsChargeBound (fun _ => 3) 6
      ((DynSystem.DynComputation.ofFreeM fun _ : Unit => flipTwice).init ()) :=
  h.isChargeBound ()

/-- The embedding of a free program into resumptions keeps its bound, and a larger budget keeps
any resumption bound. -/
example : (FreeM.toResumption flipTwice).IsChargeBound (fun _ => (1 : ℕ)) 2 :=
  (Resumption.isChargeBound_toResumption_iff flipTwice).2 (by cost_bound [flipTwice])

example : ¬ (FreeM.toResumption flipTwice).IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  rw [Resumption.isChargeBound_toResumption_iff]
  cost_bound [flipTwice]

example (r : Resumption Coin Bool) (h : r.IsChargeBound (fun _ => (1 : ℕ)) 2) :
    r.IsChargeBound (fun _ => (1 : ℕ)) 3 :=
  h.mono (by decide)

/-- A worst-case cost on indexed programs unfolds one call at a time. -/
example {I : Type} {P : IPFunctor.Endo I} {X : I → Type} {s : I} (c : (s : I) → P.A s → ℕ∞)
    (a : P.A s) (r : (b : P.B s a) → IPFunctor.IFreeM P X (P.src s a b)) :
    IPFunctor.IFreeM.cost c (IPFunctor.IFreeM.liftBind a r) = c s a + ⨆ b, (r b).cost c :=
  IPFunctor.IFreeM.cost_liftBind c a r

/-- A silent step before a visible call is free. -/
example (k : Bool → ITree Coin Bool) (n : ℕ) :
    (ITree.step (ITree.query (F := Coin) () k)).IsChargeBound (fun _ => (1 : ℕ)) n ↔
      (ITree.query (F := Coin) () k).IsChargeBound (fun _ => (1 : ℕ)) n :=
  ITree.isChargeBound_step_iff _

/-- A silent step charged `1` spends one unit before the call. -/
example (k : Bool → ITree Coin Bool) (n s : ℕ) :
    (ITree.step (ITree.query (F := Coin) () k)).IsChargeBound (fun _ => (1 : ℕ)) n s 1 ↔
      s + 1 ≤ n ∧ (ITree.query (F := Coin) () k).IsChargeBound (fun _ => (1 : ℕ)) n (s + 1) 1 :=
  ITree.isChargeBound_step_iff_add _

/-- Resource records as costs: each call is one query with three units of traffic. -/
example : flipTwice.IsChargeBound (fun _ => ExecutionCost.query 2 1) ⟨0, 2, 6, 0, 0⟩ := by
  simp only [flipTwice, isChargeBound_bind_iff', wpFold_lift, OpSpec.budget_apply,
    isChargeBound_lift_iff]
  exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    fun _ => ⟨by decide, by decide, by decide, by decide, by decide⟩⟩

end PolyFunTest.ChargeModels
