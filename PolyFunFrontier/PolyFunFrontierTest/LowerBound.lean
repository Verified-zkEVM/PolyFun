/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunFrontier.PFunctor.Free.DecisionTree.LowerBound

/-!
# Query lower bounds on a concrete program

`parity₂` asks both bits and returns their exclusive or. It computes the parity of two bits within
total roll bound `2`, and the parity lower bound rules out bound `1`.
-/

@[expose] public section

namespace PolyFunFrontierTest.LowerBound

open PFunctor Cslib Cslib.DecisionTree

/-- Ask both bits and return their exclusive or. -/
def parity₂ : (monomial (Fin 2) Bool).FreeM Bool :=
  (FreeM.lift (P := monomial (Fin 2) Bool) 0).bind fun a =>
    (FreeM.lift (P := monomial (Fin 2) Bool) 1).bind fun b => pure (xor a b)

theorem parity₂_computes (x : Fin 2 → Bool) :
    parity₂.foldFreeM id (fun i k => k (x i)) = parity 2 x := by
  revert x
  decide

example : parity₂.IsTotalRollBound 2 := by
  simp only [parity₂, FreeM.isTotalRollBound_lift_bind_iff, FreeM.isTotalRollBound_pure]
  decide

example : ¬ parity₂.IsTotalRollBound 1 := fun h => by
  have := le_of_isTotalRollBound_parity parity₂_computes h
  omega

end PolyFunFrontierTest.LowerBound
