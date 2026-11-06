/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunComplexitylib.Query.Protocol
public import PolyFunComplexitylib.Stateful.Responder

/-!
# Decision trees, protocols and stateful clients as free programs

Concrete round trips through the bridges, and the specialization of PolyFun's general query
complexity bound to Boolean decision trees.
-/

@[expose] public section

open Cslib PFunctor

/-- Query `0`, then `1` on a `true` answer. -/
def tree : DecisionTree (Fin 2) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

example : DecisionTree.equivFreeM.symm (DecisionTree.equivFreeM tree) = tree :=
  DecisionTree.equivFreeM.symm_apply_apply tree

example : tree.eval (fun _ => true) = true := rfl

example : tree.toFreeM.IsTotalRollBound 2 :=
  (DecisionTree.depth_le_iff_isTotalRollBound tree 2).mp (by decide)

/-- The general bound over any finite polynomial interface gives the decision tree bound. -/
example (f : (Fin 3 → Bool) → Bool) : DecisionTree.complexity f ≤ 3 := by
  rw [DecisionTree.complexity_eq_queryComplexity]
  simpa using FreeM.queryComplexity_le_card (P := DecisionTree.queryPFunctor (Fin 3)) f

/-- Alice sends her bit; Bob answers with the conjunction. -/
def andProtocol : Communication.Protocol Bool Bool Bool :=
  .alice id (.output false) (.bob id (.output false) (.output true))

example : andProtocol.run true true = true := rfl

example : andProtocol.toFreeM.IsTotalRollBound 2 :=
  (Communication.Protocol.depth_le_iff_isTotalRollBound andProtocol 2).mp (by decide)

/-- A counter specification: `incr` returns the old value. -/
abbrev counter : Stateful.Spec.{0, 0, 0} where
  State := ℕ
  Op := Unit
  Result _ := ℕ
  step n _ := (n + 1, n)

example : counter.toResponder.answer 5 () = (5 : ℕ) := rfl

example : counter.toResponder.next 5 () = 6 := rfl

example :
    Stateful.Spec.ofResponder counter.toResponder = { counter with valid := fun _ _ => True } :=
  Stateful.Spec.ofResponder_toResponder counter
