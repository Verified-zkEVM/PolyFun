/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.DecisionTree.Parity

public import PolyFunFrontier.PFunctor.Free.DecisionTree

/-!
# Query lower bounds for free programs

A free program over the Boolean query interface `monomial ι Bool` *computes* `f` when, answering
each query `i` from an input `x`, it returns `f x`. Its total roll bound `d`
(`PFunctor.FreeM.IsTotalRollBound`) bounds the number of queries it makes on every input. This file
transfers cslib-frontier's decision-tree lower bounds to such programs, through
`Cslib.DecisionTree.equivFreeM`.

- Every program computing `f` with total roll bound `d` has `complexity f ≤ d`, and some program
  attains `complexity f` (`Cslib.DecisionTree.complexity_le_of_isTotalRollBound`,
  `Cslib.DecisionTree.exists_isTotalRollBound_complexity`).
- **Parity needs every bit.** A program computing the parity of `n` bits has no total roll bound
  below `n`, and querying every bit once achieves `n`
  (`Cslib.DecisionTree.le_of_isTotalRollBound_parity`,
  `Cslib.DecisionTree.exists_isTotalRollBound_parity`).
- **Sensitivity.** If flipping each bit of `S` changes `f` at one input, every program computing `f`
  needs `#S` queries (`Cslib.DecisionTree.card_le_of_isTotalRollBound`). For parity under a partial
  assignment, the free bits must all be queried
  (`Cslib.DecisionTree.card_free_le_of_isTotalRollBound_parity_fill`).

The arguments are cslib-frontier's adversary arguments for decision trees
(`Cslib.DecisionTree.complexity_parity`,
`Cslib.DecisionTree.card_le_complexity_of_forall_update_ne`); only the transfer is proved here.

## Main results

* `Cslib.DecisionTree.complexity_le_of_isTotalRollBound`
* `Cslib.DecisionTree.exists_isTotalRollBound_complexity`
* `Cslib.DecisionTree.card_le_of_isTotalRollBound`
* `Cslib.DecisionTree.le_of_isTotalRollBound_parity`
* `Cslib.DecisionTree.exists_isTotalRollBound_parity`
* `Cslib.DecisionTree.card_free_le_of_isTotalRollBound_parity_fill`
-/

@[expose] public section

universe u v

namespace Cslib.DecisionTree

open PFunctor Finset BitString

variable {ι : Type u} {β : Type v}

/-- A free program over Boolean queries that computes `f` within total roll bound `d` shows that
the decision tree complexity of `f` is at most `d`. -/
theorem complexity_le_of_isTotalRollBound {f : (ι → Bool) → β} {p : (monomial ι Bool).FreeM β}
    (hp : ∀ x, p.foldFreeM id (fun i k => k (x i)) = f x) {d : ℕ}
    (hd : p.IsTotalRollBound d) : complexity f ≤ d :=
  (complexity_le_depth (t := ofFreeM p) fun x => (eval_ofFreeM p x).trans (hp x)).trans
    ((depth_ofFreeM_le_iff p d).2 hd)

/-- Over finitely many variables, some free program computes `f` within total roll bound
`complexity f`. -/
theorem exists_isTotalRollBound_complexity [Finite ι] (f : (ι → Bool) → β) :
    ∃ p : (monomial ι Bool).FreeM β,
      (∀ x, p.foldFreeM id (fun i k => k (x i)) = f x) ∧ p.IsTotalRollBound (complexity f) := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact ⟨t.toFreeM, fun x => (eval_toFreeM t x).trans (ht x),
    (depth_le_iff_isTotalRollBound t _).1 hd.le⟩

/-- **Sensitivity lower bound.** If flipping each bit of `S` changes `f` at the input `x`, every
free program computing `f` has total roll bound at least `#S`. -/
theorem card_le_of_isTotalRollBound [Finite ι] [DecidableEq ι] {f : (ι → Bool) → β}
    {x : ι → Bool} {S : Finset ι} (hS : ∀ i ∈ S, f (Function.update x i (!x i)) ≠ f x)
    {p : (monomial ι Bool).FreeM β} (hp : ∀ y, p.foldFreeM id (fun i k => k (y i)) = f y)
    {d : ℕ} (hd : p.IsTotalRollBound d) : #S ≤ d :=
  (card_le_complexity_of_forall_update_ne hS).trans (complexity_le_of_isTotalRollBound hp hd)

variable {n : ℕ}

/-- **Parity needs every bit.** A free program that computes the parity of `n` bits has no total
roll bound below `n`. -/
theorem le_of_isTotalRollBound_parity {p : (monomial (Fin n) Bool).FreeM Bool}
    (hp : ∀ x, p.foldFreeM id (fun i k => k (x i)) = parity n x) {d : ℕ}
    (hd : p.IsTotalRollBound d) : n ≤ d := by
  simpa only [complexity_parity] using complexity_le_of_isTotalRollBound hp hd

/-- The parity bound is attained: some free program computes the parity of `n` bits within total
roll bound `n`. -/
theorem exists_isTotalRollBound_parity :
    ∃ p : (monomial (Fin n) Bool).FreeM Bool,
      (∀ x, p.foldFreeM id (fun i k => k (x i)) = parity n x) ∧ p.IsTotalRollBound n := by
  simpa only [complexity_parity] using exists_isTotalRollBound_complexity (parity n)

/-- **Restricted parity.** Under a partial assignment `ρ`, a free program that computes parity of
the filled input queries every free bit: its total roll bound is at least `#ρ.free`. -/
theorem card_free_le_of_isTotalRollBound_parity_fill (ρ : PartialAssignment (Fin n))
    {p : (monomial (Fin n) Bool).FreeM Bool}
    (hp : ∀ x, p.foldFreeM id (fun i k => k (x i)) = parity n (ρ.fill x)) {d : ℕ}
    (hd : p.IsTotalRollBound d) : #ρ.free ≤ d :=
  (card_free_le_complexity_parity_fill ρ).trans (complexity_le_of_isTotalRollBound hp hd)

end Cslib.DecisionTree
