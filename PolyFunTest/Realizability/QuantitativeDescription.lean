/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Realizability.Quantitative
public import PolyFun.Realizability.Quantitative.Counting
public import Mathlib.Data.Set.Countable
public import Mathlib.Basic.Countable.Basic

/-!
# Vacuity canaries for description measures

The cost-free backend admits no description measure against a trivial faithfulness predicate:
the finite cover would make `ℕ → Bool` a countable union of finite sets. Against an unsatisfiable
predicate it admits the trivial measure, under which every predicate family is realizable at size
zero. The counting separation therefore carries no content of its own: all of it sits in the
faithfulness hypothesis and the backend's description count.
-/

public section

namespace PFunctor.QuantitativeDescriptionTest

open QuantitativeStepClass

/-- `ℕ → Bool` is not countable (Cantor). -/
theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  classical
  intro h
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (ℕ → Bool)
  refine Function.cantor_injective (fun S : Set ℕ ↦ g fun m ↦ decide (m ∈ S)) ?_
  intro S T hST
  have hfun := hg hST
  ext m
  simpa using congrFun hfun m

/-- No description measure exists for the cost-free backend against a trivial faithfulness
predicate. -/
theorem isEmpty_descriptionMeasure_true :
    IsEmpty (QuantitativeTest.zeroBackend.{0, 0, 0}.DescriptionMeasure (fun {_} _ ↦ True)) := by
  refine ⟨fun M ↦ ?_⟩
  have hall : ∀ f : ℕ → Bool, ∃ d,
      f ∈ M.RealizableLE (A := ℕ) (B := Bool) PUnit.unit PUnit.unit d := fun f ↦
    ⟨M.descSize
      (PUnit.unit : QuantitativeTest.zeroBackend.{0, 0, 0}.Realizer PUnit.unit PUnit.unit f),
      M.mem_realizableLE.mpr ⟨PUnit.unit, le_rfl⟩⟩
  have hcount : (Set.univ : Set (ℕ → Bool)).Countable := by
    have hsub : (Set.univ : Set (ℕ → Bool)) ⊆
        ⋃ d : ℕ, ↑(M.exists_realizableLE_covering (A := ℕ) (B := Bool) PUnit.unit
          (b := PUnit.unit) trivial d).choose := by
      intro f _
      obtain ⟨d, hd⟩ := hall f
      exact Set.mem_iUnion.mpr
        ⟨d, (M.exists_realizableLE_covering PUnit.unit trivial d).choose_spec.1 hd⟩
    exact (Set.countable_iUnion fun d ↦ Finset.countable_toSet _).mono hsub
  exact not_countable_nat_bool (Set.countable_univ_iff.mp hcount)

/-- Against an unsatisfiable faithfulness predicate the axioms are trivially satisfiable. Exposed so
that sibling tests can compute with its zero description size. -/
@[expose] def trivialMeasure :
    QuantitativeTest.zeroBackend.{0, 0, 0}.DescriptionMeasure (fun {_} _ ↦ False) where
  descSize _ := 0
  Desc _ _ _ := PUnit
  descFintype _ _ _ := inferInstance
  describe := by
    intros
    exact PUnit.unit
  describe_determines h := h.elim

/-- Under the trivial measure every predicate family is realizable at description size zero. -/
theorem free_no_separation (f : (n : ℕ) → ℕ → Bool) :
    ∃ q : Polynomial ℕ, ∀ n,
      f n ∈ trivialMeasure.RealizableLE (A := ℕ) (B := Bool) PUnit.unit PUnit.unit (q.eval n) :=
  ⟨0, fun _ ↦ trivialMeasure.mem_realizableLE.mpr ⟨PUnit.unit, by
    rw [Polynomial.eval_zero]
    exact le_rfl⟩⟩

end PFunctor.QuantitativeDescriptionTest
