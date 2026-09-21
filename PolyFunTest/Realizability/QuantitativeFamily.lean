/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Realizability.QuantitativeDescription
public import PolyFun.Realizability.Quantitative.Family

/-!
# Polynomial backends over the cost-free backend

The degenerate instance: zero canonical polynomials, zero envelope and overhead, and the trivial
description measure. It shows that `PolynomialBackend`, `FamRealizer`, and `FiniteTables`
instantiate at a backend that proves nothing, so none of them carries complexity content of its
own; the content is entirely in the backend's certificates.
-/

public section

namespace PFunctor.QuantitativeFamilyTest

open QuantitativeStepClass QuantitativeStepClass.DescriptionMeasure QuantitativeDescriptionTest

/-- Zero certificates over the cost-free backend and the trivial description measure. -/
noncomputable def trivialBackend : trivialMeasure.PolynomialBackend where
  timeOf _ := 0
  cost_le _ _ := by
    rw [Polynomial.eval_zero]
    exact le_rfl
  envelope _ := 0
  size_le _ _ := by
    rw [Polynomial.eval_zero]
    exact le_rfl
  envelope_le _ _ _ := by simp
  overhead _ _ := 0
  overhead_le _ _ _ _ := by simp
  timeOf_compose_le _ _ _ := by simp
  idTime := 0
  timeOf_identity_le _ _ := le_rfl
  idDesc := 0
  descSize_identity_le _ := le_rfl
  descSize_compose_le _ _ := le_rfl

/-- Every function is a finite table at zero size in the cost-free backend. -/
noncomputable def trivialTables :
    trivialMeasure.FiniteTables trivialBackend (fun {_} _ ↦ True) where
  table _ _ _ _ := PUnit.unit
  descSize_table_le := by
    intros
    exact Nat.zero_le _
  time_table_le := by
    intro A B _ a ha b f Lb hB k
    change (0 : Polynomial ℕ).eval k ≤ k + Lb + 1
    simp

/-- Families compose over the degenerate instance. -/
noncomputable example {D E F : ℕ → Type} {a : ∀ n, StepClass.unconstrained.Str (D n)}
    {b : ∀ n, StepClass.unconstrained.Str (E n)} {c : ∀ n, StepClass.unconstrained.Str (F n)}
    {f : ∀ n, D n → E n} {g : ∀ n, E n → F n}
    (X : trivialMeasure.FamRealizer trivialBackend a b f)
    (Y : trivialMeasure.FamRealizer trivialBackend b c g) :
    trivialMeasure.FamRealizer trivialBackend a c (fun n ↦ g n ∘ f n) :=
  X.comp Y

/-- Finite tables over `Fin 2` instantiate with the constant bounds. -/
noncomputable example :
    trivialMeasure.FamRealizer trivialBackend (fun _ ↦ PUnit.unit) (fun _ ↦ PUnit.unit)
      (fun _ (x : Fin 2) ↦ x) :=
  FamRealizer.ofFintype trivialTables _ (fun _ ↦ trivial) _ _ (Polynomial.C 2) (fun _ ↦ by simp)
    0 (fun _ _ ↦ by rw [Polynomial.eval_zero]; exact le_rfl)
    0 (fun _ _ ↦ by rw [Polynomial.eval_zero]; exact le_rfl)

/-- The composed family's uniform time bound is the sum of the components' plus a zero overhead. -/
example {D E F : ℕ → Type} {a : ∀ n, StepClass.unconstrained.Str (D n)}
    {b : ∀ n, StepClass.unconstrained.Str (E n)} {c : ∀ n, StepClass.unconstrained.Str (F n)}
    {f : ∀ n, D n → E n} {g : ∀ n, E n → F n}
    (X : trivialMeasure.FamRealizer trivialBackend a b f)
    (Y : trivialMeasure.FamRealizer trivialBackend b c g) :
    (X.comp Y).time = X.time + Y.time.comp (Polynomial.X + 0) + 0 :=
  FamRealizer.time_comp X Y

end PFunctor.QuantitativeFamilyTest
