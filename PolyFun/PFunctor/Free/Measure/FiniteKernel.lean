/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.FiniteKernel.Attr
public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Computing expected charges of finite programs

`simp only [expected_cost]` pushes the fold through program constructors and evaluates integrals
against finite mixtures of point masses when singletons are measurable. A symbolic kernel leaves
the joint continuation integral in the goal. Use `PFunctor.OpSpec.statefulExpectedCharge_eq_sum`
to expand a finite request as a table.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

attribute [expected_cost] PFunctor.FreeM.wpFold_bind PFunctor.FreeM.wpFold_map
  PFunctor.FreeM.wpFold_lift PFunctor.FreeM.wpFold_liftBind PFunctor.FreeM.wpFold_pure
  PFunctor.OpSpec.expectedCharge_apply PFunctor.OpSpec.statefulExpectedCharge_apply
  Kernel.const_apply Kernel.deterministic_apply lintegral_zero_measure lintegral_dirac
  lintegral_add_measure lintegral_smul_measure

/-- For a request with finite answers and finite state, each continuation contributes its
value weighted by the mass of the corresponding answer and successor state. -/
theorem PFunctor.OpSpec.statefulExpectedCharge_eq_sum {P : PFunctor} {S : Type*}
    [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) (a : P.A)
    [Fintype (P.B a)] [MeasurableSingletonClass (P.B a)] (k : P.B a → S → ℝ≥0∞) (s : S) :
    statefulExpectedCharge K c a k s =
      c a s + ∑ z : P.B a × S, k z.1 z.2 * K a s {z} := by
  rw [statefulExpectedCharge_apply, lintegral_fintype]
