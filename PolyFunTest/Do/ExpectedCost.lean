/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Do.Normalization
public import PolyFun.PFunctor.Free.Do
public import PolyFun.PFunctor.Free.Measure.FiniteKernel

/-!
# Computing the expected cost of finite clients

A client flips a fair coin and flips again after heads. Its exact cost and its upper-bound
verification condition both normalize to arithmetic. A lossy kernel exercises explicit table
expansion with different continuation costs for its joint outcomes.
-/

public section

open Std.WP OrderDual PFunctor PFunctor.FreeM MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Do.ExpectedCost

abbrev Coin : PFunctor.{0, 0} := monomial Unit Bool

private noncomputable def fair : KernelHandler Coin Unit :=
  fun _ => Kernel.const _ ((2⁻¹ : ℝ≥0∞) • (Measure.dirac (true, ()) + Measure.dirac (false, ())))

private def flipAgain : FreeM Coin Bool := do
  let first ← FreeM.lift (P := Coin) ()
  if first then FreeM.lift (P := Coin) () else pure false

private noncomputable abbrev charge : OpSpec Coin (Unit → ℝ≥0∞) :=
  OpSpec.statefulExpectedCharge fair (fun _ _ => 1)

example : wpFold charge flipAgain (fun _ _ => 0) () = 1 + 2⁻¹ := by
  simp only [flipAgain, charge, fair, expected_cost]
  norm_num [expected_cost]

section
set_option experimental.vcgen true

private noncomputable abbrev meter : WPMonad (FreeM Coin) (Unit → ℝ≥0∞)ᵒᵈ EStack⟨⟩ᵒᵈ :=
  charge.toUpperWPMonad (OpSpec.statefulExpectedCharge_mono _ _)

attribute [local instance] meter

example : ⦃ toDual (fun _ : Unit => (1 + 2⁻¹ : ℝ≥0∞)) ⦄ flipAgain
    ⦃ fun (_ : Bool) => toDual (fun _ : Unit => (0 : ℝ≥0∞)) ⦄ := by
  unfold flipAgain
  vcgen
  simp only [wp_norm]
  intro s
  simp only [OpSpec.toUpperWPMonad_wp, fair, expected_cost]
  norm_num [expected_cost]

end

/-- Normalization leaves the joint continuation integral under an unspecified kernel. -/
example (K : KernelHandler Coin Bool) (c : Coin.A → Bool → ℝ≥0∞) (k : Bool → Bool → ℝ≥0∞)
    (s : Bool) :
    wpFold (OpSpec.statefulExpectedCharge K c) (FreeM.lift ()) k s =
      c () s + ∫⁻ z, k z.1 z.2 ∂K () s := by
  conv_lhs =>
    simp only [expected_cost]
    guard_target = c () s + ∫⁻ (z : Bool × Bool), k z.1 z.2 ∂K () s

private noncomputable def lossy : KernelHandler Coin Bool :=
  fun _ => Kernel.const _ ((4⁻¹ : ℝ≥0∞) • Measure.dirac (true, false) +
    (2⁻¹ : ℝ≥0∞) • Measure.dirac (false, true))

/-- An incoming charge of two and continuation payments of four and eight at masses one
quarter and one half give a total of seven. -/
example :
    wpFold (OpSpec.statefulExpectedCharge lossy (fun _ s => if s then 0 else 2))
      (FreeM.lift (P := Coin) ())
      (fun (answer next : Bool) =>
        (if answer then 4 else 0) + (if next then 8 else 0))
      false = 7 := by
  rw [wpFold_lift, OpSpec.statefulExpectedCharge_eq_sum (P := Coin), Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [lossy, Fintype.sum_bool, Measure.dirac_apply, Pi.single_apply]
  rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, mul_assoc]
  norm_num [ENNReal.mul_inv_cancel]

end PolyFunTest.Do.ExpectedCost
