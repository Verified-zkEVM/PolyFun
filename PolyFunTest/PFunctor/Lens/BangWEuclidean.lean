/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorEuclidean
import Mathlib.Tactic.NormNum

/-!
# Euclidean reshape regressions

Selecting two copies of 46 and one copy of 2 pairs with weights 2, 3 and 7 to give 244.
The adjoint sends 5 to the duplicated leaf and zero to the omitted root. An empty selection
has the zero adjoint.
-/

public section

namespace Examples.TreeTensor.Test

open PFunctor
open scoped RealInnerProductSpace

private abbrev shape : Shape := .node (.node .leaf .leaf) .leaf

private noncomputable def flatValues : Vector ℝ 5 := #v[-42, 7, 46, 60, 2]

private def selection : Fin 3 → Fin (size shape) := (#v[2, 2, 4] : Vector (Fin 5) 3).get

private noncomputable def input : EuclideanSpace ℝ (Pos shape) :=
  WithLp.toLp 2 fun p => flatValues.get ((indexEquiv shape).symm p)

private noncomputable def weights : Vector ℝ 3 := #v[2, 3, 7]

private theorem selected_apply (j : Fin 3) :
    euclideanReshape shape selection input j = flatValues.get (selection j) := by
  rw [euclideanReshape_eq]
  change (layout shape selection).euclideanGather PUnit.unit input j = _
  rw [PFunctor.Lens.euclideanGather_apply, layout_toFunB]
  exact congrArg flatValues.get ((indexEquiv shape).symm_apply_apply _)

private theorem forward_dot :
    ⟪euclideanReshape shape selection input, WithLp.toLp 2 weights.get⟫ = 244 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Real.inner_apply, selected_apply]
  change (46 : ℝ) * 2 + 46 * 3 + 2 * 7 = 244
  norm_num

example :
    ⟪input, (fderiv ℝ (euclideanReshape shape selection) input).adjoint
      (WithLp.toLp 2 weights.get)⟫ = 244 := by
  rw [(hasFDerivAt_euclideanReshape shape selection input).fderiv,
    ContinuousLinearMap.adjoint_inner_right]
  simpa only [euclideanReshape_eq] using forward_dot

private theorem adjoint_at (i : Fin (size shape)) :
    (fderiv ℝ (euclideanReshape shape selection) input).adjoint
      (WithLp.toLp 2 weights.get) (indexEquiv shape i) =
      ∑ j : Fin 3, if selection j = i then weights.get j else 0 := by
  classical
  rw [fderiv_euclideanReshape_adjoint_apply, returnWeights_get_eq_mapDomain]
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [layout_toFunB, Finsupp.single_apply, eq_comm]

example : (fderiv ℝ (euclideanReshape shape selection) input).adjoint
    (WithLp.toLp 2 weights.get) (indexEquiv shape ⟨2, by decide⟩) = 5 := by
  rw [adjoint_at, Fin.sum_univ_three]
  change (2 : ℝ) + 3 + 0 = 5
  norm_num

example : (fderiv ℝ (euclideanReshape shape selection) input).adjoint
    (WithLp.toLp 2 weights.get) (indexEquiv shape ⟨3, by decide⟩) = 0 := by
  rw [adjoint_at, Fin.sum_univ_three]
  change (0 : ℝ) + 0 + 0 = 0
  simp

/-- Sending weights back from an empty selection gives the zero map on tree positions. -/
theorem adjoint_empty_selection {s : Shape} (x : EuclideanSpace ℝ (Pos s)) :
    (fderiv ℝ (euclideanReshape s Fin.elim0) x).adjoint =
      (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Pos s)) := by
  ext w p
  have h : w = 0 := Subsingleton.elim _ _
  simp [h]

end Examples.TreeTensor.Test
