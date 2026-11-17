/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.BangW
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean derivatives of lens reindexing

At a fixed shape, a lens gathers real coordinates by reading one input for each output.
When both fibres are finite, this is a continuous linear map of Euclidean spaces. Its
derivative is the same map, and its adjoint adds weights along the lens's backward map.
-/

public section

namespace PFunctor.Lens

open scoped RealInnerProductSpace

universe u v u' v'

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} (l : Lens P Q) (a : P.A)

/-- The continuous linear map that reads the input coordinate selected by each output. -/
@[expose] noncomputable def euclideanGather :
    EuclideanSpace ℝ (P.B a) →L[ℝ] EuclideanSpace ℝ (Q.B (l.toFunA a)) :=
  (EuclideanSpace.equiv _ ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => EuclideanSpace.proj (l.toFunB a j))

@[simp]
theorem euclideanGather_apply (x : EuclideanSpace ℝ (P.B a)) (j : Q.B (l.toFunA a)) :
    l.euclideanGather a x j = x (l.toFunB a j) := rfl

/-- At each input the Fréchet derivative of gathering is the same coordinate map. -/
theorem hasFDerivAt_euclideanGather (x : EuclideanSpace ℝ (P.B a)) :
    HasFDerivAt (l.euclideanGather a) (l.euclideanGather a) x :=
  (l.euclideanGather a).hasFDerivAt

private theorem inner_toLp_finsupp {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι)
    (w : ι →₀ ℝ) :
    ⟪x, WithLp.toLp 2 (w : ι → ℝ)⟫ =
      Finsupp.liftAddHom (fun i => AddMonoidHom.mulRight (x i)) w := by
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [PiLp.inner_apply, mul_comm]

variable [Fintype (P.B a)] [Fintype (Q.B (l.toFunA a))]

/-- The adjoint of the derivative pushes finite weights through the lens. A collision of
output coordinates adds their weights at the common input coordinate. -/
theorem fderiv_euclideanGather_adjoint (x : EuclideanSpace ℝ (P.B a))
    (w : Q.B (l.toFunA a) →₀ ℝ) :
    (fderiv ℝ (l.euclideanGather a) x).adjoint (WithLp.toLp 2 (w : _ → ℝ)) =
      WithLp.toLp 2 (⇑((bangWMap (S := ℝ) l).toFunB a w)) := by
  rw [(l.hasFDerivAt_euclideanGather a x).fderiv]
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, inner_toLp_finsupp, inner_toLp_finsupp]
  exact (l.liftAddHom_bangWMap (PFunctor.Obj.mk a fun i => AddMonoidHom.mulRight (v i)) w).symm

end PFunctor.Lens
