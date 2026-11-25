/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorReshape
public import PolyFun.PFunctor.Lens.BangW.Euclidean

/-!
# Derivative and adjoint of a tree reshape

At a fixed binary tree, the real coordinates of the executable reshape form a map between
Euclidean spaces. Its derivative reads the selected positions, and its adjoint agrees at
every original tree position with the buffer prepared by the reverse pass.
-/

public section

namespace Examples.TreeTensor

open PFunctor

variable {m : Nat}

/-- The Euclidean vector obtained by running the forward traversal and gathering its entries. -/
noncomputable def euclideanReshape (s : Shape) (r : Fin m → Fin (size s))
    (x : EuclideanSpace ℝ (Pos s)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (gather r (flatten s x)).get

/-- The prepared forward vector is the continuous linear gather of the layout lens. -/
theorem euclideanReshape_eq (s : Shape) (r : Fin m → Fin (size s)) :
    euclideanReshape s r = ⇑((layout s r).euclideanGather PUnit.unit) := by
  funext x
  ext j
  exact gather_flatten_get s x r j

/-- The Fréchet derivative of the executable reshape at a real tree is its layout gather. -/
theorem hasFDerivAt_euclideanReshape (s : Shape) (r : Fin m → Fin (size s))
    (x : EuclideanSpace ℝ (Pos s)) :
    HasFDerivAt (euclideanReshape s r) ((layout s r).euclideanGather PUnit.unit) x := by
  rw [euclideanReshape_eq]
  exact (layout s r).hasFDerivAt_euclideanGather PUnit.unit x

/-- Reading the prepared reverse buffer gives the adjoint derivative at every tree position. -/
theorem fderiv_euclideanReshape_adjoint_apply (s : Shape) (r : Fin m → Fin (size s))
    (x : EuclideanSpace ℝ (Pos s)) (w : Vector ℝ m) (p : Pos s) :
    (fderiv ℝ (euclideanReshape s r) x).adjoint (WithLp.toLp 2 w.get) p =
      (returnWeights s r w).get p := by
  rw [euclideanReshape_eq]
  have h := (layout s r).fderiv_euclideanGather_adjoint PUnit.unit x
    (Finsupp.equivFunOnFinite.symm w.get)
  exact (congrArg (fun v : EuclideanSpace ℝ (Pos s) => v p) h).trans
    (returnWeights_get_eq_bangWMap s r w p).symm

end Examples.TreeTensor
