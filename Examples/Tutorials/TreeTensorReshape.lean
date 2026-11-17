/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorTraversal
public import Examples.Tutorials.TreeTensorScatter
public import PolyFun.PFunctor.Lens.Yoneda
public import PolyFun.PFunctor.Lens.BangW

/-!
# Reshaping a tree and returning weights to it

An in-order traversal gives every tree position a flat index. A selection of these indices
may repeat or omit entries. Its forward action reads the selected entries. Its reverse action
adds weights at repeated indices and returns zero at omitted positions. Preparing the reverse
result computes its flat buffer and index function once. Each later read applies the stored index
function and selects one slot. The forward theorem uses the composite lens's action on labelled
shapes, and the reverse theorem uses its action on finitely supported weights.
-/

public section

namespace Examples.TreeTensor

open PFunctor

variable {α : Type*} {m n : Nat}

/-- Materialize selected vector entries. Each output chooses its own input index. -/
def gather (r : Fin m → Fin n) (x : Vector α n) : Vector α m :=
  Vector.ofFn fun j => x.get (r j)

/-- At a fixed tree shape the traversal and selection are lenses between single-shape layouts. -/
def layout (s : Shape) (r : Fin m → Fin (size s)) :
    Lens (purePower.{0, 0} (Pos s)) (purePower.{0, 0} (Fin m)) :=
  Lens.purePowerMap r ∘ₗ (Lens.purePowerMap (inorder.toFunB s) :
    Lens (purePower.{0, 0} (Pos s)) (purePower.{0, 0} (Fin (size s))))

@[simp] theorem layout_toFunB (s : Shape) (r : Fin m → Fin (size s)) (j : Fin m) :
    (layout s r).toFunB PUnit.unit j = indexEquiv s (r j) := by
  exact inorder_toFunB s (r j)

/-- Gathering from the materialized tree agrees with the composite lens. -/
theorem gather_flatten_get (s : Shape) (x : Pos s → α) (r : Fin m → Fin (size s)) (j : Fin m) :
    (gather r (flatten s x)).get j =
      ((layout s r).mapObj (Obj.mk PUnit.unit x)).snd j := by
  change (Vector.ofFn _)[j.val] = _
  rw [Vector.getElem_ofFn]
  exact flatten_get s x (r j)

/-- A materialized vector together with the lookup function for its original tree shape. -/
structure TreeBuffer (s : Shape) (α : Type*) where
  private mk ::
  /-- The weights in in-order layout. -/
  values : Vector α (size s)
  /-- The flat index of a tree position. -/
  rank : Pos s → Fin (size s)

/-- Read one slot of a prepared tree buffer. -/
def TreeBuffer.get {s : Shape} (buffer : TreeBuffer s α) (p : Pos s) : α :=
  buffer.values.get (buffer.rank p)

/-- Scatter the weights once and retain the inverse traversal for repeated tree reads. -/
def returnWeights [Zero α] [Add α] (s : Shape) (r : Fin m → Fin (size s))
    (w : Vector α m) : TreeBuffer s α :=
  ⟨scatter r w, (indexEquiv s).invFun⟩

/-- Each prepared lookup equals the weight pushed along the composite's direction map. -/
theorem returnWeights_get_eq_mapDomain [AddCommMonoid α] (s : Shape)
    (r : Fin m → Fin (size s)) (w : Vector α m) (p : Pos s) :
    (returnWeights s r w).get p =
      Finsupp.mapDomain ((layout s r).toFunB PUnit.unit)
        (Finsupp.equivFunOnFinite.symm w.get) p := by
  change (scatter r w).get ((indexEquiv s).symm p) =
    (Finsupp.mapDomain ((indexEquiv s) ∘ r) _) p
  rw [scatter_spec, Finsupp.mapDomain_comp, Finsupp.mapDomain_equiv_apply]

/-- The weighted action on the whole composite is implemented by the prepared tree buffer. -/
theorem returnWeights_get_eq_bangWMap [AddCommMonoid α] (s : Shape)
    (r : Fin m → Fin (size s)) (w : Vector α m) (p : Pos s) :
    (returnWeights s r w).get p =
      (Lens.bangWMap (S := α) (layout s r)).toFunB PUnit.unit
        (Finsupp.equivFunOnFinite.symm w.get) p :=
  returnWeights_get_eq_mapDomain s r w p

end Examples.TreeTensor
