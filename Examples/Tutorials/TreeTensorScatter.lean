/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Accumulating weights along an index map

Several output positions of a tensor can read the same input. The reverse operation adds the
weights of those positions into the input slot. An input that was never read receives zero.
-/

public section

namespace Examples.TreeTensor

variable {α : Type*} {n m : Nat}

/-- Add each output weight into its source slot, starting with a zero vector. -/
def scatter [Zero α] [Add α] (r : Fin m → Fin n) (w : Vector α m) : Vector α n :=
  Fin.foldl m (fun acc j => acc.set (r j) (acc.get (r j) + w.get j)) (Vector.replicate n 0)

private theorem get_foldl_add [AddCommMonoid α] (r : Fin m → Fin n) (w : Fin m → α)
    (acc : Vector α n) (i : Fin n) :
    (Fin.foldl m (fun v j => v.set (r j) (v.get (r j) + w j)) acc).get i =
      acc.get i + ∑ j, if r j = i then w j else 0 := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ, Fin.sum_univ_succ, ih (fun j => r j.succ) (fun j => w j.succ)]
    change (acc.set (r 0) (acc.get (r 0) + w 0))[i.val] + _ = acc[i.val] + _
    by_cases h : r 0 = i
    · subst i
      simp [add_assoc, Vector.get]
    · have hv : (r 0).val ≠ i.val := fun eq => h (Fin.ext eq)
      simp [h, hv]

/-- Each slot contains the sum of its fibre under the index map. -/
theorem scatter_spec [AddCommMonoid α] (r : Fin m → Fin n) (w : Vector α m) (i : Fin n) :
    (scatter r w).get i = Finsupp.mapDomain r (Finsupp.equivFunOnFinite.symm w.get) i := by
  rw [scatter, get_foldl_add, Finsupp.mapDomain_apply, Finsupp.sum_fintype _ _ (by simp)]
  change (Vector.replicate n (0 : α))[i.val] + _ = _
  simp [Finsupp.single_apply]

/-- Scattering along a composite index map gives the same weights as the two successive scatters. -/
theorem scatter_comp [AddCommMonoid α] {k : Nat} (r : Fin m → Fin n) (q : Fin k → Fin m)
    (w : Vector α k) : scatter (r ∘ q) w = scatter r (scatter q w) := by
  have intermediate : Finsupp.equivFunOnFinite.symm (scatter q w).get =
      Finsupp.mapDomain q (Finsupp.equivFunOnFinite.symm w.get) :=
    Finsupp.ext (scatter_spec q w)
  apply Vector.ext
  intro i hi
  change (scatter (r ∘ q) w).get ⟨i, hi⟩ = (scatter r (scatter q w)).get ⟨i, hi⟩
  rw [scatter_spec, scatter_spec, Finsupp.mapDomain_comp, intermediate]

end Examples.TreeTensor
