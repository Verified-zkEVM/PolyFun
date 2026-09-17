/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
import Mathlib.Data.Fintype.EquivFin

/-! # Representability is a restriction on objects

The finite-state step class has binary structural operations but does not
represent every Lean type. Its objects are represented types, not all of `Type`.
-/

@[expose] public section

example : ¬ Nonempty (PFunctor.StepClass.finite.Str Nat) := by
  change ¬ Nonempty (Fintype Nat)
  rintro ⟨representation⟩
  have : IsEmpty (Fintype Nat) := isEmpty_fintype.mpr inferInstance
  exact isEmptyElim representation

namespace RepresentationBoundary

/-- Types with two distinguished, distinct points; every function is admissible. -/
def twoPoint : PFunctor.StepClass.{0, 0} where
  Str A := { points : A × A // points.1 ≠ points.2 }
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

instance : twoPoint.HasProd where
  prod a b := ⟨((a.val.1, b.val.1), (a.val.2, b.val.1)),
    fun h => a.property (congrArg Prod.fst h)⟩
  fst_mem _ _ := trivial
  snd_mem _ _ := trivial
  pair_mem _ _ := trivial

instance : twoPoint.HasSum where
  sum a _ := ⟨(Sum.inl a.val.1, Sum.inl a.val.2), fun h => a.property (Sum.inl.inj h)⟩
  inl_mem _ _ := trivial
  inr_mem _ _ := trivial
  elim_mem _ _ := trivial

instance : twoPoint.HasOption where
  option a := ⟨(none, some a.val.1), by simp⟩
  omap_mem _ := trivial
  none_mem _ _ := trivial
  obindCtx_mem _ := trivial
  some_mem _ := trivial

instance : twoPoint.IsDistributive where
  distrib_mem _ _ _ := trivial

instance : twoPoint.Distributive where

/-- The countermodel has an actual represented object. -/
example : Nonempty (twoPoint.Str Bool) := ⟨⟨(false, true), by decide⟩⟩

/-- Even the full structural bundle need not represent the terminal type. -/
example : ¬ Nonempty (twoPoint.Str Unit) := by
  rintro ⟨⟨points, distinct⟩⟩
  exact distinct (Subsingleton.elim _ _)

/-- Nor does it need a representation of the initial type. -/
example : ¬ Nonempty (twoPoint.Str Empty) := by
  rintro ⟨⟨points, _⟩⟩
  exact points.1.elim

end RepresentationBoundary
