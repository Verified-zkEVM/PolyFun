/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Realizability.Instances
import Mathlib.Data.Fintype.EquivFin

/-! # Representability is a restriction on objects

The finite-state step class has binary structural operations but does not
represent every Lean type. Its objects are represented types, not all of `Type`.
-/

public section

example : ¬ Nonempty (PFunctor.StepClass.finite.Str Nat) := by
  change ¬ Nonempty (Fintype Nat)
  rintro ⟨representation⟩
  have : IsEmpty (Fintype Nat) := isEmpty_fintype.mpr inferInstance
  exact isEmptyElim representation
