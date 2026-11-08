/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Suprema over `Fin`

A supremum over `Fin (n + 1)` splits off its first term. Mathlib unfolds suprema over `Bool`,
`Option` and sums (`iSup_bool_eq`, `iSup_option`, `iSup_sum`), and over an empty type such as
`Fin 0` (`iSup_of_empty`); this is the `Fin` case, used to evaluate worst-case costs over finite
answer types.
-/

public section

namespace Fin

universe u

theorem iSup_succ {L : Type u} [CompleteLattice L] {n : ℕ} (f : Fin (n + 1) → L) :
    ⨆ i, f i = f 0 ⊔ ⨆ i : Fin n, f i.succ := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup f 0) (iSup_le fun j => le_iSup f _))
  induction i using Fin.cases with
  | zero => exact le_sup_left
  | succ j => exact le_sup_of_le_right (le_iSup (fun j : Fin n => f j.succ) j)

end Fin
