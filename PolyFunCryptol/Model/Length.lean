/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Data.Fin.Cases

/-! # Finite and infinite Cryptol sequence lengths -/

public section

namespace Cryptol

/-- The numeric kind contains finite sizes and infinity. -/
inductive Length where
  | finite (size : Nat)
  | infinite
  deriving Repr

instance : DecidableEq Length
  | .finite n, .finite m =>
      if h : n = m then isTrue (h ▸ rfl) else isFalse (fun h' => h (Length.finite.inj h'))
  | .infinite, .infinite => isTrue rfl
  | .finite _, .infinite => isFalse (by intro h; cases h)
  | .infinite, .finite _ => isFalse (by intro h; cases h)

namespace Length

/-- Positions in a sequence, with no position in an empty finite sequence.
Implicit reduction exposes the position type in dependent public equations. -/
@[expose, implicit_reducible] def Index : Length → Type
  | .finite n => Fin n
  | .infinite => Nat

/-- Addition of numeric lengths. -/
@[expose] def add : Length → Length → Length
  | .finite n, .finite m => .finite (n + m)
  | _, _ => .infinite

/-- Multiplication of lengths, with an empty dimension annihilating infinity. -/
@[expose] def mul : Length → Length → Length
  | .finite 0, _ | _, .finite 0 => .finite 0
  | .finite n, .finite m => .finite (n * m)
  | _, _ => .infinite

@[simp] theorem mul_finite_zero (l : Length) : l.mul (.finite 0) = .finite 0 := by
  cases l with
  | finite n => cases n <;> rfl
  | infinite => rfl

/-- Length of a parallel comprehension. -/
@[expose] def min : Length → Length → Length
  | .finite n, .finite m => .finite (Nat.min n m)
  | .finite n, .infinite => .finite n
  | .infinite, n => n

/-- Convert a valid typed sequence position to its natural-number index. -/
@[expose] def indexNat : {l : Length} → l.Index → Nat
  | .finite _, i => i.val
  | .infinite, i => i

/-- A position in a flattened sequence implies a nonempty row width. -/
theorem each_pos_of_index (parts : Length) (each : Nat)
    (i : (parts.mul (.finite each)).Index) : 0 < each := by
  cases each with
  | zero =>
      have h : (parts.mul (.finite 0)).Index = Fin 0 := by rw [mul_finite_zero]; rfl
      exact Fin.elim0 (h ▸ i)
  | succ each => exact Nat.zero_lt_succ _

/-- Check a possibly negative integer against a finite or infinite length. -/
@[expose] def checkIndex (l : Length) (i : Int) : Option l.Index :=
  if 0 ≤ i then
    match l with
    | .finite n => if h : i.toNat < n then some ⟨i.toNat, h⟩ else none
    | .infinite => some i.toNat
  else none

/-- A successful bounds check retains the original nonnegative index. -/
theorem indexNat_checkIndex (l : Length) (i : Int) (j : l.Index)
    (h : l.checkIndex i = some j) : (indexNat j : Int) = i := by
  cases l with
  | finite n =>
      simp only [checkIndex] at h
      split at h
      · rename_i hi
        split at h
        · cases Option.some.inj h
          exact Int.toNat_of_nonneg hi
        · cases h
      · cases h
  | infinite =>
      simp only [checkIndex] at h
      split at h
      · rename_i hi
        cases Option.some.inj h
        exact Int.toNat_of_nonneg hi
      · cases h

end Length

end Cryptol
