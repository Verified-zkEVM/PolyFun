/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.BitVec

/-!
# Overwriting a Single Bit of a Bitvector

`BitVec.overwriteBit i b m` writes `b` at position `i`, counting from the least significant bit.
`BitVec.getLsbD_overwriteBit` describes the value read at any position after the write.

When `i < n`, exchanging bit `i` of `m : BitVec n` with a separate Boolean is an involution on
`BitVec n × Bool`. For a uniformly sampled pair, the swap preserves uniformity and puts the
original bit at `i` in the Boolean coordinate. When `n ≤ i`, the write leaves `m` unchanged
and `m.getLsbD i` returns `false`.
-/

public section

namespace BitVec

variable {n : ℕ}

/-- Overwrite the `i`-th least significant bit of `m` with `b`, leaving all other bits
unchanged. Out-of-range positions (`n ≤ i`) leave `m` unmodified. -/
def overwriteBit (i : ℕ) (b : Bool) (m : BitVec n) : BitVec n :=
  if b then m ||| twoPow n i else m &&& ~~~ twoPow n i

theorem getLsbD_overwriteBit_self {i : ℕ} (hi : i < n) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD i = b := by
  cases b <;> simp [overwriteBit, hi]

@[simp] theorem getElem_overwriteBit_self {i : ℕ} (hi : i < n) (b : Bool)
    (m : BitVec n) : (overwriteBit i b m)[i] = b := by
  cases b <;> simp [overwriteBit]

@[simp] theorem getLsbD_overwriteBit_of_ne {i j : ℕ} (h : j ≠ i) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD j = m.getLsbD j := by
  rcases lt_or_ge j n with hj | hj
  · cases b <;> simp [overwriteBit, h, hj]
  · cases b <;> simp [overwriteBit, getLsbD_of_ge _ _ hj]

/-- Reading an overwritten vector returns the new bit exactly at the selected in-range index. -/
theorem getLsbD_overwriteBit (i j : ℕ) (b : Bool) (m : BitVec n) :
    (overwriteBit i b m).getLsbD j = if j = i ∧ i < n then b else m.getLsbD j := by
  rcases eq_or_ne j i with rfl | h
  · rcases lt_or_ge j n with hj | hj
    · rw [ite_eq_left ⟨rfl, hj⟩]
      exact getLsbD_overwriteBit_self hj b m
    · cases b <;> simp [overwriteBit, getLsbD_of_ge _ _ hj, Nat.not_lt.mpr hj]
  · simp [h]

/-- Overwriting the same position twice keeps only the outer write. -/
@[simp] theorem overwriteBit_overwriteBit (i : ℕ) (b c : Bool) (m : BitVec n) :
    overwriteBit i c (overwriteBit i b m) = overwriteBit i c m :=
  eq_of_getLsbD_eq_iff.mpr fun j _ => by
    simp only [getLsbD_overwriteBit]
    split <;> simp_all

/-- Overwriting a bit with its current value is the identity. -/
@[simp] theorem overwriteBit_getLsbD_self (i : ℕ) (m : BitVec n) :
    overwriteBit i (m.getLsbD i) m = m :=
  eq_of_getLsbD_eq_iff.mpr fun j _ => by
    rw [getLsbD_overwriteBit]
    split <;> simp_all

/-- For `i < n`, swapping the `i`-th bit with the Boolean in a pair `(m, b)` twice
recovers both `m` and `b`. -/
theorem involutive_overwriteBit_pair {i : ℕ} (hi : i < n) :
    Function.Involutive fun p : BitVec n × Bool =>
      (overwriteBit i p.2 p.1, p.1.getLsbD i) := by
  rintro ⟨m, b⟩
  simp [getLsbD_overwriteBit_self hi]

end BitVec
