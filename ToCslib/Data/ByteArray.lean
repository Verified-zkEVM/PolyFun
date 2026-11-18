/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Init.Data.ByteArray.Lemmas
public import Std.Internal.ForIn.Basic

/-!
# Byte arrays: reads after writes, and their `for` loop

Core states how `getElem!` reads `ByteArray.set!` and `ByteArray.push`. This module adds the
`getElem?` reads (`ByteArray.getElem?_set!`, `ByteArray.getElem?_push`, and their special cases)
and the `simp` attribute on core's `ByteArray.getElem!_push_lt`. When `simp` can prove an index in
bounds, it already rewrites a `getElem?` read there to a `getElem` read, which core's
`ByteArray.getElem_set!_self` handles. The `simp` lemmas here are `ByteArray.getElem?_set!_ne`
and `ByteArray.getElem?_push_lt`.

`ByteArray.forIn` counts a natural number down from the size and reads the byte at
`size - 1 - i`, so it visits the bytes in increasing order. `ByteArray.forIn_eq_forIn_toList`
states that it is the loop over `ByteArray.toList`, and `ByteArray.forIn_eq_forIn_data` that it
is the loop over the underlying array. The `Std.Internal.PureForIn` instance follows, so the
container-generic loop lemmas, and core's loop specification `Std.WP.Spec.forIn_pure`, apply to
`for b in bytes do …`. Core gives `ByteArray` no `Membership` and no `ForIn'` instance, so
`for h : b in bytes do …` does not elaborate and there is no `PureForIn'` instance to give.
-/

public section

universe u v

namespace ByteArray

variable {b : ByteArray} {i j : Nat} {v : UInt8}

/-! ## Reads after writes -/

theorem getElem?_set! :
    (b.set! i v)[j]? = if i = j then if i < b.size then some v else none else b[j]? := by
  by_cases hj : j < b.size
  · rw [getElem?_pos (b.set! i v) j (by rw [size_set!]; exact hj), getElem?_pos b j hj]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left hj, getElem_set!_self b i v hj]
    · rw [ite_eq_right hij, getElem_set!_ne b i j v hij hj]
  · rw [getElem?_neg (b.set! i v) j (by rw [size_set!]; exact hj), getElem?_neg b j hj]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_right hj]
    · rw [ite_eq_right hij]

theorem getElem?_set!_self_of_lt (h : i < b.size) : (b.set! i v)[i]? = some v := by
  rw [getElem?_set!, ite_eq_left rfl, ite_eq_left h]

@[simp]
theorem getElem?_set!_ne (h : i ≠ j) : (b.set! i v)[j]? = b[j]? := by
  rw [getElem?_set!, ite_eq_right h]

theorem getElem?_push : (b.push v)[j]? = if j = b.size then some v else b[j]? := by
  by_cases hj : j < b.size
  · rw [getElem?_pos (b.push v) j (by rw [size_push]; omega), getElem?_pos b j hj,
      ite_eq_right (Nat.ne_of_lt hj), Option.some_inj]
    exact Array.getElem_push_lt hj
  · by_cases hje : j = b.size
    · subst hje
      rw [getElem?_pos (b.push v) b.size (by rw [size_push]; omega), ite_eq_left rfl,
        Option.some_inj]
      exact Array.getElem_push_eq
    · rw [getElem?_neg (b.push v) j (by rw [size_push]; omega), ite_eq_right hje,
        getElem?_neg b j hj]

theorem getElem?_push_size : (b.push v)[b.size]? = some v := by
  rw [getElem?_push, ite_eq_left rfl]

@[simp]
theorem getElem?_push_lt (h : j < b.size) : (b.push v)[j]? = b[j]? := by
  rw [getElem?_push, ite_eq_right (Nat.ne_of_lt h)]

attribute [simp] getElem!_push_lt

/-! ## The `for` loop -/

/-- `ByteArray.toList` lists the bytes of the underlying array. -/
theorem toList_eq_data_toList (b : ByteArray) : b.toList = b.data.toList := by
  suffices h : ∀ i r, toList.loop b i r = r.reverse ++ b.data.toList.drop i by
    change toList.loop b 0 [] = _
    rw [h, List.reverse_nil, List.nil_append, List.drop_zero]
  intro i r
  fun_induction toList.loop b i r with
  | case1 i r h ih =>
    rw [ih, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.drop_eq_getElem_cons (l := b.data.toList) (i := i) (by simpa using h)]
    simp [get!, getElem!_pos b.data i h]
  | case2 i r h =>
    rw [List.drop_eq_nil_of_le (by simp; omega), List.append_nil]

/-- The reference loop of `ByteArray.forIn`, started with `i` bytes left, is the loop over the
last `i` bytes. -/
private theorem forIn_loop_eq {m : Type u → Type v} {β : Type u} [Monad m] (as : ByteArray)
    (f : UInt8 → β → m (ForInStep β)) :
    ∀ (i : Nat) (h : i ≤ as.size) (b : β),
      ByteArray.forIn.loop as f i h b = forIn (as.data.toList.drop (as.size - i)) b f
  | 0, h, b => by
    rw [ByteArray.forIn.loop, Nat.sub_zero, List.drop_eq_nil_of_le (by simp)]; rfl
  | i + 1, h, b => by
    rw [ByteArray.forIn.loop, List.drop_eq_getElem_cons (by simp; omega), List.forIn_cons]
    have e : as.size - (i + 1) = as.size - 1 - i := by omega
    simp only [e]
    refine bind_congr fun r => ?_
    cases r with
    | done b => rfl
    | yield b =>
      dsimp only
      rw [forIn_loop_eq as f i (Nat.le_of_succ_le h) b]
      congr 2
      omega

/-- A `for` loop over a byte array is the loop over its underlying array. -/
theorem forIn_eq_forIn_data {m : Type u → Type v} {β : Type u} [Monad m] (b : ByteArray)
    (init : β) (f : UInt8 → β → m (ForInStep β)) :
    forIn b init f = forIn b.data init f := by
  change ByteArray.forIn.loop b f b.size (Nat.le_refl _) init = _
  rw [forIn_loop_eq, Nat.sub_self, List.drop_zero, Array.forIn_toList]

/-- A `for` loop over a byte array is the loop over its list of bytes. -/
theorem forIn_eq_forIn_toList {m : Type u → Type v} {β : Type u} [Monad m] (b : ByteArray)
    (init : β) (f : UInt8 → β → m (ForInStep β)) :
    forIn b init f = forIn b.toList init f := by
  rw [forIn_eq_forIn_data, toList_eq_data_toList, Array.forIn_toList]

end ByteArray

namespace Std.Internal

@[simp]
theorem ForIn.toList_byteArray (b : ByteArray) : ForIn.toList b = b.toList :=
  ForIn.toList_eq_of_forIn_eq fun init f => ByteArray.forIn_eq_forIn_toList b init f

instance {m : Type u → Type v} [Monad m] : PureForIn m ByteArray UInt8 where
  forIn_eq b init f := by rw [ForIn.toList_byteArray, ByteArray.forIn_eq_forIn_toList]

end Std.Internal
