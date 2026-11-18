/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Control.Loop.Basic
public import ToCslib.Data.Array
public import ToCslib.Data.ByteArray

/-!
# Loops that fill or build arrays

After `ToCslib.Control.Loop.Basic` turns a yield-only loop into a left fold, two loop shapes
remain to be identified with a functional specification.

* **Fills.** A loop that writes `v x` at position `p x` for each `x` of a list, through
  `Array.set!`, keeps the size of the array (`Array.size_foldl_set!`), leaves every position that
  it does not write unchanged (`Array.getElem?_foldl_set!_of_forall_ne`), and, when the positions
  are distinct, holds `v x` at `p x` (`Array.getElem?_foldl_set!_of_mem`). Writing `f i` at every
  `i < n` of an array of size `n` gives `Array.ofFn` (`Array.foldl_set!_range_eq_ofFn`), and so
  does writing `f i j` at `i * n + j` in two nested loops (`Array.foldl_foldl_set!_range_eq_ofFn`).
* **Builders.** A loop that pushes or appends to an accumulator appends the mapped or
  concatenated list (`Array.foldl_push_eq_append`, `Array.foldl_append_eq_append`, and the nested
  `Array.foldl_foldl_push_eq_append`), with the same statements for byte arrays and lists.

The `loop_norm` simp set gains the rewrites from `List.range' 0 n` to `List.range n` and from a
loop over a byte array to the loop over its list of bytes.
-/

public section

universe u v

variable {α : Type u} {ι : Type v} {κ : Type v}

/-- `List.range' 0 n` is `List.range n`. -/
@[loop_norm]
theorem List.range'_zero_eq_range (n : Nat) : List.range' 0 n = List.range n :=
  List.range_eq_range'.symm

attribute [loop_norm] ByteArray.forIn_eq_forIn_toList

namespace Array

/-! ## Fills -/

/-- Writing through `setIfInBounds` in a loop keeps the size. -/
@[simp]
theorem size_foldl_setIfInBounds (l : List ι) (p : ι → Nat) (v : ι → α) (a : Array α) :
    (l.foldl (fun a x => a.setIfInBounds (p x) (v x)) a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih, size_setIfInBounds]

/-- Writing through `set!` in a loop keeps the size. -/
theorem size_foldl_set! (l : List ι) (p : ι → Nat) (v : ι → α) (a : Array α) :
    (l.foldl (fun a x => a.set! (p x) (v x)) a).size = a.size :=
  size_foldl_setIfInBounds l p v a

/-- A position that no step of the loop writes keeps its value. -/
theorem getElem?_foldl_set!_of_forall_ne {l : List ι} {p : ι → Nat} {j : Nat} (v : ι → α)
    (a : Array α) (h : ∀ x ∈ l, p x ≠ j) :
    (l.foldl (fun a x => a.set! (p x) (v x)) a)[j]? = a[j]? := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih _ fun y hy => h y (List.mem_cons_of_mem x hy), set!_eq_setIfInBounds,
      getElem?_setIfInBounds_ne (h x List.mem_cons_self)]

/-- When the loop writes at distinct positions, the position `p x` of an element `x` holds
`v x`, provided it is in bounds. -/
theorem getElem?_foldl_set!_of_mem {l : List ι} {p : ι → Nat} {x : ι} (v : ι → α) (a : Array α)
    (hnd : (l.map p).Nodup) (hx : x ∈ l) (hlt : p x < a.size) :
    (l.foldl (fun a x => a.set! (p x) (v x)) a)[p x]? = some (v x) := by
  induction l generalizing a with
  | nil => cases hx
  | cons y l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [getElem?_foldl_set!_of_forall_ne v _ fun z hz hzx =>
          hnd.1 (by rw [← hzx]; exact List.mem_map_of_mem hz), set!_eq_setIfInBounds,
        getElem?_setIfInBounds_self_of_lt hlt]
    · exact ih _ hnd.2 hx (by rw [size_set!]; exact hlt)

/-- Writing `f i` at every position `i < n` of an array of size `n` gives `Array.ofFn`. -/
theorem foldl_set!_range_eq_ofFn {n : Nat} (f : Nat → α) {a : Array α} (ha : a.size = n) :
    (List.range n).foldl (fun a i => a.set! i (f i)) a = Array.ofFn fun i : Fin n => f i := by
  refine ext_getElem? fun j => ?_
  rw [getElem?_ofFn]
  by_cases hj : j < n
  · rw [dite_eq_left hj]
    exact getElem?_foldl_set!_of_mem (p := id) f a (by simpa using List.nodup_range)
      (List.mem_range.2 hj) (ha ▸ hj)
  · rw [dite_eq_right hj]
    have := getElem?_foldl_set!_of_forall_ne (l := List.range n) (p := id) (j := j) f a
      fun i hi hij => hj (by rw [← hij]; exact List.mem_range.1 hi)
    exact this.trans (getElem?_eq_none (by omega))

/-- The positions `i * n + j` for `i < k` and `j < n`, in order, are the positions below
`k * n`. -/
private theorem flatMap_range_map_mul_add (k n : Nat) :
    (List.range k).flatMap (fun i => (List.range n).map fun j => i * n + j) =
      List.range (k * n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add]
    simp

/-- Writing `f i j` at position `i * n + j` for every `i < k` and `j < n`, in two nested loops,
of an array of size `k * n` gives `Array.ofFn`. -/
theorem foldl_foldl_set!_range_eq_ofFn {k n : Nat} (f : Nat → Nat → α) {a : Array α}
    (ha : a.size = k * n) :
    (List.range k).foldl (fun a i => (List.range n).foldl (fun a j => a.set! (i * n + j) (f i j)) a)
      a = Array.ofFn fun t : Fin (k * n) => f (t / n) (t % n) := by
  let l := (List.range k).flatMap fun i => (List.range n).map fun j => (i, j)
  have hl : (List.range k).foldl
      (fun a i => (List.range n).foldl (fun a j => a.set! (i * n + j) (f i j)) a) a =
      l.foldl (fun a x => a.set! (x.1 * n + x.2) (f x.1 x.2)) a := by
    simp only [l, List.foldl_flatMap, List.foldl_map]
  have hmap : l.map (fun x => x.1 * n + x.2) = List.range (k * n) := by
    simp only [l, List.map_flatMap, List.map_map, Function.comp_def]
    exact flatMap_range_map_mul_add k n
  rw [hl]
  refine ext_getElem? fun t => ?_
  rw [getElem?_ofFn]
  by_cases ht : t < k * n
  · rw [dite_eq_left ht]
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at ht
    have hx : (t / n, t % n) ∈ l := by
      simp only [l, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
      exact ⟨t / n, (Nat.div_lt_iff_lt_mul hn).2 ht, t % n, Nat.mod_lt t hn, rfl, rfl⟩
    have hp : t / n * n + t % n = t := by rw [Nat.mul_comm]; exact Nat.div_add_mod t n
    have := getElem?_foldl_set!_of_mem (p := fun x => x.1 * n + x.2) (fun x => f x.1 x.2) a
      (hmap ▸ List.nodup_range) hx (by simp only [hp, ha]; exact ht)
    simpa only [hp] using this
  · rw [dite_eq_right ht, getElem?_foldl_set!_of_forall_ne (p := fun x : Nat × Nat => x.1 * n + x.2)
      _ a fun x hx hxt => ht (by
        rw [← hxt, ← List.mem_range, ← hmap]
        exact List.mem_map_of_mem hx),
      getElem?_eq_none (by omega)]

end Array

namespace List

/-- Appending the array of `g x` for each element `x` of a list appends the array of
`l.flatMap g`. -/
theorem foldl_append_toArray_eq_append (l : List ι) (g : ι → List α) (acc : Array α) :
    l.foldl (fun acc x => acc ++ (g x).toArray) acc = acc ++ (l.flatMap g).toArray := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => rw [foldl_cons, ih, flatMap_cons, ← append_toArray, Array.append_assoc]

/-- Two nested loops that push `f i j` for each `j` of `g i`, for each `i` of a list, append the
concatenation of the mapped lists. -/
theorem foldl_foldl_push_eq_append (l : List ι) (g : ι → List κ) (f : ι → κ → α)
    (acc : Array α) :
    l.foldl (fun acc i => (g i).foldl (fun acc j => acc.push (f i j)) acc) acc =
      acc ++ (l.flatMap fun i => (g i).map (f i)).toArray := by
  simp only [foldl_push_eq_append]
  exact foldl_append_toArray_eq_append l (fun i => (g i).map (f i)) acc

end List

namespace ByteArray

/-- Pushing `f x` for each element `x` of a list appends the mapped list. -/
theorem foldl_push_eq_append (l : List ι) (f : ι → UInt8) (acc : ByteArray) :
    l.foldl (fun acc x => acc.push (f x)) acc = acc ++ (l.map f).toByteArray := by
  refine ByteArray.ext ?_
  rw [data_append, List.data_toByteArray, ← List.foldl_push_eq_append]
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih => exact ih (acc.push (f x))

/-- Appending `g x` for each element `x` of a list appends the concatenation of the `g x`. -/
theorem foldl_append_eq_append (l : List ι) (g : ι → ByteArray) (acc : ByteArray) :
    l.foldl (fun acc x => acc ++ g x) acc =
      acc ++ (l.flatMap fun x => (g x).toList).toByteArray := by
  refine ByteArray.ext ?_
  rw [data_append, List.data_toByteArray]
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, data_append, List.flatMap_cons, ← List.append_toArray,
      toList_eq_data_toList, Array.toArray_toList, Array.append_assoc]

end ByteArray
