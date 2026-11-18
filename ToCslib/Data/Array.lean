/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Init.Data.Array.Lemmas

/-!
# Reading an array after a write or a push

Core states how `getElem?` reads `Array.setIfInBounds` and `Array.push`, the forms that `simp`
normalizes `Array.set!` and `Array.getD` to. This module adds the remaining reads that array-state
loops need:

* `getD` after `set!`, `setIfInBounds` and `push`, as one `if` each (`Array.getD_set!`,
  `Array.getD_setIfInBounds`, `Array.getD_push`), for rewriting before `simp` normalizes `getD`;
* `getElem!` after `setIfInBounds` and `push` (`Array.getElem!_setIfInBounds`,
  `Array.getElem!_push`), with the `simp` forms for a different index and for an index below the
  size;
* the `simp` attribute on core's `Array.getElem?_push_lt`, so that a push is invisible to reads
  below the old size.
-/

public section

universe u

namespace Array

variable {α : Type u} {xs : Array α} {i j : Nat} {v d : α}

/-- Reading with a default after `setIfInBounds`. -/
theorem getD_setIfInBounds :
    (xs.setIfInBounds i v).getD j d = if i = j ∧ i < xs.size then v else xs.getD j d := by
  simp only [getD_eq_getD_getElem?, getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < xs.size <;> simp [hi]
  · simp [hij]

/-- Reading with a default after `set!`. -/
theorem getD_set! :
    (xs.set! i v).getD j d = if i = j ∧ i < xs.size then v else xs.getD j d :=
  getD_setIfInBounds

/-- Reading with a default after `push`. -/
theorem getD_push : (xs.push v).getD j d = if j = xs.size then v else xs.getD j d := by
  simp only [getD_eq_getD_getElem?, getElem?_push]
  split <;> rfl

@[simp]
theorem getElem!_setIfInBounds_ne [Inhabited α] (h : i ≠ j) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  simp only [getElem!_eq_getD, getD_setIfInBounds, h, false_and, ite_false]

theorem getElem!_setIfInBounds [Inhabited α] :
    (xs.setIfInBounds i v)[j]! = if i = j ∧ i < xs.size then v else xs[j]! := by
  simp only [getElem!_eq_getD, getD_setIfInBounds]

@[simp]
theorem getElem!_push_lt [Inhabited α] (h : j < xs.size) : (xs.push v)[j]! = xs[j]! := by
  simp only [getElem!_eq_getD, getD_push, Nat.ne_of_lt h, ite_false]

theorem getElem!_push [Inhabited α] : (xs.push v)[j]! = if j = xs.size then v else xs[j]! := by
  simp only [getElem!_eq_getD, getD_push]

attribute [simp] getElem?_push_lt

end Array
