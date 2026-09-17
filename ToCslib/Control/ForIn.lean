/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Internal.ForIn
public import Init.Data.Vector.Lemmas

/-!
# Effect-free loops over `Option` and `Vector`

Core's `Std.Internal.PureForIn` classes identify the containers whose `for` loop is the loop
over the list `ForIn.toList` computes, which is what the loop specifications of the
weakest-precondition layer and the transport of loops along monad morphisms reduce to. Core
supplies instances for lists, arrays, ranges, slices, and iterators; this file adds `Option`
(a loop of at most one iteration) and `Vector`, whose loop is its array's.
-/

public section

universe u v u₁

namespace Std.Internal

/-- Transport a `forIn'` loop along an equation between its lists, re-typing the membership
proofs of the body. -/
private theorem forIn'_cast {γ : Type u₁} {δ : Type u} {n : Type u → Type v} [Monad n]
    {l₁ l₂ : List γ} (h : l₁ = l₂) (init : δ) (f : (a : γ) → a ∈ l₂ → δ → n (ForInStep δ)) :
    forIn' l₂ init f = forIn' l₁ init fun a ha b => f a (h ▸ ha) b := by
  subst h; rfl

/-! ## `Option` -/

section Option

variable {α : Type u₁}

@[simp]
theorem ForIn.toList_option (o : Option α) : ForIn.toList o = o.toList := by
  apply ForIn.toList_eq_of_forIn_eq
  intro init f
  cases o with
  | none => rfl
  | some a =>
    simp only [Option.toList, List.forIn_cons, List.forIn_nil]
    exact bind_congr fun r => by cases r <;> rfl

instance : LawfulMemForInId (Option α) α where
  mem_toList_iff {a o} := by cases o <;> simp [Option.toList, eq_comm]

instance {m : Type u → Type v} [Monad m] : PureForIn' m (Option α) α where
  forIn'_eq o init f := by
    cases o with
    | none => rfl
    | some a =>
      rw [forIn'_cast (ForIn.toList_option (some a)).symm]
      simp only [Option.toList, List.forIn'_cons, List.forIn'_nil]
      exact bind_congr fun r => by cases r <;> rfl

instance {m : Type u → Type v} [Monad m] : PureForIn m (Option α) α where
  forIn_eq o init f := by
    cases o with
    | none => rfl
    | some a =>
      simp only [ForIn.toList_option, Option.toList, List.forIn_cons, List.forIn_nil]
      exact bind_congr fun r => by cases r <;> rfl

end Option

/-! ## `Vector` -/

section Vector

variable {α : Type u₁} {n : Nat}

@[simp]
theorem ForIn.toList_vector (xs : Vector α n) : ForIn.toList xs = xs.toList := by
  apply ForIn.toList_eq_of_forIn_eq
  intro init f
  cases xs with
  | mk xs h => rw [Vector.forIn_mk, ← Array.forIn_toList]; rfl

instance : LawfulMemForInId (Vector α n) α where
  mem_toList_iff {a xs} := by rw [ForIn.toList_vector, Vector.mem_toList_iff]

instance {m : Type u → Type v} [Monad m] : PureForIn' m (Vector α n) α where
  forIn'_eq xs init f := by
    cases xs with
    | mk xs h =>
      rw [Vector.forIn'_mk, forIn'_cast (l₁ := xs.toList) (ForIn.toList_vector (Vector.mk xs h)).symm,
        Array.forIn'_toList]

instance {m : Type u → Type v} [Monad m] : PureForIn m (Vector α n) α where
  forIn_eq xs init f := by
    cases xs with
    | mk xs h => rw [Vector.forIn_mk, ← Array.forIn_toList, ForIn.toList_vector]; rfl

end Vector

end Std.Internal
