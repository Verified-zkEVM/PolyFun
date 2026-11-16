/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.OmegaCompletePartialOrder
public import Mathlib.Order.Fin.Basic

/-!
# Recurrences depending on earlier coordinates

Each coordinate may inspect only its strict prefix. Over a well-founded order of coordinates,
such equations have at most one solution (`Function.UsesPrefix.fixedPoint_unique`); the
coordinates can be `Fin n`, or `ℕ` for a stream. Over `Fin n` the solution is computed by
well-founded recursion. When the coordinate operations are continuous, this solution is also
their least fixed point. The values may themselves contain partial information or errors.
-/

public section

namespace Function

variable {n : Nat} {ι α : Type*}

/-- Compute a finite recurrence using only already computed coordinates. -/
@[expose] def prefixRecursion (step : (i : Fin n) → (Fin i.val → α) → α) (i : Fin n) : α :=
  step i (fun j => prefixRecursion step ⟨j.val, j.isLt.trans i.isLt⟩)
termination_by i.val

/-- Unfold one coordinate without expanding the preceding computations. -/
theorem prefixRecursion_apply (step : (i : Fin n) → (Fin i.val → α) → α) (i : Fin n) :
    prefixRecursion step i =
      step i (fun j => prefixRecursion step ⟨j.val, j.isLt.trans i.isLt⟩) := by
  rw [prefixRecursion]

/-- Coordinate `i` depends only on coordinates strictly before `i`. -/
@[expose] def UsesPrefix [LT ι] (f : (ι → α) → ι → α) : Prop :=
  ∀ (i : ι) (x y : ι → α), (∀ j, j < i → x j = y j) → f x i = f y i

/-- A prefix-dependent system over well-founded coordinates has at most one solution, even with
partial values. -/
theorem UsesPrefix.fixedPoint_unique [LT ι] [WellFoundedLT ι] {f : (ι → α) → ι → α}
    (hf : UsesPrefix f) {x y : ι → α} (hx : f x = x) (hy : f y = y) : x = y := by
  funext i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    rw [← congrFun hx i, ← congrFun hy i]
    exact hf i x y ih

end Function

namespace OmegaCompletePartialOrder.ContinuousHom

variable {n : Nat} {D : Type*} [OmegaCompletePartialOrder D]

/-- Assemble continuous operations on strict prefixes into simultaneous equations. -/
@[expose] def prefixMap (step : (i : Fin n) → (Fin i.val → D) →𝒄 D) :
    (Fin n → D) →𝒄 (Fin n → D) :=
  .ofFun (fun x i => step i (fun j => x ⟨j.val, j.isLt.trans i.isLt⟩))

/-- The assembled equations depend only on earlier coordinates. -/
theorem prefixMap_usesPrefix (step : (i : Fin n) → (Fin i.val → D) →𝒄 D) :
    Function.UsesPrefix (prefixMap step) := by
  intro i x y h
  apply congrArg (step i)
  funext j
  exact h ⟨j.val, j.isLt.trans i.isLt⟩ j.isLt

/-- Well-founded evaluation satisfies the simultaneous equations. -/
theorem prefixMap_prefixRecursion (step : (i : Fin n) → (Fin i.val → D) →𝒄 D) :
    prefixMap step (Function.prefixRecursion (fun i => step i)) =
      Function.prefixRecursion (fun i => step i) := by
  funext i
  exact (Function.prefixRecursion_apply (fun i => step i) i).symm

/-- The least fixed point of finite prefix equations is their computed solution. -/
theorem prefixMap_fix [OrderBot D] (step : (i : Fin n) → (Fin i.val → D) →𝒄 D) :
    (prefixMap step).fix = Function.prefixRecursion (fun i => step i) :=
  (prefixMap_usesPrefix step).fixedPoint_unique (prefixMap step).map_fix
    (prefixMap_prefixRecursion step)

end OmegaCompletePartialOrder.ContinuousHom
