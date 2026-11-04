/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Value

/-!
# Charge bounds of loops

A loop over a list whose body stays within a budget per iteration stays within the sum of those
budgets, or `xs.length • B` for a uniform budget `B`. This holds for `List.forM`, `List.mapM`,
`List.foldlM` and `List.forIn`, the forms that `for` loops in `do` blocks elaborate to, both for
structural charge bounds and for worst-case costs.

Early exit in `forIn` only shortens a branch, so the bound is the same. The cost bounds are
inequalities: a branch that ends at a call with no answer never reaches the next iteration.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {ω : Type w} {γ : Type v} {β : Type uB}

section Bound

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
  {c : P.A → ω}

/-- A `forM` loop stays within the sum of the budgets of its iterations. -/
theorem isChargeBound_forM {xs : List γ} {f : γ → FreeM P PUnit} {B : γ → ω}
    (h : ∀ a ∈ xs, IsChargeBound (f a) c (B a)) :
    IsChargeBound (forM xs f) c (xs.map B).sum := by
  induction xs with
  | nil => exact isChargeBound_pure _
  | cons a as ih =>
    rw [List.forM_cons, List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).bind fun _ =>
      ih fun b hb => h b (List.mem_cons_of_mem a hb)

/-- A `forM` loop with a uniform budget per iteration stays within `xs.length • B`. -/
theorem isChargeBound_forM_const {xs : List γ} {f : γ → FreeM P PUnit} {B : ω}
    (h : ∀ a ∈ xs, IsChargeBound (f a) c B) : IsChargeBound (forM xs f) c (xs.length • B) := by
  simpa using isChargeBound_forM (B := fun _ => B) h

/-- A `mapM` loop stays within the sum of the budgets of its iterations. -/
theorem isChargeBound_mapM {xs : List γ} {f : γ → FreeM P β} {B : γ → ω}
    (h : ∀ a ∈ xs, IsChargeBound (f a) c (B a)) :
    IsChargeBound (xs.mapM f) c (xs.map B).sum := by
  induction xs with
  | nil => exact isChargeBound_pure _
  | cons a as ih =>
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    refine (h a List.mem_cons_self).bind fun _ => ?_
    rw [LawfulMonad.bind_pure_comp, isChargeBound_map_iff']
    exact ih fun b hb => h b (List.mem_cons_of_mem a hb)

/-- A `foldlM` loop whose step stays within `B` from every accumulator stays within
`xs.length • B`. -/
theorem isChargeBound_foldlM {xs : List γ} {f : β → γ → FreeM P β} {B : ω}
    (h : ∀ b, ∀ a ∈ xs, IsChargeBound (f b a) c B) (init : β) :
    IsChargeBound (xs.foldlM f init) c (xs.length • B) := by
  induction xs generalizing init with
  | nil => exact isChargeBound_pure _
  | cons a as ih =>
    rw [List.foldlM_cons, List.length_cons, succ_nsmul']
    exact (h init a List.mem_cons_self).bind fun b =>
      ih (fun b' a' ha' => h b' a' (List.mem_cons_of_mem a ha')) b

/-- A `forIn` loop whose body stays within `B` from every state stays within `xs.length • B`.
Exiting early only shortens a branch. -/
theorem isChargeBound_forIn {xs : List γ} {f : γ → β → FreeM P (ForInStep β)} {B : ω}
    (h : ∀ a ∈ xs, ∀ b, IsChargeBound (f a b) c B) (init : β) :
    IsChargeBound (forIn xs init f) c (xs.length • B) := by
  induction xs generalizing init with
  | nil => exact isChargeBound_pure _
  | cons a as ih =>
    rw [List.forIn_cons, List.length_cons, succ_nsmul']
    refine (h a List.mem_cons_self init).bind fun r => ?_
    cases r with
    | done b => exact isChargeBound_pure _
    | yield b => exact ih (fun a' ha' => h a' (List.mem_cons_of_mem a ha')) b

end Bound

section Cost

variable [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
  {c : P.A → ω}

omit [CanonicallyOrderedAdd ω] in
/-- A sequence whose continuation ignores the result costs at most the sum of the parts. -/
theorem cost_bind_const_le {α : Type v} {δ : Type v} (x : FreeM P α) (y : FreeM P δ) :
    cost c (x >>= fun _ => y) ≤ cost c x + cost c y :=
  (cost_bind_le x _).trans (add_le_add le_rfl (iSup_le fun _ => le_rfl))

omit [CanonicallyOrderedAdd ω] in
/-- A `forM` loop costs at most the sum of the costs of its iterations. -/
theorem cost_forM_le (xs : List γ) (f : γ → FreeM P PUnit) :
    cost c (forM xs f) ≤ (xs.map fun a => cost c (f a)).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    rw [List.forM_cons, List.map_cons, List.sum_cons]
    exact (cost_bind_const_le _ _).trans (add_le_add le_rfl ih)

/-- A `forIn` loop whose body costs at most `B` from every state costs at most
`xs.length • B`. -/
theorem cost_forIn_le {xs : List γ} {f : γ → β → FreeM P (ForInStep β)} {B : ω}
    (h : ∀ a ∈ xs, ∀ b, cost c (f a b) ≤ B) (init : β) :
    cost c (forIn xs init f) ≤ xs.length • B := by
  induction xs generalizing init with
  | nil => simp
  | cons a as ih =>
    rw [List.forIn_cons, List.length_cons, succ_nsmul']
    refine (cost_bind_le _ _).trans (add_le_add (h a List.mem_cons_self init) (iSup_le ?_))
    rintro (b | b)
    · simp
    · exact ih (fun a' ha' => h a' (List.mem_cons_of_mem a ha')) b

end Cost

end PFunctor.FreeM
