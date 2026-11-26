/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Support

/-!
# Membership in the support of a program that is expensive to evaluate

`FreeM.CanReturn` is inductive, so neither the kernel nor the elaborator evaluates a program to
compare two memberships in its support. The program `big n` below decides its head constructor by
matching on `2 ^ n`. At `n = 2 ^ 32`, evaluating it would compute `2 ^ (2 ^ 32)`, which the kernel
refuses to do.

Each theorem compares `a ∈ support small` with `a ∈ support (big (2 ^ 32))`, where `small`
unfolds to `big (2 ^ 32)` in one step: by passing a hypothesis to a lemma, by `unfold`, and by a
hypothesis whose type is the expected type exactly. Comparing the two memberships must reduce to
comparing the two programs, without evaluating either one.
-/

@[expose] public section

namespace PolyFunTest.SupportKernel

open PFunctor MonadAttach

/-- Operations carry a size `n` and have `n + 1` answers. -/
def Sized : PFunctor := ⟨ℕ, fun n => Fin (n + 1)⟩

/-- A program whose head constructor depends on `2 ^ n`. -/
def big (n : ℕ) : FreeM Sized ℕ :=
  match 2 ^ n with
  | 0 => .pure 0
  | k + 1 => .liftBind k fun _ => .pure 5

/-- `big (2 ^ 32)`, one delta step away. -/
def small : FreeM Sized ℕ := big (2 ^ 32)

/-- The possible outputs of `big n`, for an abstract `n`. -/
theorem mem_support_big (n a : ℕ) (h : a ∈ support (big n)) : a = 0 ∨ a = 5 := by
  unfold big at h
  split at h
  · exact .inl (FreeM.canReturn_pure_iff.mp h)
  · obtain ⟨_, h⟩ := FreeM.mem_support_liftBind.mp h
    exact .inr (FreeM.canReturn_pure_iff.mp h)

/-- Passing `h : a ∈ support small` where `a ∈ support (big (2 ^ 32))` is expected. -/
theorem mem_support_small (a : ℕ) (h : a ∈ support small) : a = 0 ∨ a = 5 :=
  mem_support_big (2 ^ 32) a h

/-- `unfold` changes the goal by definitional equality. -/
theorem mem_support_small_of_unfold (a : ℕ) : a ∈ support small → a = 0 ∨ a = 5 := by
  unfold small
  exact mem_support_big _ a

/-- A hypothesis whose type is the expected type, passed to a lemma about `small`. -/
example (a : ℕ) (h : a ∈ support small) : a = 0 ∨ a = 5 :=
  mem_support_small a h

end PolyFunTest.SupportKernel
