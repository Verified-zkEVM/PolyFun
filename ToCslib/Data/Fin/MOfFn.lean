/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Data.Fin.Cases

/-!
# Monadic sequencing of `Fin`-indexed families

`Fin.mOfFn n f` sequences the computations `f i` in increasing index order and collects their
results as a function `Fin n → α`. It is the function-valued counterpart of Mathlib's
`List.Vector.mOfFn`. The successor equation binds `f 0` before sequencing the tail, so in
`Option` the first `none` stops the traversal. Both `Fin.mOfFn_zero` and `Fin.mOfFn_succ`
hold by `rfl` for importers.

The result is a chain of `Fin.cons`. The compiler simplifications from `ToCslib.Data.Fin.Cases`
let a lookup follow `i.val` tails to retrieve the value collected at index `i`.
-/

public section

universe u v

namespace Fin

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- Run a `Fin n`-indexed family of monadic computations in index order and collect the results
as a function on `Fin n`. -/
@[expose]
def mOfFn : (n : ℕ) → (Fin n → m α) → m (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← mOfFn n fun i => f i.succ
    pure (Fin.cons a rest)

@[simp]
theorem mOfFn_zero (f : Fin 0 → m α) : mOfFn 0 f = pure Fin.elim0 := rfl

theorem mOfFn_succ (n : ℕ) (f : Fin (n + 1) → m α) :
    mOfFn (n + 1) f = (do
      let a ← f 0
      let rest ← mOfFn n fun i => f i.succ
      pure (Fin.cons a rest)) := rfl

/-- Sequencing a family of pure computations returns the family of their values. -/
@[simp]
theorem mOfFn_pure [LawfulMonad m] (n : ℕ) (f : Fin n → α) :
    mOfFn n (fun i => (pure (f i) : m α)) = pure f := by
  induction n with
  | zero => exact congrArg pure (funext fun i => i.elim0)
  | succ n ih =>
    rw [mOfFn_succ, pure_bind, ih fun i => f i.succ, pure_bind]
    exact congrArg pure (Fin.cons_self_tail f)

end Fin
