/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Monadic sequencing of `Fin`-indexed families

`Fin.mOfFn n f` runs `f 0`, …, `f (n - 1)` in order and collects the results as a function
`Fin n → α`. It is the function-valued counterpart of Mathlib's `List.Vector.mOfFn`; the pinned
core, Batteries and Mathlib define no monadic `Fin.ofFn`. The body is exposed so that its two
equations, `Fin.mOfFn_zero` and `Fin.mOfFn_succ`, hold by `rfl` for every importer.
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
