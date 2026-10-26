/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Indexed
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Sequencing a dependent tuple of two-index programs

`FreeM₂.seqPi f` runs the programs `f 0, …, f (k - 1)` in order, each starting and ending at
the same state, and returns the dependent tuple of their results. Its two equations are
definitional: the empty tuple returns at once (`seqPi_zero`), and a tuple of positive length
binds its head, then the sequenced tail, and returns their `Fin.cons` (`seqPi_succ`).
`seqPi_unique` identifies every operation satisfying these two equations with `seqPi`.

The recursion is not a dependent left fold such as Batteries' `Fin.dfoldlM`: that fold extends
an accumulator after each step, so its tree associates the binds the other way and agrees with
`seqPi` only up to bind associativity.
-/

@[expose] public section

universe uI uA uB v

namespace IPFunctor.FreeM₂

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {s : I}

/-- Run `f 0, …, f (k - 1)` in order and return the dependent tuple of their results. -/
def seqPi : {k : ℕ} → {β : Fin k → Type v} → ((i : Fin k) → FreeM₂ P s s (β i)) →
    FreeM₂ P s s ((i : Fin k) → β i)
  | 0, _, _ => FreeM₂.pure fun i => i.elim0
  | _ + 1, _, f => (f 0).bind fun b => (seqPi fun i => f i.succ).bind fun bs =>
      FreeM₂.pure (Fin.cons b bs)

@[simp]
theorem seqPi_zero {β : Fin 0 → Type v} (f : (i : Fin 0) → FreeM₂ P s s (β i)) :
    seqPi f = FreeM₂.pure fun i => i.elim0 :=
  rfl

theorem seqPi_succ {k : ℕ} {β : Fin (k + 1) → Type v}
    (f : (i : Fin (k + 1)) → FreeM₂ P s s (β i)) :
    seqPi f = (f 0).bind fun b => (seqPi fun i => f i.succ).bind fun bs =>
      FreeM₂.pure (Fin.cons b bs) :=
  rfl

/-- An operation with the two equations of `seqPi` is `seqPi`. -/
theorem seqPi_unique
    (g : ∀ {k : ℕ} {β : Fin k → Type v}, ((i : Fin k) → FreeM₂ P s s (β i)) →
      FreeM₂ P s s ((i : Fin k) → β i))
    (hzero : ∀ {β : Fin 0 → Type v} (f : (i : Fin 0) → FreeM₂ P s s (β i)),
      g f = FreeM₂.pure fun i => i.elim0)
    (hsucc : ∀ {k : ℕ} {β : Fin (k + 1) → Type v}
      (f : (i : Fin (k + 1)) → FreeM₂ P s s (β i)),
      g f = (f 0).bind fun b => (g fun i => f i.succ).bind fun bs =>
        FreeM₂.pure (Fin.cons b bs))
    {k : ℕ} {β : Fin k → Type v} (f : (i : Fin k) → FreeM₂ P s s (β i)) :
    g f = seqPi f := by
  induction k with
  | zero => exact hzero f
  | succ k ih => rw [hsucc, seqPi_succ, ih]

end IPFunctor.FreeM₂
