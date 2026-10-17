/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import ToCslib.Data.Fin.Cases

/-!
# Direct finite case API

Dependent result types and both boundary cases remain definitionally usable.
Compiled large-vector checks live in the downstream execution consumer.
-/

example {n : Nat} {α : Fin (n + 1) → Type} (x : α 0) (xs : ∀ i : Fin n, α i.succ) :
    Fin.casesDirect x xs 0 = x := rfl

example {n : Nat} {α : Fin (n + 1) → Type} (x : α 0) (xs : ∀ i : Fin n, α i.succ)
    (i : Fin n) : Fin.casesDirect x xs i.succ = xs i := rfl

example {n : Nat} {α : Type} (x : α) (xs : Fin n → α) :
    Matrix.vecCons x xs = Matrix.vecConsDirect x xs := by
  rw [Matrix.vecCons_eq_vecConsDirect]
