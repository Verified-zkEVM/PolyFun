/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Fin.VecNotation

/-!
# Direct compilation of finite case analysis

Core defines `Fin.cases` by induction. Strict evaluation can compute discarded induction
hypotheses at each level of a nested `Fin.cons` chain, repeating work exponentially in the
index. The `@[csimp]` lemmas compile `Fin.cases`, `Fin.cons`, and `Matrix.vecCons` using a
direct match on the index. Looking up entry `i` then follows `i.val` tails and selects the
head. This counts the steps to select an entry in the chain. Computing its values may take
additional work.

Import this module where definitions using finite case analysis or vector notation are compiled,
as `ToCslib.Data.Fin.MOfFn` does. Proofs use the ordinary computation equations of `Fin.cases`.
-/

public section

-- upstream candidate: compiled case analysis for core's `Fin.cases` and Mathlib's wrappers.

namespace Fin

universe u

/-- Finite case analysis with direct pattern matching on the underlying natural. -/
@[expose] def casesDirect {n : Nat} {motive : Fin (n + 1) → Sort u}
    (zero : motive 0) (succ : ∀ i : Fin n, motive i.succ) :
    (i : Fin (n + 1)) → motive i
  | ⟨0, _⟩ => zero
  | ⟨i + 1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Compile finite case analysis without evaluating unused induction hypotheses. -/
@[csimp] theorem cases_eq_casesDirect : @Fin.cases = @casesDirect := by
  funext n motive zero succ i
  rcases i with ⟨i, hi⟩
  cases i <;> rfl

/-- Dependent tuple construction using direct case selection. -/
@[expose] def consDirect {n : Nat} {α : Fin (n + 1) → Sort u}
    (x : α 0) (xs : ∀ i : Fin n, α i.succ) : ∀ i, α i := casesDirect x xs

/-- Rewriting the wrapper is necessary when its imported implementation is inlined later. -/
@[csimp] theorem cons_eq_consDirect : @Fin.cons = @consDirect := by
  funext n α x xs i
  change Fin.cases x xs i = casesDirect x xs i
  rw [cases_eq_casesDirect]

end Fin

namespace Matrix

universe u

/-- Nondependent vector construction with direct case selection. -/
@[expose] def vecConsDirect {α : Type u} {n : Nat} (x : α) (xs : Fin n → α) :
    Fin (n + 1) → α := Fin.casesDirect x xs

/-- Compile vector notation without the imported induction-based wrapper. -/
@[csimp] theorem vecCons_eq_vecConsDirect : @vecCons = @vecConsDirect := by
  funext α n x xs i
  change Fin.cases (motive := fun _ => α) x xs i =
    Fin.casesDirect (motive := fun _ => α) x xs i
  rw [Fin.cases_eq_casesDirect]

end Matrix
