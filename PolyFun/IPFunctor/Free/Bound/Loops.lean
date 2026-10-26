/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Bound
public import PolyFun.IPFunctor.Free.Tuple
public import Batteries.Data.Fin.Fold
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Resource bounds for loops of two-index programs

The programs `FreeM₂ P s s α` that end at their start state can be sequenced by any monad
structure whose `pure` and `bind` are those of `FreeM₂` (`FreeM₂.IsDiagonalMonad`). Different
developments may declare different such structures, for instance with a different `map`, so
the laws here take the structure as an argument rather than fixing an instance.

Through such a structure, roll bounds compose along the two standard loops:
* `List.foldlM`, a left fold of a step program over a list;
* Batteries' `Fin.dfoldlM`, the dependent left fold over `Fin n` whose accumulator type varies
  with the position.

The dependent tuple sequencer `FreeM₂.seqPi` uses `FreeM₂.bind` and `FreeM₂.pure` directly and
needs no monad structure; `isRollBound_seqPi` and its specializations bound it the same way.

The generic laws `isRollBound_foldlM` and `isRollBound_dfoldlM` combine the per-step budgets
with the same side conditions as `FreeM₂.isRollBound_bind`. Their specializations bound charge
by the sum of the per-step budgets, or by the number of steps times a uniform budget, and
preserve a predicate on every rolled shape.
-/

public section

universe uI uA uB v

namespace IPFunctor.FreeM₂

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {s : I}

/-- A monad structure on the programs that end at their start state, whose `pure` and `bind`
are those of `FreeM₂`. Its `map` and sequencing operations are unconstrained. -/
structure IsDiagonalMonad (inst : Monad (FreeM₂.{uI, uA, uB, v} P s s)) : Prop where
  /-- The monadic `pure` is `FreeM₂.pure`. -/
  pure_eq : ∀ {α : Type v} (a : α), @Pure.pure _ inst.toPure _ a = FreeM₂.pure a
  /-- The monadic bind is `FreeM₂.bind`. -/
  bind_eq : ∀ {α β : Type v} (x : FreeM₂ P s s α) (g : α → FreeM₂ P s s β),
    x >>= g = x.bind g

variable {inst : Monad (FreeM₂.{uI, uA, uB, v} P s s)} {B : Type*}
  {canRoll : (s : I) → P.A s → B → Prop} {cost : (s : I) → P.A s → B → B}

/-! ## Left folds over lists -/

section List

variable {σ : Type v} {ε : Type*} {f : σ → ε → FreeM₂ P s s σ}

/-- Roll bounds compose along a left fold over a list, with the side conditions of
`FreeM₂.isRollBound_bind`. Step `e` is bounded by `budget e`, and the fold by those budgets
combined in list order, associated to the right, with final budget `z`. -/
theorem isRollBound_foldlM (hm : IsDiagonalMonad inst) (combine : B → B → B)
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    (budget : ε → B) (z : B) (hf : ∀ acc e, (f acc e).IsRollBound (budget e) canRoll cost)
    (l : List ε) (init : σ) :
    (l.foldlM f init).IsRollBound (l.foldr (fun e b => combine (budget e) b) z)
      canRoll cost := by
  induction l generalizing init with
  | nil =>
      rw [List.foldlM_nil, hm.pure_eq]
      exact isRollBound_pure _ _
  | cons e l ih =>
      rw [List.foldlM_cons, hm.bind_eq, List.foldr_cons]
      exact isRollBound_bind combine h_can h_cost (hf init e) ih

variable {c : (s : I) → P.A s → ℕ}

/-- Charge bounds add along a left fold over a list. -/
theorem isChargeBound_foldlM (hm : IsDiagonalMonad inst) (b : ε → ℕ)
    (hf : ∀ acc e, (f acc e).IsChargeBound c (b e)) (l : List ε) (init : σ) :
    (l.foldlM f init).IsChargeBound c (l.map b).sum := by
  have h := isRollBound_foldlM hm (· + ·) (by grind) (by grind) b 0 hf l init
  rwa [← List.foldr_map, ← List.sum_eq_foldr] at h

/-- Steps within a common charge budget `k` give a left fold within `l.length * k`. -/
theorem isChargeBound_foldlM_of_forall (hm : IsDiagonalMonad inst) {k : ℕ}
    (hf : ∀ acc e, (f acc e).IsChargeBound c k) (l : List ε) (init : σ) :
    (l.foldlM f init).IsChargeBound c (l.length * k) := by
  simpa using isChargeBound_foldlM hm (fun _ => k) hf l init

/-- A predicate on every rolled shape is preserved by a left fold over a list. The predicate is
the roll bound with the unit budget, check `p` and the identity cost. -/
theorem isRollBound_foldlM_unit (hm : IsDiagonalMonad inst) {p : (s : I) → P.A s → Prop}
    (hf : ∀ acc e, (f acc e).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b))
    (l : List ε) (init : σ) :
    (l.foldlM f init).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b) :=
  isRollBound_foldlM hm (fun _ _ => ()) (fun _ _ _ _ _ h => ⟨h, h⟩)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) (fun _ => ()) () hf l init

end List

/-! ## Dependent left folds over `Fin n` -/

section Fin

private theorem foldr_add_eq_sum {m : ℕ} (b : Fin m → ℕ) :
    Fin.foldr m (fun i k => b i + k) 0 = ∑ i, b i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Fin.foldr_succ, Fin.sum_univ_succ, ih]

/-- Roll bounds compose along the dependent left fold `Fin.dfoldlM`, with the side conditions
of `FreeM₂.isRollBound_bind`. Step `i` is bounded by `budget i`, and the fold by those budgets
combined in index order, associated to the right, with final budget `z`. -/
theorem isRollBound_dfoldlM (hm : IsDiagonalMonad inst) (combine : B → B → B)
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    {n : ℕ} {α : Fin (n + 1) → Type v} (budget : Fin n → B) (z : B)
    {f : (i : Fin n) → α i.castSucc → FreeM₂ P s s (α i.succ)}
    (hf : ∀ i x, (f i x).IsRollBound (budget i) canRoll cost) (init : α 0) :
    (Fin.dfoldlM n α f init).IsRollBound (Fin.foldr n (fun i b => combine (budget i) b) z)
      canRoll cost := by
  induction n with
  | zero =>
      rw [Fin.dfoldlM_zero, hm.pure_eq]
      exact isRollBound_pure _ _
  | succ n ih =>
      rw [Fin.dfoldlM_succ, hm.bind_eq, Fin.foldr_succ]
      exact isRollBound_bind combine h_can h_cost (hf 0 init)
        fun y => ih (α := α ∘ Fin.succ) (f := fun i x => f i.succ x) (fun i => budget i.succ)
          (fun i x => hf i.succ x) y

variable {c : (s : I) → P.A s → ℕ} {n : ℕ} {α : Fin (n + 1) → Type v}
  {f : (i : Fin n) → α i.castSucc → FreeM₂ P s s (α i.succ)}

/-- Charge bounds add along the dependent left fold `Fin.dfoldlM`. -/
theorem isChargeBound_dfoldlM (hm : IsDiagonalMonad inst) (b : Fin n → ℕ)
    (hf : ∀ i x, (f i x).IsChargeBound c (b i)) (init : α 0) :
    (Fin.dfoldlM n α f init).IsChargeBound c (∑ i, b i) := by
  have h := isRollBound_dfoldlM hm (· + ·) (by grind) (by grind) b 0 hf init
  rwa [foldr_add_eq_sum] at h

/-- Steps within a common charge budget `k` give a dependent left fold over `Fin n` within
`n * k`. -/
theorem isChargeBound_dfoldlM_of_forall (hm : IsDiagonalMonad inst) {k : ℕ}
    (hf : ∀ i x, (f i x).IsChargeBound c k) (init : α 0) :
    (Fin.dfoldlM n α f init).IsChargeBound c (n * k) := by
  simpa using isChargeBound_dfoldlM hm (fun _ => k) hf init

/-- A predicate on every rolled shape is preserved by the dependent left fold `Fin.dfoldlM`. The
predicate is the roll bound with the unit budget, check `p` and the identity cost. -/
theorem isRollBound_dfoldlM_unit (hm : IsDiagonalMonad inst) {p : (s : I) → P.A s → Prop}
    (hf : ∀ i x, (f i x).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b)) (init : α 0) :
    (Fin.dfoldlM n α f init).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b) :=
  isRollBound_dfoldlM hm (fun _ _ => ()) (fun _ _ _ _ _ h => ⟨h, h⟩)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) (fun _ => ()) () hf init

end Fin

/-! ## Dependent tuples -/

section Tuple

/-- Roll bounds compose along the dependent tuple sequencer `seqPi`, with the side conditions of
`FreeM₂.isRollBound_bind` and a right unit `z` of `combine`, which bounds the final `pure`.
Program `i` is bounded by `budget i`, and the tuple by those budgets combined in index order,
associated to the right, with final budget `z`. -/
theorem isRollBound_seqPi (combine : B → B → B)
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    {k : ℕ} {β : Fin k → Type v} (budget : Fin k → B) (z : B) (hz : ∀ b, combine b z = b)
    {f : (i : Fin k) → FreeM₂ P s s (β i)}
    (hf : ∀ i, (f i).IsRollBound (budget i) canRoll cost) :
    (seqPi f).IsRollBound (Fin.foldr k (fun i b => combine (budget i) b) z) canRoll cost := by
  induction k with
  | zero => exact isRollBound_pure _ _
  | succ k ih =>
      rw [seqPi_succ, Fin.foldr_succ, ← hz (Fin.foldr k _ z)]
      exact isRollBound_bind combine h_can h_cost (hf 0) fun _ =>
        isRollBound_bind combine h_can h_cost
          (ih (f := fun i => f i.succ) (fun i => budget i.succ) fun i => hf i.succ)
          fun _ => isRollBound_pure _ _

variable {c : (s : I) → P.A s → ℕ} {k : ℕ} {β : Fin k → Type v}
  {f : (i : Fin k) → FreeM₂ P s s (β i)}

/-- Charge bounds add along the dependent tuple sequencer `seqPi`. -/
theorem isChargeBound_seqPi (b : Fin k → ℕ) (hf : ∀ i, (f i).IsChargeBound c (b i)) :
    (seqPi f).IsChargeBound c (∑ i, b i) := by
  have h := isRollBound_seqPi (· + ·) (by grind) (by grind) b 0 Nat.add_zero hf
  rwa [foldr_add_eq_sum] at h

/-- Programs within a common charge budget `m` give a sequenced tuple of length `k` within
`k * m`. -/
theorem isChargeBound_seqPi_of_forall {m : ℕ} (hf : ∀ i, (f i).IsChargeBound c m) :
    (seqPi f).IsChargeBound c (k * m) := by
  simpa using isChargeBound_seqPi (fun _ => m) hf

/-- A predicate on every rolled shape is preserved by the dependent tuple sequencer `seqPi`. The
predicate is the roll bound with the unit budget, check `p` and the identity cost. -/
theorem isRollBound_seqPi_unit {p : (s : I) → P.A s → Prop}
    (hf : ∀ i, (f i).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b)) :
    (seqPi f).IsRollBound () (fun s a _ => p s a) (fun _ _ b => b) :=
  isRollBound_seqPi (fun _ _ => ()) (fun _ _ _ _ _ h => ⟨h, h⟩)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) (fun _ => ()) () (fun _ => rfl) hf

end Tuple

end IPFunctor.FreeM₂
