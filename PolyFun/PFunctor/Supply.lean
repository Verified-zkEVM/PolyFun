/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Basic

/-!
# Positional answer supplies for a polynomial functor

A `Supply P` assigns to each position of a polynomial functor the list of answers to be handed out
there, in order: the structural content of a pre-sampled answer tape. `Supply.run` executes a
`FreeM P` program against one, consuming a position's answers in order and failing once they run
out.

The operations come in two families, which are the two ways of rewinding a run. `takeAt` truncates
a position's list, so everything past the cut is *discarded* and a rerun must be resupplied there.
`setAt` instead substitutes a single answer in place, so a rerun is presented the same supply apart
from that one answer.

`run_addValues` is why the two agree on runs: a run consumes a prefix of each position's list, so
answers appended past what it reads are invisible to it. Combined with `setAt_eq_addValues_drop`,
which factors substitution through truncate-append-restore, this gives
`run_setAt_eq_run_takeAt_addValues`: substituting the `n`-th answer and rewinding to it produce the
same run.
-/

@[expose] public section

universe uA uB v

namespace PFunctor

/-- A positional answer supply for `P`: for each position, the answers to be handed out there, in
order. -/
def Supply (P : PFunctor.{uA, uB}) : Type max uA uB :=
  (a : P.A) → List (P.B a)

namespace Supply

variable {P : PFunctor.{uA, uB}}

instance : EmptyCollection (Supply P) := ⟨fun _ => []⟩

@[ext]
protected lemma ext {s t : Supply P} (h : ∀ a, s a = t a) : s = t := funext h

@[simp] lemma empty_apply (a : P.A) : (∅ : Supply P) a = [] := rfl

variable [DecidableEq P.A]

/-- Replace the answers at position `a`. -/
def update (s : Supply P) (a : P.A) (xs : List (P.B a)) : Supply P :=
  Function.update s a xs

/-- Keep only the first `n` answers at position `a`, discarding the rest. -/
def takeAt (s : Supply P) (a : P.A) (n : ℕ) : Supply P :=
  Function.update s a ((s a).take n)

/-- Append answers at position `a`. -/
def addValues (s : Supply P) {a : P.A} (us : List (P.B a)) : Supply P :=
  Function.update s a (s a ++ us)

/-- Replace the `n`-th answer at position `a`, leaving every other answer — and every other
position — untouched. An out-of-range `n` leaves the supply unchanged. -/
def setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) : Supply P :=
  Function.update s a ((s a).set n u)

/-- Consume one answer from position `a`, when there is one. -/
def pop (s : Supply P) (a : P.A) : Option (P.B a × Supply P) :=
  match s a with
  | [] => none
  | u :: us => some (u, Function.update s a us)

/-! ### Basic evaluation

`Supply P` is a `def`, so the elaborator does not see its Pi type on its own; naming the motive
keeps the `Function.update` lemmas applicable below. -/

/-- The dependent motive a supply's answer lists live over. -/
private abbrev motive (P : PFunctor.{uA, uB}) : P.A → Type uB := fun a => List (P.B a)

@[simp] lemma update_apply_self (s : Supply P) (a : P.A) (xs : List (P.B a)) :
    s.update a xs a = xs := Function.update_self (β := motive P) a xs s

@[simp] lemma update_apply_of_ne (s : Supply P) (a : P.A) (xs : List (P.B a)) {b : P.A}
    (hb : b ≠ a) : s.update a xs b = s b := Function.update_of_ne (β := motive P) hb xs s

@[simp] lemma takeAt_apply_self (s : Supply P) (a : P.A) (n : ℕ) :
    s.takeAt a n a = (s a).take n := Function.update_self (β := motive P) a _ s

@[simp] lemma takeAt_apply_of_ne (s : Supply P) (a : P.A) (n : ℕ) {b : P.A} (hb : b ≠ a) :
    s.takeAt a n b = s b := Function.update_of_ne (β := motive P) hb _ s

@[simp] lemma addValues_apply_self (s : Supply P) {a : P.A} (us : List (P.B a)) :
    s.addValues us a = s a ++ us := Function.update_self (β := motive P) a _ s

@[simp] lemma addValues_apply_of_ne (s : Supply P) {a : P.A} (us : List (P.B a)) {b : P.A}
    (hb : b ≠ a) : s.addValues us b = s b := Function.update_of_ne (β := motive P) hb _ s

@[simp] lemma setAt_apply_self (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    s.setAt a n u a = (s a).set n u := Function.update_self (β := motive P) a _ s

@[simp] lemma setAt_apply_of_ne (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) {b : P.A}
    (hb : b ≠ a) : s.setAt a n u b = s b := Function.update_of_ne (β := motive P) hb _ s

lemma length_setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    (s.setAt a n u a).length = (s a).length := by simp

/-! ### Point substitution -/

/-- Substituting at position `n` does not change the truncation at `n`: the two supplies present
the same answers strictly before the substituted one. -/
@[simp] lemma takeAt_setAt (s : Supply P) (a : P.A) (n : ℕ) (u : P.B a) :
    (s.setAt a n u).takeAt a n = s.takeAt a n := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.take_set_of_le le_rfl]
  · simp [hb]

/-- The substituted position carries the new answer. -/
lemma getElem?_setAt_self (s : Supply P) (a : P.A) {n : ℕ} (u : P.B a)
    (hn : n < (s a).length) : (s.setAt a n u a)[n]? = some u := by
  simpa using List.getElem?_set_self hn

/-- Only the last substitution at a position survives, so the supplies obtained by varying one
answer form a family indexed by the replacement alone. -/
@[simp] lemma setAt_setAt (s : Supply P) (a : P.A) (n : ℕ) (u u' : P.B a) :
    (s.setAt a n u).setAt a n u' = s.setAt a n u' := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.set_set]
  · simp [hb]

/-- A supply is the member of its own substitution family at its current answer. -/
lemma setAt_getElem_self (s : Supply P) (a : P.A) {n : ℕ} (hn : n < (s a).length) :
    s.setAt a n (s a)[n] = s := by
  ext b; by_cases hb : b = a
  · subst hb; simp [List.set_getElem_self]
  · simp [hb]

/-- Substitution factors through truncate, append, restore. The final `addValues` restores exactly
the tail that `takeAt` discards, which is the difference between substituting an answer and
rewinding to it. -/
lemma setAt_eq_addValues_drop (s : Supply P) (a : P.A) {n : ℕ} (u : P.B a)
    (hn : n < (s a).length) :
    s.setAt a n u = ((s.takeAt a n).addValues [u]).addValues ((s a).drop (n + 1)) := by
  ext b; by_cases hb : b = a
  · subst hb
    simp only [setAt_apply_self, addValues_apply_self, takeAt_apply_self]
    rw [List.set_eq_take_append_cons_drop]
    simp [hn]
  · simp [hb]

/-! ### Running a program against a supply -/

variable {α : Type v}

/-- Run a program against a supply: each operation at position `a` consumes the next answer listed
there, and the run fails once that list is exhausted. The remaining supply is returned alongside
the result. -/
def run : FreeM P α → Supply P → Option (α × Supply P)
  | .pure x, s => some (x, s)
  | .liftBind a next, s =>
      match s a with
      | [] => none
      | u :: us => run (next u) (Function.update s a us)

@[simp] lemma run_pure (x : α) (s : Supply P) :
    run (pure x : FreeM P α) s = some (x, s) := rfl

lemma run_liftBind_of_nil {a : P.A} (next : P.B a → FreeM P α) {s : Supply P} (hs : s a = []) :
    run (FreeM.liftBind a next) s = none := by
  rw [run]; rw [hs]

lemma run_liftBind_of_cons {a : P.A} (next : P.B a → FreeM P α) {s : Supply P} {u : P.B a}
    {us : List (P.B a)} (hs : s a = u :: us) :
    run (FreeM.liftBind a next) s = run (next u) (s.update a us) := by
  rw [run]; rw [hs]; rfl

private lemma addValues_update_self (s : Supply P) (a : P.A) (vs us : List (P.B a)) :
    (s.addValues us).update a (vs ++ us) = (s.update a vs).addValues us :=
  Supply.ext fun c => by
    by_cases hc : c = a
    · subst hc; simp
    · simp [hc]

private lemma addValues_update_of_ne (s : Supply P) {a b : P.A} (hb : b ≠ a)
    (vs : List (P.B b)) (us : List (P.B a)) :
    (s.addValues us).update b vs = (s.update b vs).addValues us :=
  Supply.ext fun c => by
    by_cases hc : c = b
    · subst hc; simp [hb]
    · by_cases hc' : c = a
      · subst hc'; simp [hc]
      · simp [hc, hc']

/-- **Answers past what a run reads are invisible to it.** A run consumes a prefix of each
position's list, so appending more answers changes neither the result nor the unconsumed remainder
apart from the appended tail. -/
theorem run_addValues : ∀ (program : FreeM P α) {s : Supply P} {a : P.A} (us : List (P.B a))
    {x : α} {s' : Supply P}, run program s = some (x, s') →
      run program (s.addValues us) = some (x, s'.addValues us)
  | .pure y, s, a, us, x, s', h => by
      rw [show run (FreeM.pure y : FreeM P α) s = some (y, s) from rfl, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .liftBind b next, s, a, us, x, s', h => by
      classical
      cases hs : s b with
      | nil => rw [run_liftBind_of_nil next hs] at h; simp at h
      | cons v vs =>
          rw [run_liftBind_of_cons next hs] at h
          by_cases hb : b = a
          · subst hb
            have hcons : (s.addValues us) b = v :: (vs ++ us) := by
              rw [addValues_apply_self, hs, List.cons_append]
            rw [run_liftBind_of_cons next hcons, addValues_update_self s b vs us]
            exact run_addValues (next v) us h
          · have hcons : (s.addValues us) b = v :: vs := by
              rw [addValues_apply_of_ne _ _ (Ne.symm fun h' => hb h'.symm), hs]
            rw [run_liftBind_of_cons next hcons, addValues_update_of_ne s hb vs us]
            exact run_addValues (next v) us h

/-- **The two rewind primitives agree on runs.** Substituting the `n`-th answer at `a` and
rewinding to that point before supplying `u` present the same answers to the program, because the
answers after the substituted one are past what the run consumes. -/
theorem run_setAt_eq_run_takeAt_addValues (program : FreeM P α) (s : Supply P) (a : P.A) {n : ℕ}
    (u : P.B a) (hn : n < (s a).length) {x : α} {s' : Supply P}
    (h : run program ((s.takeAt a n).addValues [u]) = some (x, s')) :
    run program (s.setAt a n u) = some (x, s'.addValues ((s a).drop (n + 1))) := by
  rw [setAt_eq_addValues_drop s a u hn]
  exact run_addValues program _ h

end Supply

end PFunctor
