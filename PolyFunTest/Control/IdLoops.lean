/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.IdLoops

/-!
# Invariant rules for loops in `Id`

Each rule of `PolyFun.Control.Monad.Support.IdLoops` is applied to a small loop: a search that
stops early, a loop whose body uses its membership proof, a loop over an array, a loop that only
yields under an invariant, and loops with `return` inside, both as bare loops and as the
elaborated `do` blocks of definitions, where the rule is applied without restating the body.
-/

@[expose] public section

namespace PolyFunTest.IdLoops

/-! ## Invariant rules -/

/-- Stop at the first element above `5`; otherwise keep the last element seen. -/
def lastSmall (xs : List Nat) : Nat :=
  (forIn (m := Id) xs 0 fun a _ => if a > 5 then pure (.done 0) else pure (.yield a)).run

/-- The early exit is a `.done` step, which must establish the invariant at the end. -/
example (xs : List Nat) : lastSmall xs ≤ 5 :=
  Id.run_forIn_list_of_inv (fun _ _ b => b ≤ 5)
    (fun _ cur _ _ _ _ => by
      by_cases hc : cur > 5
      · simp only [hc, ↓reduceIte, Id.run_pure]; exact Nat.zero_le 5
      · simp only [hc, ↓reduceIte, Id.run_pure]; exact Nat.le_of_not_lt hc)
    (Nat.zero_le 5)

/-- The body builds an index into the list from its membership proof. -/
example (xs : List Nat) :
    let r := (forIn' (m := Id) xs 0 fun a ha b =>
      pure (.yield (max b (⟨xs.idxOf a, List.idxOf_lt_length_of_mem ha⟩ : Fin xs.length).val))).run
    r = 0 ∨ r < xs.length :=
  Id.run_forIn'_list_of_inv (fun _ _ b => b = 0 ∨ b < xs.length)
    (fun pref cur suff hsplit b hb => by
      have hlt : xs.idxOf cur < xs.length := List.idxOf_lt_length_of_mem (by simp [hsplit])
      simp only [Id.run_pure]
      omega)
    (Or.inl rfl)

/-- A bound on the state that every step preserves. -/
example (xs : List Nat) :
    (forIn (m := Id) xs 0 fun a b =>
      if a = 0 then pure (.done b) else pure (.yield (min (b + a) 7))).run ≤ 7 :=
  Id.run_forIn_list_of_const_inv (fun b => b ≤ 7)
    (fun cur _ b hb => by
      by_cases hc : cur = 0
      · simp only [hc, ↓reduceIte, Id.run_pure, ForInStep.value]; exact hb
      · simp only [hc, ↓reduceIte, Id.run_pure, ForInStep.value]; exact Nat.min_le_right _ _)
    (Nat.zero_le 7)

/-- An array loop counts at most the elements it has consumed. -/
example (xs : Array Nat) :
    (forIn (m := Id) xs 0 fun a b => pure (.yield (if a = 0 then b else b + 1))).run ≤ xs.size := by
  have := Id.run_forIn_of_pureForIn (f := fun a b => pure (.yield (if a = 0 then b else b + 1)))
    (init := 0) xs (fun pref _ b => b ≤ pref.length)
    (fun _ cur _ _ b hb => by
      simp only [Id.run_pure, List.length_append, List.length_singleton]
      split <;> omega)
    (Nat.le_refl 0)
  simpa using this

/-! ## Loops that only yield under an invariant -/

/-- A loop that would stop on a zero is the sum when no element is zero. -/
example (xs : List Nat) (h : ∀ a ∈ xs, a ≠ 0) :
    (forIn (m := Id) xs 0 fun a b => if a = 0 then pure (.done b) else pure (.yield (b + a))).run =
      xs.foldl (· + ·) 0 :=
  Id.run_forIn_list_eq_foldl_of_inv (· + ·) (fun _ _ _ => True)
    (fun pref cur suff hsplit b _ => by
      have hcur : cur ≠ 0 := h cur (by rw [hsplit]; simp)
      exact ⟨by simp [hcur], trivial⟩)
    trivial

/-- The same over a range: dividing by the index is safe on `[1:n]`. -/
example (n : Nat) :
    (forIn (m := Id) [1:n] 0 fun i b =>
      if i = 0 then pure (.done b) else pure (.yield (b + n / i))).run =
      (ForIn.toList [1:n]).foldl (fun b i => b + n / i) 0 :=
  Id.run_forIn_eq_foldl_of_pureForIn_of_inv [1:n] (fun b i => b + n / i) (fun _ _ _ => True)
    (fun pref cur suff hsplit b _ => by
      have hcur : cur ∈ ForIn.toList [1:n] := by rw [hsplit]; simp
      have : cur ≠ 0 := by simp at hcur; omega
      exact ⟨by simp [this], trivial⟩)
    trivial

/-! ## Early return -/

/-- Return the first element above `5`, or `none`. -/
def firstBig (xs : List Nat) : Option Nat := Id.run do
  for x in xs do
    if x > 5 then return some x
  return none

/-- The body of `firstBig` over its `Option (Option Nat) × PUnit` state, as `do` elaborates it. -/
def firstBigBody (x : Nat) (s : Option (Option Nat) × PUnit) :
    Id (ForInStep (Option (Option Nat) × PUnit)) :=
  if x > 5 then pure (.done (some (some x), s.2)) else pure (.yield (none, s.2))

/-- The bare loop either runs to the end over small elements or returns a large one. -/
example (xs : List Nat) :
    (forIn xs (none, ()) firstBigBody).run.1 = none ∧ (∀ x ∈ xs, x ≤ 5) ∨
      ∃ x ∈ xs, (forIn xs (none, ()) firstBigBody).run.1 = some (some x) ∧ 5 < x := by
  have key := Id.run_forIn_list_earlyReturn_of_inv (xs := xs) (init := ())
    (f := firstBigBody) (fun pref _ _ => ∀ x ∈ pref, x ≤ 5)
    (fun r _ => ∃ x ∈ xs, r = some x ∧ 5 < x)
    (fun pref cur suff hsplit _ hb => by
      by_cases hc : cur > 5
      · simp only [firstBigBody, hc, ↓reduceIte, Id.run_pure]
        exact ⟨cur, by simp [hsplit], rfl, hc⟩
      · simp only [firstBigBody, hc, ↓reduceIte, Id.run_pure]
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hb x hx
        · rw [List.mem_singleton.1 hx]; exact Nat.le_of_not_lt hc)
    (fun _ h => absurd h List.not_mem_nil)
  generalize (forIn xs (none, ()) firstBigBody).run = res at key ⊢
  obtain ⟨_ | r, b⟩ := res
  · exact Or.inl ⟨rfl, key⟩
  · obtain ⟨x, hx, rfl, hlt⟩ := key; exact Or.inr ⟨x, hx, rfl, hlt⟩

/-- The same rule over an array of small elements: the loop never returns early. -/
example (xs : Array Nat) (h : ∀ x ∈ xs, x ≤ 5) :
    (forIn xs (none, ()) firstBigBody).run.1 = none := by
  have key := Id.run_forIn_earlyReturn_of_pureForIn (init := ()) (f := firstBigBody) xs
    (fun _ _ _ => True) (fun _ _ => False)
    (fun pref cur suff hsplit _ _ => by
      have hcur : cur ∈ ForIn.toList xs := by rw [hsplit]; simp
      have hc : ¬cur > 5 := Nat.not_lt.2 (h cur (by simpa using hcur))
      simp only [firstBigBody, hc, ↓reduceIte, Id.run_pure])
    trivial
  generalize (forIn xs (none, ()) firstBigBody).run = res at key ⊢
  obtain ⟨_ | r, b⟩ := res
  · rfl
  · exact key.elim

/-! ## A loop followed by the rest of the `do` block -/

/-- Count the elements of an array in a `do` block that continues after the loop. -/
def countPlusOne (xs : Array Nat) : Nat := Id.run do
  let mut c := 0
  for _ in xs do
    c := c + 1
  return c + 1

/-- The rule applies to the elaborated block; the body is never restated. -/
example (xs : Array Nat) : countPlusOne xs = xs.size + 1 := by
  unfold countPlusOne
  apply Id.run_bind_forIn_of_pureForIn xs (· = xs.size + 1) (fun pref _ c => c = pref.length)
  · intro _ _ _ _ b hb; simp [hb]
  · rfl
  · intro b hb; simp [hb]

/-- `firstBig` finds nothing when every element is at most `5`. -/
example (xs : List Nat) (h : ∀ x ∈ xs, x ≤ 5) : firstBig xs = none := by
  unfold firstBig
  apply Id.run_bind_forIn_earlyReturn_of_pureForIn xs (· = none) (fun _ _ _ => True)
    (fun _ _ => False)
  · intro pref cur suff hsplit _ _
    have hxs : xs = pref ++ cur :: suff := by simpa using hsplit
    have hc : ¬cur > 5 := Nat.not_lt.2 (h cur (by simp [hxs]))
    simp only [hc, ↓reduceIte, Id.run_pure]
  · trivial
  · intro _ _ hf; exact hf.elim
  · intro _ _; rfl

/-- `firstBig` returns an element above `5` whenever it returns. -/
example (xs : List Nat) (r : Nat) (hr : firstBig xs = some r) : r ∈ xs ∧ 5 < r := by
  revert hr
  unfold firstBig
  apply Id.run_bind_forIn_earlyReturn_of_pureForIn xs (fun o => o = some r → r ∈ xs ∧ 5 < r)
    (fun _ _ _ => True) (fun o _ => ∀ s, o = some s → s ∈ xs ∧ 5 < s)
  · intro pref cur suff hsplit _ _
    by_cases hc : cur > 5
    · simp only [hc, ↓reduceIte, Id.run_pure]
      intro s hs
      cases hs
      have hxs : xs = pref ++ cur :: suff := by simpa using hsplit
      exact ⟨by simp [hxs], hc⟩
    · simp only [hc, ↓reduceIte, Id.run_pure]
  · trivial
  · intro o _ ho hor; exact ho r hor
  · intro _ _ h; cases h

end PolyFunTest.IdLoops
