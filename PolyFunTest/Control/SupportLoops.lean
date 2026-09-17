/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.Loops
public import PolyFun.Control.Monad.Support.Instances

/-!
# Loop rules for exact support, without a triple

The invariant rules of `PolyFun.Control.Monad.Support.Loops` discharge "always" and "sometimes"
judgments about `for` loops, `forM`, and `foldlM` directly, with no weakest-precondition
instance installed and no `vcgen` call.
-/

public section

open MonadAttach

/-! Universal loop safety needs no exact support equations on the base monad. -/

example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] (xs : List Nat) (f : Nat → m PUnit) :
    AllOutputs (fun _ => True) (xs.forM f) :=
  allOutputs_forM_list_of_inv (fun _ _ => True)
    (fun _ _ _ _ _ => allOutputs_true _) trivial

example (xs : List Nat) (f : Nat → StateT Bool Id PUnit) :
    AllOutputs (fun _ => True) (xs.forM f) :=
  allOutputs_forM_list_of_inv (fun _ _ => True)
    (fun _ _ _ _ _ => allOutputs_true _) trivial

example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] (xs : List Nat) (f : Nat → Nat → m (ForInStep Nat)) :
    AllOutputs (fun _ => True) (forIn xs 0 f) :=
  allOutputs_forIn_list_of_const_inv (fun _ => True)
    (fun _ _ _ _ r _ => by cases r <;> trivial) trivial

/-- A nondeterministic choice between an element and its successor. -/
def choose (x : Nat) : SetM Nat := ({x, x + 1} : Set Nat)

theorem canReturn_choose {x y : Nat} : CanReturn (choose x) y ↔ y = x ∨ y = x + 1 := by
  rw [SetM.canReturn_iff]
  simp [choose, SetM.run]

/-- A `let mut` accumulator over a `for` loop, in the nondeterministic monad. -/
def sumList (xs : List Nat) : SetM Nat := do
  let mut s := 0
  for x in xs do
    s := s + x
  pure s

/-- The invariant relates the accumulator to the elements consumed so far. -/
example (xs : List Nat) : AllOutputs (fun r => r = xs.sum) (sumList xs) := by
  unfold sumList
  rw [allOutputs_bind]
  intro r hr
  rw [allOutputs_pure]
  have := allOutputs_forIn_list_of_inv (m := SetM) (xs := xs) (init := 0)
    (f := fun x s => pure (ForInStep.yield (s + x))) (fun pref _ s => s = pref.sum)
    (fun pref cur suff _ b hb => by simp [hb]) rfl
  simpa using this r hr

/-- A choice at every element, constrained by the element. -/
def chooseSum (xs : List Nat) : SetM Nat := do
  let mut s := 0
  for x in xs do
    let y ← choose x
    s := s + y
  pure s

example (xs : List Nat) : AllOutputs (fun r => xs.sum ≤ r) (chooseSum xs) := by
  unfold chooseSum
  rw [allOutputs_bind]
  intro r hr
  rw [allOutputs_pure]
  have := allOutputs_forIn_list_of_inv (m := SetM) (xs := xs) (init := 0)
    (f := fun x s => choose x >>= fun y => pure (ForInStep.yield (s + y)))
    (fun pref _ s => pref.sum ≤ s)
    (fun pref cur suff _ b hb => by
      rw [allOutputs_bind]
      intro y hy
      rw [allOutputs_pure]
      rcases canReturn_choose.mp hy with rfl | rfl <;> simp <;> omega) (Nat.le_refl _)
  simpa using this r hr

/-- The "sometimes" twin: some run of the loop returns exactly the sum. -/
example (xs : List Nat) : SomeOutput (fun r => r = xs.sum) (chooseSum xs) := by
  unfold chooseSum
  rw [someOutput_bind]
  have := someOutput_forIn_list_of_inv (m := SetM) (xs := xs) (init := 0)
    (f := fun x s => choose x >>= fun y => pure (ForInStep.yield (s + y)))
    (fun pref _ s => s = pref.sum)
    (fun pref cur suff _ b hb => by
      rw [someOutput_bind]
      refine ⟨cur, canReturn_choose.mpr (Or.inl rfl), ?_⟩
      rw [someOutput_pure]
      simp [hb]) rfl
  exact this.imp fun r ⟨hr, hsum⟩ => ⟨hr, (someOutput_pure _ _).mpr hsum⟩

/-- `forM` by the induction rule. -/
example (xs : List Nat) : AllOutputs (fun _ => True) (xs.forM fun x => choose x *> pure ⟨⟩) :=
  allOutputs_forM_list_of_inv (fun _ _ => True) (fun _ _ _ _ _ => by simp) trivial

/-- Arrays iterate over their list, so the container rule applies through `PureForIn`. -/
example (xs : Array Nat) : AllOutputs (fun r => r = xs.toList.sum)
    (forIn xs 0 (fun x s => pure (ForInStep.yield (s + x))) : SetM Nat) := by
  have := allOutputs_forIn_of_pureForIn (m := SetM) xs (init := 0)
    (f := fun x s => pure (ForInStep.yield (s + x))) (fun pref _ s => s = pref.sum)
    (fun pref cur suff _ b hb => by simp [hb]) rfl
  simpa using this
