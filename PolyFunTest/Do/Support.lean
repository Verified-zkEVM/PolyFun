/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.Control.Do.Spec
import Std.Do.Internal.Ensures
import Mathlib.Data.ENat.Lattice

/-!
# Lawful attachment on core's `vcgen`

The demonic interpretation of a monad with lawful attachment, installed locally, lets `vcgen`
decompose `do` blocks whose leaves are then discharged against the support: `wp` is the "always"
judgment by `rfl`, core's triple is the guarded judgment, and a sound triple converts back into a
support fact through `allOutputs_of_wp`. The angelic interpretation is checked to compute the
"sometimes" judgment. The module acknowledges the tactic's experimental status with `set_option
experimental.vcgen true`; `PolyFunTest.Do.Algebra` pins the diagnostic itself.
-/

public section

open Std.WP MonadAttach

set_option experimental.vcgen true

/-! ## Upstream return predicates and weaker assumptions -/

section Lawful

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
  [LawfulMonadAttach m] {α : Type u}

example (x : m α) (p : α → Prop) : AllOutputs p x ↔ Std.Do.Internal.Ensures p x := by
  constructor
  · intro h
    exact Std.Do.Internal.Ensures.canReturn.weaken h
  · intro h a ha
    exact (Std.Do.Internal.MayReturn.of_canReturn ha).imp h

example (x : m α) (a : α) :
    a ∈ support x ↔ Std.Do.Internal.MayReturn x a :=
  Std.Do.Internal.MayReturn.canReturn_iff x a

example : WPMonad m Prop EStack⟨⟩ := toWPMonadDemonic

example : @LawfulWPMonadAttach m Prop EStack⟨⟩ _ _ _ _ _ (toWPMonadDemonic (m := m)) :=
  toWPMonadDemonic_lawfulWPMonadAttach

example {ω : Type u} [Monoid ω] : LawfulMonadAttach (WriterT ω m) := inferInstance

end Lawful

-- A numeric interpretation and structural safety can describe the same computation.
example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] [MAlgOrdered m ℕ∞] (x : m Nat) :
    ((toWPMonadDemonic (m := m)).toWP Nat).wp x (fun a => a = 0) estack⟨⟩
      = AllOutputs (fun a => a = 0) x ∧
    ((MAlgOrdered.toWPMonad (m := m) (l := ℕ∞)).toWP Nat).wp x (fun a => (a : ℕ∞))
      estack⟨⟩ = MAlgOrdered.wp x (fun a => (a : ℕ∞)) := ⟨rfl, rfl⟩

example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [WeaklyLawfulMonadAttach m] {ω : Type} [Monoid ω] :
    WeaklyLawfulMonadAttach (WriterT ω m) := inferInstance

-- Flattened StateT support has no exact bind law; demonic sequencing still applies.
example : WPMonad (StateT Bool Id) Prop EStack⟨⟩ := toWPMonadDemonic

example : WPMonad (ReaderT Empty Id) Prop EStack⟨⟩ := toWPMonadDemonic

example {ω : Type} [Monoid ω] :
    LawfulMonadAttach (WriterT ω (StateT Bool Id)) := inferInstance

-- The standard state lift retains the initial and final states in its postconditions.
example {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] (x : StateT Bool m Nat) (p : Nat → Bool → Prop) (s : Bool) :
    letI := toWPMonadDemonic (m := m)
    wp x p estack⟨⟩ s = AllOutputs (fun q => p q.1 q.2) (x.run s) := rfl

-- Lawful instances agree even when their attachment implementations are different.
example {m : Type → Type} [Monad m] (i j : MonadAttach m)
    (hi : @LawfulMonadAttach m _ i) (hj : @LawfulMonadAttach m _ j)
    {α : Type} (x : m α) (a : α) :
    @CanReturn m i α x a ↔ @CanReturn m j α x a := by
  have transfer (k l : MonadAttach m) (hk : @LawfulMonadAttach m _ k)
      (hl : @LawfulMonadAttach m _ l) (h : @CanReturn m k α x a) :
      @CanReturn m l α x a := by
    rw [← hl.map_attach (x := x)] at h
    exact hk.canReturn_map_imp h
  exact ⟨transfer i j hi hj, transfer j i hj hi⟩

/-- The demonic interpretation of `SetM`, installed locally. -/
local instance instWPMonadSetMDemonic : WPMonad SetM Prop EStack⟨⟩ :=
  toWPMonadDemonic

/-- A nondeterministic choice followed by a deterministic step. -/
def choose12 : SetM Nat := do
  let x ← (({1, 2} : Set Nat) : SetM Nat)
  pure (x + 1)

/-- `wp` is the "always" judgment. -/
example (x : SetM Nat) (post : Nat → Prop) (epost : EStack⟨⟩) :
    wp x post epost = AllOutputs post x :=
  rfl

/- `vcgen` decomposes the bind chain; the nondeterministic leaf has no registered
specification, so its verification condition is left as a support fact. -/
theorem choose12_spec : ⦃ True ⦄ choose12 ⦃ fun r => r = 2 ∨ r = 3 ⦄ := by
  vcgen -errorOnMissingSpec [choose12]
  intro a ha
  have ha' : a ∈ ({1, 2} : Set Nat) := SetM.canReturn_iff.mp ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
  change AllOutputs (fun r => r = 2 ∨ r = 3) (pure (a + 1) : SetM Nat)
  rw [allOutputs_pure]
  omega

/-- A sound triple converts back into a support fact. -/
example : AllOutputs (fun r => r = 2 ∨ r = 3) choose12 := by
  have := toWPMonadDemonic_lawfulWPMonadAttach (m := SetM)
  refine allOutputs_of_wp ?_
  intro _
  simpa only [Lean.Order.ofProp_prop_eq] using choose12_spec.le_wp trivial

/-- A `let mut` accumulator over a `for` loop. -/
def sumList (xs : List Nat) : SetM Nat := do
  let mut s := 0
  for x in xs do
    s := s + x
  pure s

/- `vcgen` reaches the loop through core's `Spec.forIn_list`; the invariant relates the
accumulator to the elements consumed so far. -/
theorem sumList_spec (xs : List Nat) : ⦃ True ⦄ sumList xs ⦃ fun r => r = xs.sum ⦄ := by
  vcgen [sumList] invariants
    · fun pref _ s => s = pref.sum
  all_goals simp_all

/-- The loop rule for the "always" judgment, stated without any triple. -/
example (xs : List Nat) : AllOutputs (fun r => r = xs.sum) (sumList xs) := by
  have := toWPMonadDemonic_lawfulWPMonadAttach (m := SetM)
  refine allOutputs_of_wp ?_
  intro _
  simpa only [Lean.Order.ofProp_prop_eq] using (sumList_spec xs).le_wp trivial

/-- A `forM` loop whose body is a nondeterministic choice constrained by the element. -/
def checkAll (xs : List Nat) : SetM PUnit :=
  forM xs fun x => (({x, x + 1} : Set Nat) : SetM Nat) *> pure ⟨⟩

/- `forM` over a list has no specification in core; `PolyFun.Control.Do.Spec` supplies
`Spec.forM_list`, whose `PUnit`-accumulator invariant `vcgen`'s `invariants` clause fills. The
nondeterministic body has no registered specification and is left as a support fact. -/
theorem checkAll_spec (xs : List Nat) : ⦃ True ⦄ checkAll xs ⦃ fun _ => True ⦄ := by
  vcgen -errorOnMissingSpec [checkAll] invariants
    · fun _ _ _ => True
  all_goals simp

/-- The same loop through the function `List.forM`. -/
def checkAll' (xs : List Nat) : SetM PUnit :=
  xs.forM fun x => (({x, x + 1} : Set Nat) : SetM Nat) *> pure ⟨⟩

/- `Spec.forM_list` is stated on the class method `forM`, the simp normal form; the function
spelling reaches it through `List.forM_eq_forM` in the unfolding list. -/
theorem checkAll'_spec (xs : List Nat) : ⦃ True ⦄ checkAll' xs ⦃ fun _ => True ⦄ := by
  vcgen -errorOnMissingSpec [checkAll', List.forM_eq_forM] invariants
    · fun _ _ _ => True
  all_goals simp

/-- The demonic interpretation is conjunctive. -/
example (x : SetM Nat) :
    @WPConjunctive (SetM Nat) Nat Prop EStack⟨⟩ _ _ (instWPMonadSetMDemonic.toWP Nat) x :=
  toWPMonadDemonic_wpConjunctive x

/-- The angelic interpretation computes the "sometimes" judgment. -/
example (x : SetM Nat) (post : Nat → Prop) (epost : EStack⟨⟩) :
    ((toWPMonadAngelic (m := SetM)).toWP Nat).wp x post epost = SomeOutput post x :=
  rfl
