/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.PFunctor.Free.Do
public import Mathlib.Data.ENat.Lattice

/-!
# Exact weakest preconditions under `simp`

`ExactWPMonad` is found for every exact construction — an ordered algebra installed locally,
core's transformer lifts over it, the demonic and angelic support readings, and the scoped
free-program readings — and its equational set normalizes core's `wp` itself: after `simp`, goals
keep core's head, with no `MAlgOrdered.wp` or support judgment in the result. The base monad is
a fresh copy of `Id` so that no global core instance competes with the local one.
-/

public section

open Std.WP

namespace PolyFunTest.Exact

/-- A deterministic monad with no global weakest-precondition instance. -/
@[expose]
def Det (α : Type) : Type := α

instance : Monad Det where
  pure a := a
  bind x f := f x

instance : LawfulMonad Det :=
  LawfulMonad.mk' Det (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- The identity ordered algebra on `Det` at the extended naturals. -/
noncomputable local instance instMAlgOrderedDetENat : MAlgOrdered Det ℕ∞ where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

/-- Its core interpretation, installed locally. -/
noncomputable local instance instWPMonadDetENat : WPMonad Det ℕ∞ EStack⟨⟩ :=
  MAlgOrdered.toWPMonad

/-! ## Instances -/

example : ExactWPMonad Det ℕ∞ EStack⟨⟩ := inferInstance
example {σ : Type} : ExactWPMonad (StateT σ Det) (σ → ℕ∞) EStack⟨⟩ := inferInstance
example {ρ : Type} : ExactWPMonad (ReaderT ρ Det) (ρ → ℕ∞) EStack⟨⟩ := inferInstance
example : ExactWPMonad (OptionT Det) ℕ∞ ((Unit → ℕ∞) × EStack⟨⟩) := inferInstance
example {ε : Type} : ExactWPMonad (ExceptT ε Det) ℕ∞ ((ε → ℕ∞) × EStack⟨⟩) :=
  inferInstance

example : @ExactWPMonad SetM Prop EStack⟨⟩ _ _ _ (MonadAttach.toWPMonadDemonic (m := SetM)) :=
  inferInstance
example : @ExactWPMonad SetM Prop EStack⟨⟩ _ _ _ (MonadAttach.toWPMonadAngelic (m := SetM)) :=
  inferInstance

section FreeDemonic
open scoped PFunctor.FreeM.DemonicWP
example (P : PFunctor.{0, 0}) : ExactWPMonad (PFunctor.FreeM P) Prop EStack⟨⟩ := inferInstance
end FreeDemonic

section FreeAngelic
open scoped PFunctor.FreeM.AngelicWP
example (P : PFunctor.{0, 0}) : ExactWPMonad (PFunctor.FreeM P) Prop EStack⟨⟩ := inferInstance
end FreeAngelic

/-! ## Normalization keeps core's head -/

/-- A `do` block normalizes to nested `wp` of its draws. -/
example (a : Det Nat) (b : Nat → Det Nat) (post : Nat → ℕ∞) :
    wp (do let x ← a; let y ← b x; pure (x + y) : Det Nat) post estack⟨⟩ =
      wp a (fun x => wp (b x) (fun y => post (x + y)) estack⟨⟩) estack⟨⟩ := by
  simp only [ExactWPMonad.wp_bind, ExactWPMonad.wp_pure]

/-- Maps fuse into the postcondition and branches move outward. -/
example (c : Bool) (a b : Det Nat) (f : Nat → Nat) (post : Nat → ℕ∞) :
    wp (f <$> if c then a else b) post estack⟨⟩ =
      if c then wp a (fun x => post (f x)) estack⟨⟩
      else wp b (fun x => post (f x)) estack⟨⟩ := by
  simp only [ExactWPMonad.wp_map, ExactWPMonad.wp_ite]

/-- `simp` does not unfold core's `wp` into `MAlgOrdered.wp`: the bridge is a lemma, not a
normalization. -/
example (a : Det Nat) (post : Nat → ℕ∞) :
    wp (a >>= fun x => pure (x + 1)) post estack⟨⟩ =
      wp a (fun x => post (x + 1)) estack⟨⟩ := by
  simp

/-- A stateful program normalizes through core's `StateT` lift. -/
example (a : Det Nat) (post : Nat → Nat → ℕ∞) (s : Nat) :
    wp (do let x ← StateT.lift a; modify (· + x); pure x : StateT Nat Det Nat) post
        estack⟨⟩ s =
      wp a (fun x => post x (s + x)) estack⟨⟩ := by
  simp [StateT.run_lift, StateT.run_modify]

/-- The failure branch of `OptionT` reaches the exception postcondition exactly. -/
example (a : Det Nat) (post : Nat → ℕ∞) (epost : (Unit → ℕ∞) × EStack⟨⟩) :
    wp (do let x ← OptionT.lift a; if x = 0 then failure else pure x : OptionT Det Nat) post
        epost =
      wp a (fun x => if x = 0 then epost.fst () else post x) estack⟨⟩ := by
  simp only [ExactWPMonad.wp_bind, ExactWPMonad.wp_ite, ExactWPMonad.wp_pure,
    OptionT.wp_apply_eq, OptionT.run_lift, OptionT.run_failure, Lean.Order.pushOption_some,
    Lean.Order.pushOption_none]

/-- An upper bound through a bind, which the inequational laws alone do not give. -/
example (a : Det Nat) (b : Nat → Det Nat) (post : Nat → ℕ∞) (c : ℕ∞)
    (h : ∀ x, wp (b x) post estack⟨⟩ ≤ c) (ha : ∀ g : Nat → ℕ∞, (∀ x, g x ≤ c) →
      wp a g estack⟨⟩ ≤ c) :
    wp (a >>= b) post estack⟨⟩ ≤ c := by
  rw [ExactWPMonad.wp_bind]
  exact ha _ h

/-- The demonic reading normalizes as a predicate transformer, not as its judgment. -/
example (x : SetM Nat) (f : Nat → SetM Nat) (p : Nat → Prop) :
    (letI := MonadAttach.toWPMonadDemonic (m := SetM)
     wp (x >>= f) p estack⟨⟩) =
      (letI := MonadAttach.toWPMonadDemonic (m := SetM)
       wp x (fun a => wp (f a) p estack⟨⟩) estack⟨⟩) := by
  let := MonadAttach.toWPMonadDemonic (m := SetM.{0})
  exact ExactWPMonad.wp_bind x f p estack⟨⟩

end PolyFunTest.Exact
