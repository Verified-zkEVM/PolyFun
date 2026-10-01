/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Do.Spec
public import PolyFun.Control.Monad.Algebra.WP
public import Mathlib.Data.ENat.Lattice

/-!
# The transformers' constructors, lifts, runners and loops on core's `vcgen`

The rules of `PolyFun.Control.Do.Spec` for `StateT.mk`, `StateT.lift`, running a `StateT` with
the state discarded, `OptionT.mk`, `ExceptT.mk`, `ExceptT.lift`, running an `OptionT` or `ExceptT`
into a postcondition of the returned option or result, `List.mapM` with a loop invariant, and the
sequence combinators `<*` and `*>`, each over core's `Prop` reading of `Id`, where the matcher
applies the rule to the constructor, lift or runner before `vcgen` looks inside; and `guard` under
a lattice-valued reading of a deterministic monad, where `Spec.guard_OptionT_iInf` applies in
place of the `Prop` rule.
-/

public section

open Std.WP

set_option experimental.vcgen true

namespace PolyFunTest.Transformers

/- `StateT.lift` through the base computation. -/
example : ⦃ fun _ => True ⦄ (StateT.lift (pure true : Id Bool) : StateT Nat Id Bool)
    ⦃ fun b _ => b = true ⦄ := by
  vcgen

/- A handler written with `StateT.mk` runs its body at the incoming state. -/
example : ⦃ fun _ => True ⦄ (StateT.mk fun s => (pure (true, s + 1) : Id (Bool × Nat)) :
    StateT Nat Id Bool) ⦃ fun _ s => 0 < s ⦄ := by
  vcgen
  simp

/- Running a `StateT` program at a state, with the final state discarded. -/
example : ⦃ True ⦄ ((do
      let b ← StateT.lift (pure true : Id Bool)
      set (1 : Nat)
      pure b : StateT Nat Id Bool).run' 0) ⦃ fun b => b = true ⦄ := by
  vcgen

/- An `OptionT` lift succeeds; running it observes the option. -/
example : ⦃ True ⦄ (OptionT.lift (pure true : Id Bool) : OptionT Id Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen

/- `OptionT.mk` is read through the option its body returns. -/
example : ⦃ True ⦄ (OptionT.mk (pure (some true) : Id (Option Bool)) : OptionT Id Bool).run
    ⦃ fun o => o = some true ⦄ := by
  vcgen
  simp [Lean.Order.pushOption]

/- An `ExceptT` lift succeeds; running it observes the result. -/
example : ⦃ True ⦄ (ExceptT.lift (pure true : Id Bool) : ExceptT String Id Bool).run
    ⦃ fun r => r = .ok true ⦄ := by
  vcgen

/- `ExceptT.mk` is read through the result its body returns. -/
example : ⦃ True ⦄ (ExceptT.mk (pure (.ok true) : Id (Except String Bool)) :
    ExceptT String Id Bool).run ⦃ fun r => r = .ok true ⦄ := by
  vcgen
  simp [Lean.Order.pushExcept]

/- `List.mapM` with an invariant relating the outputs so far to the elements consumed. -/
example : ⦃ True ⦄ ([1, 2, 3].mapM fun n => (pure (n + 1) : Id Nat))
    ⦃ fun bs => bs.length = 3 ⦄ := by
  vcgen invariants
    · fun pref _ bs => bs.length = pref.length
  all_goals simp_all

/- The sequence combinators keep the first, respectively the second, value. -/
example : ⦃ True ⦄ ((pure true : Id Bool) <* (pure 0 : Id Nat)) ⦃ fun b => b = true ⦄ := by
  vcgen

example : ⦃ True ⦄ ((pure 0 : Id Nat) *> (pure true : Id Bool)) ⦃ fun b => b = true ⦄ := by
  vcgen

/-! ## `guard` under a lattice-valued reading

A deterministic monad with no global weakest-precondition instance, read at the extended
naturals through a local ordered algebra, as `PolyFunTest.Do.Exact` sets up; the `Prop` rule
for `guard` does not apply there, and `Spec.guard_OptionT_iInf` does. -/

/-- A deterministic monad with no global weakest-precondition instance. -/
@[expose]
def Det (α : Type) : Type := α

instance : Monad Det where
  pure a := a
  bind x f := f x

instance : LawfulMonad Det :=
  LawfulMonad.mk' Det (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

noncomputable local instance instMAlgOrderedDetENat : MAlgOrdered Det ℕ∞ where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

noncomputable local instance instWPMonadDetENat : WPMonad Det ℕ∞ EStack⟨⟩ :=
  MAlgOrdered.toWPMonad

/- `guard` on a true condition continues, through `Spec.guard_OptionT_iInf`: the branch for the
false condition is ruled out by `decide`. -/
example : ⦃ (3 : ℕ∞) ⦄ (do guard (1 < 2); OptionT.lift (pure 3 : Det ℕ∞) : OptionT Det ℕ∞)
    ⦃ fun n => n; estack⟨fun _ => 0⟩ ⦄ := by
  vcgen
  rename_i h
  exact absurd h.down (by decide)

end PolyFunTest.Transformers
