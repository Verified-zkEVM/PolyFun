/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support
public import PolyFun.Control.Monad.Algebra.WP
public import Std.Internal.Do

/-!
# Exact support as core weakest preconditions

The always/some judgments of a monad with exact support are core `WPMonad` interpretations at
the `Prop` carrier with no exception layer: demonically, `wp x post` is `AllOutputs post x`;
angelically, it is `SomeOutput post x`. Both satisfy core's inequational laws — the angelic
reading has no counterpart on the older `Std.Do` stack, whose transformers carry conjunctivity
as a field. The demonic reading is conjunctive (`toWPMonadDemonic_wpConjunctive`); the angelic
one is not, and `PolyFunTest/Control/MonadAttach.lean` pins the counterexample. Neither is a
global instance: install them scoped or local where the support semantics is intended, exactly
as `mAlgOrderedPropDemonic` is.

`LawfulWPMonadAttach` mirrors, field for field, the class Lean master ships in
`Std/WP/Monad/Sound.lean` (public from v4.35): a `wp`-provable postcondition holds at every
value the computation can return. It lives in the `Std.Internal.Do` namespace so that the v4.35
rename of that namespace to `Std.WP` deletes it. `support_subset_of_wp` and `allOutputs_of_wp`
turn any sound triple — including one discharged by `vcgen` — into a support fact.
-/

public section

universe u v w z

open Std.Internal.Do
open scoped Lean.Order

namespace Std.Internal.Do

/-- Soundness of the weakest precondition interpretation of `m`: a postcondition that `wp` proves
holds of every value the program returns. Mirrors `Std.WP.LawfulWPMonadAttach` on Lean master. -/
class LawfulWPMonadAttach (m : Type u → Type v) (Pred : outParam (Type w))
    (EPred : outParam (Type z)) [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] where
  /-- From a `wp`-provable postcondition and a `MonadAttach.CanReturn` witness, conclude `P` at
  that value. -/
  of_canReturn_wp {α : Type u} {x : m α} {P : α → Prop} {a : α} :
    MonadAttach.CanReturn x a →
      (Lean.Order.top ⊑ wp x (fun a => ⌜P a⌝) Lean.Order.top) → P a

end Std.Internal.Do

namespace MonadAttach

section Eliminations

variable {m : Type u → Type v} [Monad m] [MonadAttach m] [LawfulMonadAttach m]
  {Pred : Type w} {EPred : Type z} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
  [LawfulWPMonadAttach m Pred EPred]

/-- Any sound weakest-precondition proof bounds the support. -/
theorem support_subset_of_wp {α : Type u} {x : m α} {P : α → Prop}
    (h : Lean.Order.top ⊑ wp x (fun a => ⌜P a⌝) Lean.Order.top) : support x ⊆ {a | P a} :=
  fun _ hcan => LawfulWPMonadAttach.of_canReturn_wp hcan h

/-- The "always" phrasing of `support_subset_of_wp`: a sound weakest-precondition proof
discharges the almost-sure judgment. Untagged: its antecedent has no first-order pattern for
`grind` to index. -/
theorem allOutputs_of_wp {α : Type u} {x : m α} {P : α → Prop}
    (h : Lean.Order.top ⊑ wp x (fun a => ⌜P a⌝) Lean.Order.top) : AllOutputs P x :=
  fun _ hcan => LawfulWPMonadAttach.of_canReturn_wp hcan h

end Eliminations

section Demonic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- The demonic (all-outputs) interpretation at the `Prop` carrier: `wp x post` holds when every
possible output of `x` satisfies `post`. Not an instance. -/
@[expose, instance_reducible]
def toWPMonadDemonic : WPMonad m Prop EPost.Nil where
  toLawfulMonad := inferInstance
  toWP _ :=
    { wpTrans := fun x => ⟨fun post _ => AllOutputs post x⟩
      wp_trans_monotone := fun _ _ _ _ _ _ hpost => allOutputs_mono hpost }
  pure_le_wp_pure a post _ := (allOutputs_pure post a).mpr
  bind_le_wp_bind x f post _ := fun h => (allOutputs_bind post x f).mpr fun a ha => h a ha

@[simp]
theorem toWPMonadDemonic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EPost.Nil) :
    ((toWPMonadDemonic (m := m)).toWP α).wp x post epost = AllOutputs post x :=
  rfl

/-- Core's triple under the demonic interpretation is the guarded "always" judgment. -/
theorem toWPMonadDemonic_triple_iff {α : Type u} (x : m α) (pre : Prop) (post : α → Prop)
    (epost : EPost.Nil) :
    @Std.Internal.Do.Triple Prop EPost.Nil (m α) α _ _ x ((toWPMonadDemonic (m := m)).toWP α)
        pre post epost ↔
      (pre → AllOutputs post x) := by
  let inst := (toWPMonadDemonic (m := m)).toWP α
  exact ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

/-- The demonic interpretation is conjunctive: "always" distributes over `∧`. -/
theorem toWPMonadDemonic_wpConjunctive {α : Type u} (x : m α) :
    @WPConjunctive (m α) α Prop EPost.Nil _ _ ((toWPMonadDemonic (m := m)).toWP α) x := by
  let inst := (toWPMonadDemonic (m := m)).toWP α
  refine ⟨fun Q₁ Q₂ _ _ => ?_⟩
  change Lean.Order.meet (AllOutputs Q₁ x) (AllOutputs Q₂ x) →
    AllOutputs (Lean.Order.meet Q₁ Q₂) x
  rw [Lean.Order.meet_prop_eq_and]
  rintro ⟨h₁, h₂⟩ a ha
  rw [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and]
  exact ⟨h₁ a ha, h₂ a ha⟩

/-- The demonic interpretation is sound in core's sense: `CanReturn` is exactly the support. -/
theorem toWPMonadDemonic_lawfulWPMonadAttach :
    @LawfulWPMonadAttach m Prop EPost.Nil _ _ _ _ _ (toWPMonadDemonic (m := m)) := by
  let inst := toWPMonadDemonic (m := m)
  refine ⟨fun {α x P a} hcan hwp => ?_⟩
  have h : AllOutputs (fun a => ⌜P a⌝) x := Lean.Order.of_top_le_prop hwp
  simpa only [Lean.Order.ofProp_prop_eq] using h a hcan

end Demonic

section Angelic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- The angelic (some-output) interpretation at the `Prop` carrier: `wp x post` holds when some
possible output of `x` satisfies `post`. Expressible only on the inequational stack; not an
instance. -/
@[expose, instance_reducible]
def toWPMonadAngelic : WPMonad m Prop EPost.Nil where
  toLawfulMonad := inferInstance
  toWP _ :=
    { wpTrans := fun x => ⟨fun post _ => SomeOutput post x⟩
      wp_trans_monotone := fun _ _ _ _ _ _ hpost => someOutput_mono hpost }
  pure_le_wp_pure a post _ := (someOutput_pure post a).mpr
  bind_le_wp_bind x f post _ := fun h => (someOutput_bind post x f).mpr h

@[simp]
theorem toWPMonadAngelic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EPost.Nil) :
    ((toWPMonadAngelic (m := m)).toWP α).wp x post epost = SomeOutput post x :=
  rfl

/-- Core's triple under the angelic interpretation is the guarded "sometimes" judgment. -/
theorem toWPMonadAngelic_triple_iff {α : Type u} (x : m α) (pre : Prop) (post : α → Prop)
    (epost : EPost.Nil) :
    @Std.Internal.Do.Triple Prop EPost.Nil (m α) α _ _ x ((toWPMonadAngelic (m := m)).toWP α)
        pre post epost ↔
      (pre → SomeOutput post x) := by
  let inst := (toWPMonadAngelic (m := m)).toWP α
  exact ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

end Angelic

end MonadAttach
