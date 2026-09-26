/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support
public import PolyFun.Control.Monad.Algebra.WP
public import Std.WP

/-!
# Monadic support as core weakest preconditions

The always/some judgments are core predicate transformers at the `Prop` carrier with no
exception layer, built from `MonadAttach` alone: demonically (`toWPDemonic`), `wp x post` is
`AllOutputs post x`; angelically (`toWPAngelic`), it is `SomeOutput post x`. Both extend to
`WPMonad` interpretations satisfying core's inequational laws — the angelic reading has no
counterpart on the older `Std.Do` stack, whose transformers carry conjunctivity as a field. The
demonic reading is conjunctive (`toWPMonadDemonic_wpConjunctive`); the angelic one is not, and
`PolyFunTest/Do/Angelic.lean` pins the counterexample against core's classes. Neither is a global
instance: install them scoped or local where the support semantics is intended, exactly as
`mAlgOrderedPropDemonic` is. The demonic monad laws need only `LawfulMonadAttach`: core's
return-value elimination rules prove them. The angelic laws need the introduction rules of
`ExactMonadAttach`.

`Std.WP.LawfulWPMonadAttach` is soundness of a `WPMonad` interpretation with respect to
lawful attachment: a `wp`-provable postcondition holds at every value the computation can return.
`support_subset_of_wp` and `allOutputs_of_wp` turn any sound triple — including one discharged
by `vcgen` — into a support fact. This additional soundness property is not automatic for
angelic or quantitative interpretations.

The angelic interpretation is a may/existential reading and nothing more: a proof of `wp x post`
exhibits one favourable output, so it has no `LawfulWPMonadAttach` instance (the other outputs
are unconstrained) and no `WPConjunctive` instance (core's `Triple.and`, `Triple.mp`, and
`Triple.observe` do not apply). Empty support makes it false where the demonic reading is
vacuously true. Existential reachability is not a probability bound, and under scheduler
nondeterminism it says only that some favourable schedule exists, nothing about a fixed, fair,
random, or adversarial scheduler.
-/

public section

universe u v w z

open Std.WP
open scoped Lean.Order

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
discharges the all-outputs judgment. Untagged: its antecedent has no first-order pattern for
`grind` to index. -/
theorem allOutputs_of_wp {α : Type u} {x : m α} {P : α → Prop}
    (h : Lean.Order.top ⊑ wp x (fun a => ⌜P a⌝) Lean.Order.top) : AllOutputs P x :=
  fun _ hcan => LawfulWPMonadAttach.of_canReturn_wp hcan h

end Eliminations

section Transformers

variable {m : Type u → Type v} [MonadAttach m]

/-- The demonic (all-outputs) predicate transformer of `m α` at the `Prop` carrier, from
attachment alone: `wp x post` holds when every possible output of `x` satisfies `post`. Not an
instance. -/
@[expose, instance_reducible]
def toWPDemonic (α : Type u) : WP (m α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => AllOutputs post x⟩
  wp_trans_monotone _ _ _ _ _ _ hpost := allOutputs_mono hpost

@[simp]
theorem toWPDemonic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    (toWPDemonic (m := m) α).wp x post epost = AllOutputs post x :=
  rfl

/-- The angelic (some-output) predicate transformer of `m α` at the `Prop` carrier, from
attachment alone: `wp x post` holds when some possible output of `x` satisfies `post`. Not an
instance, and deliberately without `WPConjunctive` or `LawfulWPMonadAttach` companions. -/
@[expose, instance_reducible]
def toWPAngelic (α : Type u) : WP (m α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => SomeOutput post x⟩
  wp_trans_monotone _ _ _ _ _ _ hpost := someOutput_mono hpost

@[simp]
theorem toWPAngelic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    (toWPAngelic (m := m) α).wp x post epost = SomeOutput post x :=
  rfl

end Transformers

section Demonic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

/-- The demonic (all-outputs) interpretation at the `Prop` carrier, `toWPDemonic` with core's
monad laws: `wp x post` holds when every possible output of `x` satisfies `post`. Not an
instance. -/
@[expose, instance_reducible]
def toWPMonadDemonic : WPMonad m Prop EStack⟨⟩ where
  toLawfulMonad := inferInstance
  toWP := toWPDemonic
  pure_le_wp_pure _ _ _ := by
    intro h b hb
    cases LawfulMonadAttach.eq_of_canReturn_pure hb
    exact h
  bind_le_wp_bind _ _ _ _ := by
    intro h b hb
    obtain ⟨a, ha, hab⟩ := LawfulMonadAttach.canReturn_bind_imp' hb
    exact h a ha b hab

@[simp]
theorem toWPMonadDemonic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((toWPMonadDemonic (m := m)).toWP α).wp x post epost = AllOutputs post x :=
  rfl

/-- Core's triple under the demonic interpretation is the guarded "always" judgment. -/
theorem toWPMonadDemonic_triple_iff {α : Type u} (x : m α) (pre : Prop) (post : α → Prop)
    (epost : EStack⟨⟩) :
    @Std.WP.Triple Prop EStack⟨⟩ (m α) α _ _ x ((toWPMonadDemonic (m := m)).toWP α)
        pre post epost ↔
      (pre → AllOutputs post x) := by
  let inst := (toWPMonadDemonic (m := m)).toWP α
  exact ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

/-- The demonic interpretation is conjunctive: "always" distributes over `∧`. -/
theorem toWPMonadDemonic_wpConjunctive {α : Type u} (x : m α) :
    @WPConjunctive (m α) α Prop EStack⟨⟩ _ _ ((toWPMonadDemonic (m := m)).toWP α) x := by
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
    @LawfulWPMonadAttach m Prop EStack⟨⟩ _ _ _ _ _ (toWPMonadDemonic (m := m)) := by
  let inst := toWPMonadDemonic (m := m)
  refine ⟨fun {α x P a} hcan hwp => ?_⟩
  have h : AllOutputs (fun a => ⌜P a⌝) x := Lean.Order.of_top_le_prop hwp
  simpa only [Lean.Order.ofProp_prop_eq] using h a hcan

end Demonic

section Angelic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- The angelic (some-output) interpretation at the `Prop` carrier, `toWPAngelic` with core's
monad laws: `wp x post` holds when some possible output of `x` satisfies `post`. Expressible only
on the inequational stack; not an instance, and neither conjunctive nor sound in the sense of
`LawfulWPMonadAttach` (see the module docstring). -/
@[expose, instance_reducible]
def toWPMonadAngelic : WPMonad m Prop EStack⟨⟩ where
  toLawfulMonad := inferInstance
  toWP := toWPAngelic
  pure_le_wp_pure a post _ := (someOutput_pure post a).mpr
  bind_le_wp_bind x f post _ := fun h => (someOutput_bind post x f).mpr h

@[simp]
theorem toWPMonadAngelic_wp {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((toWPMonadAngelic (m := m)).toWP α).wp x post epost = SomeOutput post x :=
  rfl

/-- Core's triple under the angelic interpretation is the guarded "sometimes" judgment. -/
theorem toWPMonadAngelic_triple_iff {α : Type u} (x : m α) (pre : Prop) (post : α → Prop)
    (epost : EStack⟨⟩) :
    @Std.WP.Triple Prop EStack⟨⟩ (m α) α _ _ x ((toWPMonadAngelic (m := m)).toWP α)
        pre post epost ↔
      (pre → SomeOutput post x) := by
  let inst := (toWPMonadAngelic (m := m)).toWP α
  exact ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

end Angelic

end MonadAttach
