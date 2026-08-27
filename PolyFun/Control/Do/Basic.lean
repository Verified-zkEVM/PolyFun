/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Tactic.Do
public import PolyFun.Control.Monad.Hom
public import PolyFun.Control.Monad.Support

/-!
# Core `Std.Do` Enablement

This file is the *only* PolyFun root importing `Std.Tactic.Do`; every other use of
the core `Std.Do` weakest-precondition framework and the `mvcgen` tactic must go
through it (or through `PolyFun.PFunctor.Free.Do`), keeping the dependency on the
evolving upstream API quarantined.

It provides constructions — deliberately not instances — that transport core
`Std.Do` structure onto PolyFun's monads:

* `MonadHom.transportWP` / `MonadHom.transportWPMonad` pull a `WP`/`WPMonad`
  structure back along a monad morphism `F : m →ᵐ n`, so a monad that interprets
  into an `mvcgen`-ready stack inherits its predicate-transformer semantics.
* `MonadAttach.toWP` / `MonadAttach.toWPMonad` give any monad with exact support
  the demonic (almost-sure) interpretation at the `.pure` post shape: `wp x Q`
  holds when every possible output of `x` satisfies `Q`. `MonadAttach.toWPSound`
  proves that interpretation sound in core's sense, with `attach` supplying the
  `Ensures` witness.
* `MonadAttach.support_subset_of_wp` / `allOutputs_of_wp` go the other way: *any*
  `WPSound` predicate-transformer semantics bounds the support, so an
  `mvcgen`-discharged triple becomes a support fact in one step. These need only
  `LawfulMonadAttach`, so they also apply to `StateT`/`ReaderT`/`EStateM`, where
  `ExactMonadAttach` is unavailable.

Downstream libraries choose where to register these (scoped or local); a global
instance here would clash with registrations on reducible unfoldings of the same
monads downstream.

The demonic reading is the *only* one expressible here, and the reason is
structural. `Std.Do.PredTrans` carries conjunctivity as a structure field, stated
as a bi-entailment `t (Q₁ ∧ₚ Q₂) ⊣⊢ₛ t Q₁ ∧ t Q₂`. `AllOutputs` distributes over
`∧` in both directions, so `toWP` can discharge it; `SomeOutput` distributes only
left-to-right, since two different outputs may witness the two conjuncts
separately. There is therefore no angelic `Std.Do.WP`, and the angelic reading
stays at the `MAlgOrdered` level, whose `μ_bind_mono` asks only for monotonicity.
`PolyFunTest/Control/MonadAttach.lean` pins both directions and the failure.

This file depends on `Std.Do.Internal.Ensures` only through `WPSound`'s own field
type. Reasoning here goes through `WPSound.of_wp_canReturn`, which lives in the
stable `Std.Do` namespace; core's `Internal.MayReturn.canReturn_eq` (which proves
`CanReturn` *is* the intrinsic strongest postcondition) is cited but not depended
upon.

Both of those are on a known clock. Upstream of this pin, core promotes its
lattice-generic `Std.Internal.Do` tree to a public `Std.WP` (shipping in v4.35,
not v4.34), replaces `WPSound` with `Std.WP.LawfulWPMonadAttach` — whose single
field concludes from a `MonadAttach.CanReturn` witness directly, dropping the
`Ensures` formulation — and deprecates `mvcgen` in favour of `vcgen`. That stack
also drops conjunctivity from `PredTrans`, re-introducing it as the opt-in,
one-directional `WPConjunctive`, which is what would unblock an angelic bridge.
The elimination direction below is already stated against `CanReturn`, so it
carries over as a rename.
-/

@[expose] public section

universe u v w

open Std.Do

namespace MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {ps : PostShape.{u}}

/-- Transport a core `Std.Do.WP` structure along a monad morphism: interpret
`x : m α` by the predicate transformer of its image `F x`. Not an instance —
downstream registers it at chosen carriers. -/
@[instance_reducible]
def transportWP (F : m →ᵐ n) [WP n ps] : WP m ps where
  wp x := WP.wp (F x)

/-- The transported structure is a `WPMonad` whenever the target is and the
source is a lawful monad. Not an instance. -/
@[instance_reducible]
def transportWPMonad (F : m →ᵐ n) [LawfulMonad m] [WPMonad n ps] : WPMonad m ps where
  toLawfulMonad := inferInstance
  toWP := F.transportWP
  wp_pure a := by
    change WP.wp (F (pure a)) = _
    rw [F.mmap_pure]
    exact WPMonad.wp_pure a
  wp_bind x f := by
    change WP.wp (F (x >>= f)) = _
    rw [F.mmap_bind]
    exact WPMonad.wp_bind (F x) fun a => F (f a)

end MonadHom

namespace MonadAttach

section Demonic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
  [ExactMonadAttach m]

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
theorem allOutputs_postCond_and {α : Type u} (x : m α)
    (Q₁ Q₂ : PostCond α .pure) :
    AllOutputs (fun a => ((Q₁.and Q₂).1 a).down) x ↔
      AllOutputs (fun a => (Q₁.1 a).down) x ∧ AllOutputs (fun a => (Q₂.1 a).down) x := by
  rw [← allOutputs_and]
  exact Iff.of_eq (congrArg (AllOutputs · x) (funext fun a => rfl))

/-- The demonic (almost-sure) `Std.Do.WP` structure of a supported monad at the
`.pure` post shape: `wp x Q` asserts that every possible output of `x` satisfies
the success postcondition. Not an instance. -/
@[instance_reducible]
def toWP : WP m .pure where
  wp x :=
    { trans := fun Q => ⌜AllOutputs (fun a => (Q.1 a).down) x⌝
      conjunctiveRaw := fun Q₁ Q₂ =>
        SPred.pure_congr (allOutputs_postCond_and x Q₁ Q₂) }

/-- The demonic interpretation is a `WPMonad` whenever the support is exact.
Not an instance. -/
@[instance_reducible]
def toWPMonad : WPMonad m .pure where
  toLawfulMonad := inferInstance
  toWP := MonadAttach.toWP
  wp_pure a := by
    ext Q
    exact allOutputs_pure _ a
  wp_bind x f := by
    ext Q
    exact allOutputs_bind _ x f

/-! ### Soundness in core's sense

`attach` is exactly the witness `Std.Do`'s `Ensures` asks for: decorate the
computation's results with their reachability proofs, then re-tag those proofs
with the postcondition, which the "always" judgment supplies pointwise. -/

omit [MonadAttach m] [ExactMonadAttach m] in
theorem erasesTo_of_map_eq {α : Type u} {P : α → Prop} {y : m (Subtype P)} {x : m α}
    (h : Subtype.val <$> y = x) : Std.Do.Internal.ErasesTo y x :=
  ⟨fun {_} k => by rw [← h, bind_map_left]⟩

omit [ExactMonadAttach m] in
/-- An "always" judgment yields the `Ensures` witness core's soundness class wants.

Stated at `WeaklyLawfulMonadAttach` rather than `ExactMonadAttach`: the witness is built
from `attach` and its bind-faithfulness alone, and needs nothing about how possible
outputs compose. That matters because `StateT`, `ReaderT`, and `EStateM` have the weak
class but provably not the exact one. -/
theorem ensures_of_allOutputs {α : Type u} [WeaklyLawfulMonadAttach m] {x : m α}
    {P : α → Prop} (h : AllOutputs P x) : Std.Do.Internal.Ensures P x :=
  ⟨⟨(fun z : Subtype (CanReturn x) => (⟨z.1, h z.1 z.2⟩ : Subtype P)) <$> MonadAttach.attach x,
    erasesTo_of_map_eq (by rw [Functor.map_map]; exact WeaklyLawfulMonadAttach.map_attach)⟩⟩

omit [ExactMonadAttach m] in
/-- The demonic interpretation is sound in core's sense. Not an instance.

Like `ensures_of_allOutputs` this needs only the weak class, so the *soundness* of the
demonic reading is available for every monad core equips — including the stateful ones.
What exactness buys is `toWPMonad`, i.e. the `wp_bind` law, not soundness. -/
theorem toWPSound [WeaklyLawfulMonadAttach m] :
    letI := toWP (m := m); WPSound m .pure :=
  letI := toWP (m := m)
  { ensures_of_wp := fun {_ _ _} hwp => ensures_of_allOutputs (hwp True.intro) }

end Demonic

/-! ### From weakest preconditions back to supports

The converse direction needs no exactness — only that `CanReturn` is the strongest
postcondition — so it applies to every monad core equips, including the stateful
ones where `ExactMonadAttach` fails. -/

section OfWP

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
  [LawfulMonadAttach m] {ps : PostShape.{u}} [WP m ps] [WPSound m ps]

/-- Any `WPSound` predicate-transformer semantics bounds the support. -/
theorem support_subset_of_wp {α : Type u} {x : m α} {P : α → Prop}
    (h : ⊢ₛ wp⟦x⟧ (⇓?a => ⌜P a⌝)) : support x ⊆ {a | P a} :=
  fun _ hcan => WPSound.of_wp_canReturn (P := P) hcan h

/-- The "always" phrasing of `support_subset_of_wp`: a weakest-precondition proof
discharges the almost-sure judgment. -/
theorem allOutputs_of_wp {α : Type u} {x : m α} {P : α → Prop}
    (h : ⊢ₛ wp⟦x⟧ (⇓?a => ⌜P a⌝)) : AllOutputs P x :=
  fun _ hcan => WPSound.of_wp_canReturn (P := P) hcan h

end OfWP

end MonadAttach
