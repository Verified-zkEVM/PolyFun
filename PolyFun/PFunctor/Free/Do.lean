/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP.Upstream

/-!
# Core Program Logic for the Free Monad

Scoped core `WPMonad` interpretations of `FreeM P`, and the `@[spec]` lemmas that let `vcgen`
decompose `do` programs over `FreeM P` with uninterpreted operations:

* under `open scoped PFunctor.FreeM.DemonicWP`, `wp x Q E` is "every possible output of `x`
  satisfies `Q`" (`MonadAttach.toWPMonadDemonic`); it is conjunctive and sound, by the global
  instances keyed on that construction, and the scope's rule `Spec.lift` demands the
  postcondition of *every* response to an operation;
* under `open scoped PFunctor.FreeM.AngelicWP`, `wp x Q E` is "some possible output of `x`
  satisfies `Q`" (`MonadAttach.toWPMonadAngelic`), and the scope's rule `Spec.lift_angelic` asks
  for *some* response;
* through a handler, `FreeM.wpMonadOfHandler s` installed locally lets `Spec.lift_ofHandler`
  reduce an operation to the handler's `wp`;
* under the reading of a spec, `OpSpec.toWPMonad Φ hΦ`, `Spec.lift_lower` reads an operation as
  `Φ` applied to the postcondition. It is registered at low priority, below rules for particular
  specs such as `Spec.lift_budget`. Under the expectation reading
  (`PolyFun.PFunctor.Free.Measure.WP`), whose spec is the integral against the answer measure, the
  precondition is that integral, and `vcgen` leaves the continuation under it;
* under the upper-bound reading of a spec, `OpSpec.toUpperWPMonad Φ hΦ` installed locally lets
  `Spec.lift_upper` read an operation as `Φ` in the dual order. For a charge
  (`PolyFun.PFunctor.Free.WP.Charge`) the precondition is the call's charge plus the supremum of
  the continuation, so `vcgen` decomposes the call and leaves the continuation under the supremum.
  `Spec.liftBind_lower` and `Spec.liftBind_upper` are the rules for the constructor spelling.

`Spec.lift`, `Spec.liftBind` and `Spec.lift_angelic` are stated for one reading each, so each is
registered `scoped` in the scope of its reading. `Spec.bind` holds for every interpretation of
`FreeM P`, and `Spec.lift_ofHandler` and `Spec.lift_upper` are stated against the construction
they read, for all its parameters; these three are registered globally.

The instances are scoped because downstream libraries register their own core interpretations
on reducible unfoldings of `FreeM` (oracle computations, for one); a global instance here would
race those registrations.
-/

@[expose] public section

universe uA uB v w z

open Std.WP MonadAttach
open scoped Lean.Order

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}}

namespace DemonicWP

/-- Demonic (all-outputs) core interpretation of free programs with uninterpreted
operations. Its conjunctivity and soundness are the global instances
`MonadAttach.instWPConjunctiveToWPMonadDemonic` and
`MonadAttach.instLawfulWPMonadAttachToWPMonadDemonic`. -/
scoped instance instWPMonad : WPMonad (FreeM P) Prop EStack⟨⟩ :=
  toWPMonadDemonic

variable {α : Type uB}

/-- The demonic `wp` is the "always" judgment. -/
theorem wp_eq_allOutputs (x : FreeM P α) (post : α → Prop) (epost : EStack⟨⟩) :
    wp x post epost = AllOutputs post x :=
  rfl

@[deprecated (since := "2026-11-16")] alias wp_apply_eq := wp_eq_allOutputs

/-- The demonic triple is the guarded "always" judgment. -/
theorem triple_iff_allOutputs (x : FreeM P α) (pre : Prop) (post : α → Prop)
    (epost : EStack⟨⟩) :
    Triple x pre post epost ↔ (pre → AllOutputs post x) :=
  Triple.iff

end DemonicWP

namespace AngelicWP

/-- Angelic (some-output) core interpretation of free programs with uninterpreted
operations. -/
scoped instance instWPMonad : WPMonad (FreeM P) Prop EStack⟨⟩ :=
  toWPMonadAngelic

variable {α : Type uB}

/-- The angelic `wp` is the "sometimes" judgment. -/
theorem wp_eq_someOutput (x : FreeM P α) (post : α → Prop) (epost : EStack⟨⟩) :
    wp x post epost = SomeOutput post x :=
  rfl

@[deprecated (since := "2026-11-16")] alias wp_apply_eq := wp_eq_someOutput

end AngelicWP

namespace Spec

/-- Sequencing for the direct `FreeM.bind` spelling, for any core interpretation.

Core's generic bind specification is indexed under `Bind.bind`; `vcgen` also needs this
registration for cslib's concrete `FreeM.bind` head. The proof is core's bind rule. -/
@[spec]
theorem bind {α β : Type uB} {Pred : Type v} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WPMonad (FreeM P) Pred EPred]
    (x : FreeM P α) (f : α → FreeM P β) (Q : β → Pred) (E : EPred) :
    Triple (x.bind f) (wp x (fun a => wp (f a) Q E) E) Q E :=
  Std.WP.Spec.bind x f

section Demonic

open DemonicWP

/-- An uninterpreted operation, demonically: the weakest precondition of `FreeM.lift a` demands
the postcondition of every response. Registered in the scope `PFunctor.FreeM.DemonicWP`. -/
theorem lift (a : P.A) (Q : P.B a → Prop) (E : EStack⟨⟩) :
    Triple (FreeM.lift (P := P) a) (∀ b, Q b) Q E :=
  ⟨fun h b _ => h b⟩

/-- A node written with the constructor: every continuation must meet the postcondition.
Registered in the scope `PFunctor.FreeM.DemonicWP`. -/
theorem liftBind {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) (Q : α → Prop)
    (E : EStack⟨⟩) :
    Triple (FreeM.liftBind a r) (∀ b, wp (r b) Q E) Q E :=
  ⟨fun h => (allOutputs_liftBind Q a r).mpr h⟩

end Demonic

section Angelic

open AngelicWP

/-- An uninterpreted operation, angelically: some response meets the postcondition. Registered in
the scope `PFunctor.FreeM.AngelicWP`. -/
theorem lift_angelic (a : P.A) (Q : P.B a → Prop) (E : EStack⟨⟩) :
    Triple (FreeM.lift (P := P) a) (∃ b, Q b) Q E :=
  ⟨fun ⟨b, hb⟩ => ⟨b, by rw [← mem_support, support_lift]; exact Set.mem_univ b, hb⟩⟩

end Angelic

section Handler

variable {n : Type uB → Type w} [Monad n] {Pred : Type v} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]

/-- Through a handler, an operation's weakest precondition is the handler's. Stated against the
transported interpretation explicitly; it applies once `wpMonadOfHandler s` is installed. -/
@[spec]
theorem lift_ofHandler (s : Handler n P) (a : P.A) (Q : P.B a → Pred) (E : EPred) :
    @Triple Pred EPred (FreeM P (P.B a)) (P.B a) _ _ (FreeM.lift (P := P) a)
      ((wpMonadOfHandler s).toWP _) (wp (s a) Q E) Q E :=
  WP.triple_of_le_wp _ <| by rw [wpMonadOfHandler_wp, FreeM.liftM_lift]

end Handler

section Lower

/-- Under the reading of a spec, an operation's weakest precondition is the spec's transformer
applied to the postcondition. Stated against the explicit interpretation; it applies once
`OpSpec.toWPMonad Φ hΦ` is installed, or a reading defined as one, such as the expectation reading
of `PolyFun.PFunctor.Free.Measure.WP`. Registered at low priority, so that a rule for a particular
spec, such as `Spec.lift_budget`, takes precedence when it is registered or passed to `vcgen`. -/
@[spec low]
theorem lift_lower {l : Type uB} [CompleteLattice l] (Φ : OpSpec P l) (hΦ : Φ.Monotone)
    (a : P.A) (Q : P.B a → l) (E : EStack⟨⟩) :
    @Triple l EStack⟨⟩ (FreeM P (P.B a)) (P.B a) _ _ (FreeM.lift (P := P) a)
      ((Φ.toWPMonad hΦ).toWP _) (Φ a Q) Q E := by
  let inst := Φ.toWPMonad hΦ
  refine ⟨?_⟩
  change Φ a Q ⊑ ((Φ.toWPMonad hΦ).toWP _).wp (FreeM.lift (P := P) a) Q E
  rw [OpSpec.toWPMonad_wp, FreeM.wpFold_lift]

/-- Under the reading of a spec, a node in constructor spelling applies the spec's transformer to
the weakest preconditions of its continuations. Registered at low priority, as `Spec.lift_lower`
is. -/
@[spec low]
theorem liftBind_lower {α : Type v} {l : Type v} [CompleteLattice l] (Φ : OpSpec P l)
    (hΦ : Φ.Monotone) (a : P.A) (r : P.B a → FreeM P α) (Q : α → l) (E : EStack⟨⟩) :
    @Triple l EStack⟨⟩ (FreeM P α) α _ _ (FreeM.liftBind a r) ((Φ.toWPMonad hΦ).toWP α)
      (Φ a fun b => ((Φ.toWPMonad hΦ).toWP α).wp (r b) Q E) Q E := by
  let inst := Φ.toWPMonad hΦ
  refine ⟨?_⟩
  change _ ⊑ ((Φ.toWPMonad hΦ).toWP α).wp (FreeM.liftBind a r) Q E
  simp only [OpSpec.toWPMonad_wp]
  exact Lean.Order.PartialOrder.rel_refl

end Lower

section Upper

variable {l : Type uB} [CompleteLattice l]

/-- Under the upper-bound reading of a spec, an operation's weakest precondition is the spec's
transformer read in the dual order. Stated against the explicit interpretation; it applies once
`OpSpec.toUpperWPMonad Φ hΦ` is installed. -/
@[spec]
theorem lift_upper (Φ : OpSpec P l) (hΦ : Φ.Monotone) (a : P.A) (Q : P.B a → lᵒᵈ)
    (E : EStack⟨⟩ᵒᵈ) :
    @Triple lᵒᵈ EStack⟨⟩ᵒᵈ (FreeM P (P.B a)) (P.B a) _ _ (FreeM.lift (P := P) a)
      ((Φ.toUpperWPMonad hΦ).toWP _)
      (OrderDual.toDual (Φ a fun b => OrderDual.ofDual (Q b))) Q E :=
  WP.triple_of_le_wp _ <| by
    rw [OpSpec.toUpperWPMonad_wp, FreeM.wpFold_lift]
    exact Lean.Order.PartialOrder.rel_refl

end Upper

/-- Under the upper-bound reading of a spec, a node in constructor spelling applies the spec's
transformer, in the dual order, to the weakest preconditions of its continuations. -/
@[spec]
theorem liftBind_upper {α : Type v} {l : Type v} [CompleteLattice l] (Φ : OpSpec P l)
    (hΦ : Φ.Monotone) (a : P.A) (r : P.B a → FreeM P α) (Q : α → lᵒᵈ) (E : EStack⟨⟩ᵒᵈ) :
    @Triple lᵒᵈ EStack⟨⟩ᵒᵈ (FreeM P α) α _ _ (FreeM.liftBind a r) ((Φ.toUpperWPMonad hΦ).toWP α)
      (OrderDual.toDual
        (Φ a fun b => OrderDual.ofDual (((Φ.toUpperWPMonad hΦ).toWP α).wp (r b) Q E))) Q E := by
  let inst := Φ.toUpperWPMonad hΦ
  refine ⟨?_⟩
  change _ ⊑ ((Φ.toUpperWPMonad hΦ).toWP α).wp (FreeM.liftBind a r) Q E
  simp only [OpSpec.toUpperWPMonad_wp, OrderDual.ofDual_toDual]
  exact Lean.Order.PartialOrder.rel_refl

end Spec

/-! ## Rules of the support readings -/

namespace DemonicWP

attribute [scoped spec] Spec.lift Spec.liftBind

end DemonicWP

namespace AngelicWP

attribute [scoped spec] Spec.lift_angelic

end AngelicWP

end PFunctor.FreeM
