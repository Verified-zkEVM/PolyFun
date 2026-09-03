/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP.Upstream
public import Std.Tactic.Do

/-!
# Core Program Logic for the Free Monad

The tactic-tier module of the `Std.Do` quarantine for free programs. It registers *scoped*
core `WPMonad` interpretations of `FreeM P` and the `@[spec]` lemmas that let `vcgen` decompose
`do` programs over `FreeM P` with uninterpreted operations:

* under `open scoped PFunctor.FreeM.DemonicWP`, `wp x Q E` is "every possible output of `x`
  satisfies `Q`" (`MonadAttach.toWPMonadDemonic`); it is conjunctive and sound, and
  `Spec.lift` demands the postcondition of *every* response to an operation;
* under `open scoped PFunctor.FreeM.AngelicWP`, `wp x Q E` is "some possible output of `x`
  satisfies `Q`" (`MonadAttach.toWPMonadAngelic`), and `Spec.lift_angelic` asks for *some*
  response;
* through a handler, `FreeM.wpMonadOfHandler s` installed locally lets `Spec.lift_ofHandler`
  reduce an operation to the handler's `wp`.

`vcgen` matches `@[spec]` lemmas structurally, so `Spec.lift`, whose value type is the dependent
`P.B a`, applies wherever the goal's value type is syntactically `P.B a`: under `bind`, where the
type comes from the operation itself. An operation in tail position, after the value type has
been normalized to a concrete type, is left as a `wp` goal that rewriting with
`DemonicWP.wp_apply_eq` and `FreeM.allOutputs_lift` finishes.

The instances are scoped because downstream libraries register their own core interpretations
on reducible unfoldings of `FreeM` (oracle computations, for one); a global instance here would
race those registrations. This module imports `Std.Tactic.Do` for the `@[spec]` attribute
syntax.
-/

@[expose] public section

universe uA uB v w z

open Std.Internal.Do MonadAttach
open scoped Lean.Order

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}}

namespace DemonicWP

/-- Demonic (all-outputs) core interpretation of free programs with uninterpreted
operations. -/
scoped instance instWPMonadAll : WPMonad (FreeM P) Prop EPost.Nil :=
  toWPMonadDemonic

/-- The demonic interpretation is sound: a `wp`-provable postcondition holds at every possible
output. -/
scoped instance instLawfulWPMonadAttachAll : LawfulWPMonadAttach (FreeM P) Prop EPost.Nil :=
  toWPMonadDemonic_lawfulWPMonadAttach

/-- The demonic interpretation is conjunctive at every program. -/
scoped instance instWPConjunctiveAll {α : Type uB} (x : FreeM P α) : WPConjunctive x :=
  toWPMonadDemonic_wpConjunctive x

variable {α : Type uB}

/-- The demonic `wp` is the "always" judgment. -/
theorem wp_apply_eq (x : FreeM P α) (post : α → Prop) (epost : EPost.Nil) :
    wp x post epost = AllOutputs post x :=
  rfl

/-- The demonic triple is the guarded "always" judgment. -/
theorem triple_iff_allOutputs (x : FreeM P α) (pre : Prop) (post : α → Prop)
    (epost : EPost.Nil) :
    Triple x pre post epost ↔ (pre → AllOutputs post x) :=
  ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

end DemonicWP

namespace AngelicWP

/-- Angelic (some-output) core interpretation of free programs with uninterpreted
operations. -/
scoped instance instWPMonadSome : WPMonad (FreeM P) Prop EPost.Nil :=
  toWPMonadAngelic

variable {α : Type uB}

/-- The angelic `wp` is the "sometimes" judgment. -/
theorem wp_apply_eq (x : FreeM P α) (post : α → Prop) (epost : EPost.Nil) :
    wp x post epost = SomeOutput post x :=
  rfl

end AngelicWP

namespace Spec

section Demonic

open DemonicWP

/-- An uninterpreted operation, demonically: the weakest precondition of `FreeM.lift a` demands
the postcondition of every response. -/
@[spec]
theorem lift (a : P.A) (Q : P.B a → Prop) (E : EPost.Nil) :
    Triple (FreeM.lift (P := P) a) (∀ b, Q b) Q E :=
  ⟨fun h b _ => h b⟩

/-- A node written with the constructor: every continuation must meet the postcondition. -/
@[spec]
theorem liftBind {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) (Q : α → Prop)
    (E : EPost.Nil) :
    Triple (FreeM.liftBind a r) (∀ b, wp (r b) Q E) Q E :=
  ⟨fun h => (allOutputs_liftBind Q a r).mpr h⟩

end Demonic

section Angelic

open AngelicWP

/-- An uninterpreted operation, angelically: some response meets the postcondition. -/
@[spec]
theorem lift_angelic (a : P.A) (Q : P.B a → Prop) (E : EPost.Nil) :
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
      ((wpMonadOfHandler s).toWP _) (wp (s a) Q E) Q E := by
  let inst := wpMonadOfHandler (P := P) s
  refine ⟨?_⟩
  change wp (s a) Q E ⊑ wp ((FreeM.lift a).liftM s) Q E
  rw [FreeM.liftM_lift]

end Handler

end Spec

end PFunctor.FreeM
