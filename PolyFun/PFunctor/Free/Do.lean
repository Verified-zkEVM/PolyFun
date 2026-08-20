/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Do.Basic
public import PolyFun.PFunctor.Free.WP

/-!
# Core `Std.Do` Structure for the Free Monad

Together with `PolyFun.Control.Do.Basic`, this file quarantines PolyFun's use of
the core `Std.Do` framework. It equips `FreeM P` with predicate-transformer
semantics in two ways:

* **Through a handler**: `FreeM.wpMonadOfHandler s` interprets programs by
  `FreeM.liftM s` into any monad already carrying a `WPMonad` structure, via
  `MonadHom.transportWPMonad`. Registration is left to the caller.
* **Demonically, with operations uninterpreted**: the *scoped* instances
  `instWPAll` / `instWPMonadAll` interpret `wp⟦x⟧ Q` as "every possible output of
  `x` satisfies `Q`" (the `MonadSupport.toWP` structure at the `.pure` post
  shape). Under `open scoped PFunctor.FreeM.DemonicWP`, the `mvcgen` tactic
  decomposes `do`-programs over `FreeM P`, with `Spec.lift` providing the
  verification condition for an uninterpreted operation: all of its responses
  must satisfy the continuation.

The instances are scoped because downstream libraries register their own
`Std.Do.WP` structures on reducible unfoldings of `FreeM` (for example on oracle
computations); a global instance here would race those registrations.
-/

@[expose] public section

universe uA uB v w

open Std.Do

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}}

/-- Interpret free programs through a handler into a monad with a `WPMonad`
structure. Not an instance — register it scoped or local downstream. -/
@[instance_reducible]
def wpMonadOfHandler {n : Type uB → Type w} {ps : PostShape.{uB}} [Monad n]
    [WPMonad n ps] (s : Handler n P) : WPMonad (FreeM P) ps :=
  (FreeM.liftMHom s).transportWPMonad

namespace DemonicWP

/-- Demonic (all-outputs) predicate-transformer semantics for free programs with
uninterpreted operations, at the `.pure` post shape. -/
scoped instance instWPAll : WP (FreeM P) .pure :=
  MonadSupport.toWP

/-- The demonic semantics respects the monad structure. -/
scoped instance instWPMonadAll : WPMonad (FreeM P) .pure :=
  MonadSupport.toWPMonad

variable {α : Type uB}

/-- The demonic `wp⟦x⟧` is the "always" judgment on the success postcondition. -/
theorem wp_apply_eq (x : FreeM P α) (Q : PostCond α .pure) :
    wp⟦x⟧ Q = ⌜AllOutputs (fun a => (Q.1 a).down) x⌝ :=
  rfl

/-- The demonic triple with trivial precondition is the "always" judgment. -/
theorem triple_iff_allOutputs (x : FreeM P α) (Q : PostCond α .pure) :
    Triple x ⌜True⌝ Q ↔ AllOutputs (fun a => (Q.1 a).down) x := by
  constructor
  · intro h
    exact h trivial
  · intro h
    exact SPred.pure_mono fun _ => h

end DemonicWP

namespace Spec

open DemonicWP

/-- Schematic specification for an uninterpreted operation under the demonic
semantics: the weakest precondition of `FreeM.lift a` demands the postcondition
of *every* response. Registered for `mvcgen`. -/
@[spec]
theorem lift (a : P.A) {Q : PostCond (P.B a) .pure} :
    Triple (FreeM.lift (P := P) a) (⌜∀ b, (Q.1 b).down⌝) Q :=
  SPred.pure_mono fun h b _ => h b

end Spec

end PFunctor.FreeM
