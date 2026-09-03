/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.PFunctor.Free.Support
public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Hom.WP

/-!
# Free Programs as Core Weakest-Precondition Monads

Two ways to give `FreeM P` a core `WPMonad` interpretation, both constructions rather than
instances (`PolyFun.PFunctor.Free.Do` registers the scoped ones):

* **syntactically**, from a per-operation spec `Φ : OpSpec P l`: `OpSpec.toWPMonad` is the
  ordered algebra `OpSpec.toMAlgOrdered` seen through `MAlgOrdered.toWPMonad`, and its `wp` is the
  fold `wpFold Φ`;
* **through a handler** `s : Handler n P` into a monad already carrying a `WPMonad`:
  `FreeM.wpMonadOfHandler s` is the interpretation transported along `FreeM.liftMHom s`, and its
  `wp` is the target's `wp` of the interpreted program.

`wpFold_le_wp_liftM` is the soundness of per-operation specs against a handler stated over any
core `WPMonad`, the generic form of `wpFold_le_wpVia`; it needs only the inequational `bind` law.
-/

@[expose] public section

universe uA uB v w z

open Std.Internal.Do

namespace PFunctor

variable {P : PFunctor.{uA, uB}}

namespace OpSpec

variable {l : Type v} [CompleteLattice l]

/-- The core interpretation of free programs induced by a monotone per-operation spec. -/
@[instance_reducible]
def toWPMonad (Φ : OpSpec P l) (hΦ : Φ.Mono) : WPMonad (FreeM P) l EPost.Nil :=
  letI := Φ.toMAlgOrdered hΦ
  MAlgOrdered.toWPMonad

/-- Its `wp` is the syntactic fold. -/
theorem toWPMonad_wp (Φ : OpSpec P l) (hΦ : Φ.Mono) {α : Type v} (x : FreeM P α) (post : α → l)
    (epost : EPost.Nil) :
    ((Φ.toWPMonad hΦ).toWP α).wp x post epost = FreeM.wpFold Φ x post := by
  change (letI := Φ.toMAlgOrdered hΦ; MAlgOrdered.wp x post) = _
  exact FreeM.wp_toMAlgOrdered Φ hΦ x post

end OpSpec

namespace FreeM

section Handler

variable {n : Type uB → Type w} [Monad n] {Pred : Type v} {EPred : Type z}
  [Assertion Pred] [Assertion EPred]

/-- Interpret free programs through a handler into a monad with a core `WPMonad` structure. -/
@[instance_reducible]
def wpMonadOfHandler [WPMonad n Pred EPred] (s : Handler n P) : WPMonad (FreeM P) Pred EPred :=
  (FreeM.liftMHom s).transportWPMonad

/-- The transported `wp` is the target's `wp` of the interpreted program. -/
theorem wpMonadOfHandler_wp [WPMonad n Pred EPred] (s : Handler n P) {α : Type uB}
    (x : FreeM P α) (post : α → Pred) (epost : EPred) :
    ((wpMonadOfHandler s).toWP α).wp x post epost = wp (x.liftM s) post epost :=
  rfl

end Handler

section Soundness

variable {n : Type uB → Type w} [Monad n] {l : Type uB} [CompleteLattice l]
  [WPMonad n l EPost.Nil] {α : Type uB}

/-- **Soundness of per-operation specs against a handler**, over any core `WPMonad`: specs that
lower-bound the handler's `wp` at every operation give a syntactic `wp` lower-bounding the
semantic `wp` of the interpreted program. -/
theorem wpFold_le_wp_liftM {Φ : OpSpec P l} (s : Handler n P)
    (h : ∀ (a : P.A) (k : P.B a → l), Φ a k ≤ wp (s a) k Lean.Order.bot)
    (x : FreeM P α) (post : α → l) :
    wpFold Φ x post ≤ wp (x.liftM s) post Lean.Order.bot := by
  induction x with
  | pure x =>
    rw [wpFold_pure, FreeM.liftM_pure]
    exact WPMonad.pure_le_wp_pure x post Lean.Order.bot
  | lift_bind a r ih =>
    change Φ a (fun b => wpFold Φ (r b) post) ≤
      wp (((FreeM.lift a).bind r).liftM s) post Lean.Order.bot
    rw [bind_eq_bind, FreeM.liftM_lift_bind]
    calc Φ a (fun b => wpFold Φ (r b) post)
        ≤ wp (s a) (fun b => wpFold Φ (r b) post) Lean.Order.bot := h a _
      _ ≤ wp (s a) (fun b => wp ((r b).liftM s) post Lean.Order.bot) Lean.Order.bot :=
          WP.wp_consequence (s a) _ _ Lean.Order.bot fun b => ih b
      _ ≤ wp (s a >>= fun b => (r b).liftM s) post Lean.Order.bot :=
          WPMonad.bind_le_wp_bind (s a) _ post Lean.Order.bot

end Soundness

end FreeM

end PFunctor
