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

Both are exact (`ExactWPMonad`) whenever their source is: the syntactic one always, the handler
one when the target's interpretation is exact.

`wpFold_le_wp_liftM` is the soundness of per-operation specs against a handler stated over any
core `WPMonad`; it needs only the inequational `bind` law. `wpFold_eq_wp_liftM` is its exact
counterpart over an exact target. Over the demonic reading of the target's support they say
which outputs the interpreted program can return (`allOutputs_liftM_of_wpFold`).
-/

@[expose] public section

universe uA uB v w z

open Std.WP

namespace PFunctor

variable {P : PFunctor.{uA, uB}}

namespace OpSpec

variable {l : Type v} [CompleteLattice l]

/-- The core interpretation of free programs induced by a monotone per-operation spec. -/
@[instance_reducible]
def toWPMonad (Φ : OpSpec P l) (hΦ : Φ.Mono) : WPMonad (FreeM P) l EStack⟨⟩ :=
  letI := Φ.toMAlgOrdered hΦ
  MAlgOrdered.toWPMonad

/-- Its `wp` is the syntactic fold. -/
theorem toWPMonad_wp (Φ : OpSpec P l) (hΦ : Φ.Mono) {α : Type v} (x : FreeM P α) (post : α → l)
    (epost : EStack⟨⟩) :
    ((Φ.toWPMonad hΦ).toWP α).wp x post epost = FreeM.wpFold Φ x post := by
  change (letI := Φ.toMAlgOrdered hΦ; MAlgOrdered.μ (x >>= fun a => pure (post a))) = _
  exact FreeM.toMAlgOrdered_μ_bind_pure Φ hΦ x post

/-- The syntactic interpretation is exact. -/
instance instExactWPMonadToWPMonad (Φ : OpSpec P l) (hΦ : Φ.Mono) :
    @ExactWPMonad (FreeM P) l EStack⟨⟩ _ _ _ (Φ.toWPMonad hΦ) :=
  letI := Φ.toMAlgOrdered hΦ
  MAlgOrdered.instExactWPMonadToWPMonad

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

/-- Interpretation through a handler into an exact interpretation is exact. -/
instance instExactWPMonadWpMonadOfHandler [WPMonad n Pred EPred] [ExactWPMonad n Pred EPred]
    (s : Handler n P) : @ExactWPMonad (FreeM P) Pred EPred _ _ _ (wpMonadOfHandler s) :=
  MonadHom.instExactWPMonadTransportWPMonad _

end Handler

section Soundness

variable {n : Type uB → Type w} [Monad n] {l : Type uB} [CompleteLattice l]
  [WPMonad n l EStack⟨⟩] {α : Type uB}

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

/-- **Exact per-operation specs give the semantic wp exactly**, over an exact core
interpretation of the target. -/
theorem wpFold_eq_wp_liftM [ExactWPMonad n l EStack⟨⟩] {Φ : OpSpec P l} (s : Handler n P)
    (h : ∀ (a : P.A) (k : P.B a → l), Φ a k = wp (s a) k Lean.Order.bot)
    (x : FreeM P α) (post : α → l) :
    wpFold Φ x post = wp (x.liftM s) post Lean.Order.bot := by
  induction x with
  | pure x => rw [wpFold_pure, FreeM.liftM_pure, ExactWPMonad.wp_pure]
  | lift_bind a r ih =>
    change Φ a (fun b => wpFold Φ (r b) post) =
      wp (((FreeM.lift a).bind r).liftM s) post Lean.Order.bot
    rw [bind_eq_bind, FreeM.liftM_lift_bind, ExactWPMonad.wp_bind, h a]
    exact congrArg (fun k => wp (s a) k Lean.Order.bot) (funext fun b => ih b)

end Soundness

/-! ## Support of the interpreted program

Over the demonic reading of the target's support (`MonadAttach.toWPMonadDemonic`), the
soundness theorem turns a syntactic fold into a guarantee about every output the interpreted
program can return. The carrier is `Prop`, so these live at the ground direction universe. -/

section SemanticSupport

open MonadAttach

variable {Q : PFunctor.{uA, 0}} {n : Type → Type w}
  [Monad n] [LawfulMonad n] [MonadAttach n] [ExactMonadAttach n] {α : Type}

/-- **Specs discharge support facts about the interpreted program.** A per-operation spec
that each handled operation validates for all its outputs turns a syntactic fold into a
guarantee about every output the interpreted program can return. -/
theorem allOutputs_liftM_of_wpFold {Φ : OpSpec Q Prop} (s : Handler n Q)
    (h : ∀ (a : Q.A) (k : Q.B a → Prop), Φ a k → AllOutputs k (s a))
    (x : FreeM Q α) (post : α → Prop) (hx : wpFold Φ x post) :
    AllOutputs post (x.liftM s) := by
  let := toWPMonadDemonic (m := n)
  exact wpFold_le_wp_liftM (n := n) s (fun a k => h a k) x post hx

/-- The demonic fold at the *canonical* spec already implies the interpreted guarantee,
whenever the handler validates that spec: the handler must establish every postcondition
that holds for all typed responses. This constrains its outputs to the operation's response
type; it does not claim that the handler can produce every response. -/
theorem allOutputs_liftM_of_allOutputs (s : Handler n Q)
    (h : ∀ (a : Q.A) (k : Q.B a → Prop), (∀ b, k b) → AllOutputs k (s a))
    (x : FreeM Q α) (post : α → Prop) (hx : AllOutputs post x) :
    AllOutputs post (x.liftM s) :=
  allOutputs_liftM_of_wpFold s h x post ((wpFold_demonic_iff_allOutputs x post).mpr hx)

end SemanticSupport

end FreeM

end PFunctor
