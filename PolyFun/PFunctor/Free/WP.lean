/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Support
public import PolyFun.PFunctor.Handler

/-!
# Weakest Preconditions Over the Free Monad

This file provides the extrinsic verification-condition substrate for `FreeM P`,
in two coupled layers:

* **Syntactic wp.** An `OpSpec P l` assigns each operation `a : P.A` a predicate
  transformer `(P.B a → l) → l` over an ordered carrier `l`, saying what one call
  to `a` guarantees. `FreeM.wpFold Φ` folds these per-operation specs over a free
  tree, leaving the operations uninterpreted. Every monotone spec induces an
  ordered monad algebra `OpSpec.toMAlgOrdered`, so the whole `MAlgOrdered.wp` /
  `Triple` rule set applies; `wp_toMAlgOrdered` identifies the induced `wp` with
  `wpFold`.

* **Semantic wp.** `FreeM.wpVia s` is the weakest precondition of the program
  *interpreted* through a handler `s : Handler m P` into a monad carrying an
  ordered algebra. The soundness theorems `wpFold_le_wpVia` / `wpFold_eq_wpVia`
  say that per-operation specs that (under-)approximate the handler's wp give
  syntactic wps that (under-)approximate the semantic wp — the generic engine
  behind handler-specification reasoning.

The canonical `Prop`-carrier specs `OpSpec.demonic` ("every response") and
`OpSpec.angelic` ("some response") recover the support-based judgments of
`PolyFun.PFunctor.Free.Support`: `wpFold_demonic_iff_allOutputs` and
`wpFold_angelic_iff_someOutput` identify their folds with `AllOutputs` and
`SomeOutput`, so trivial-precondition ("always" / "never") triples and the
syntactic wp theory agree.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor

/-! ## Per-operation specifications -/

/-- A per-operation predicate-transformer specification for the interface `P` over
an ordered carrier `l`: at each position `a`, transform a postcondition on the
directions of `a` into a precondition. -/
def OpSpec (P : PFunctor.{uA, uB}) (l : Type w) : Type max uA uB w :=
  (a : P.A) → (P.B a → l) → l

namespace OpSpec

variable {P : PFunctor.{uA, uB}} {l : Type w}

/-- Monotonicity of a per-operation spec in its continuation. -/
def Mono [Preorder l] (Φ : OpSpec P l) : Prop :=
  ∀ (a : P.A) ⦃k k' : P.B a → l⦄, (∀ b, k b ≤ k' b) → Φ a k ≤ Φ a k'

/-- The demonic ("all responses") spec on the `Prop` carrier: a call to `a`
guarantees only that *every* response satisfies the continuation. -/
def demonic (P : PFunctor.{uA, uB}) : OpSpec P Prop :=
  fun _ k => ∀ b, k b

/-- The angelic ("some response") spec on the `Prop` carrier: a call to `a`
guarantees that *some* response satisfies the continuation. -/
def angelic (P : PFunctor.{uA, uB}) : OpSpec P Prop :=
  fun _ k => ∃ b, k b

theorem demonic_mono : (demonic P).Mono :=
  fun _ _ _ h hk b => h b (hk b)

theorem angelic_mono : (angelic P).Mono :=
  fun _ _ _ h => fun ⟨b, hb⟩ => ⟨b, h b hb⟩

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {l : Type w} {α β : Type v}

/-! ## Syntactic weakest precondition -/

/-- Fold a per-operation spec over a free tree: the syntactic weakest
precondition of `x` for postcondition `post`, with operations uninterpreted. -/
def wpFold (Φ : OpSpec P l) : FreeM P α → (α → l) → l
  | .pure x, post => post x
  | .liftBind a r, post => Φ a fun b => (r b).wpFold Φ post

@[simp, freeM_unfold]
theorem wpFold_pure (Φ : OpSpec P l) (x : α) (post : α → l) :
    wpFold Φ (pure x : FreeM P α) post = post x :=
  rfl

@[freeM_unfold]
theorem wpFold_liftBind (Φ : OpSpec P l) (a : P.A) (r : P.B a → FreeM P α)
    (post : α → l) :
    wpFold Φ (FreeM.liftBind a r) post = Φ a fun b => wpFold Φ (r b) post :=
  rfl

@[simp]
theorem wpFold_lift (Φ : OpSpec P l) (a : P.A) (post : P.B a → l) :
    wpFold Φ (FreeM.lift (P := P) a) post = Φ a post :=
  rfl

theorem wpFold_bind (Φ : OpSpec P l) (x : FreeM P α) (f : α → FreeM P β)
    (post : β → l) :
    wpFold Φ (x >>= f) post = wpFold Φ x fun a => wpFold Φ (f a) post := by
  induction x with
  | pure x => rfl
  | lift_bind a r ih => exact congrArg (Φ a) (funext fun b => ih b)

theorem wpFold_mono [Preorder l] {Φ : OpSpec P l} (hΦ : Φ.Mono) (x : FreeM P α)
    {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wpFold Φ x post ≤ wpFold Φ x post' := by
  induction x with
  | pure x => exact h x
  | lift_bind a r ih => exact hΦ a fun b => ih b

/-! ## The induced ordered monad algebra -/

/-- Every monotone per-operation spec over a complete lattice induces an ordered
monad algebra on `FreeM P`, giving the full `MAlgOrdered.wp`/`Triple` rule set
for free. -/
@[instance_reducible]
def _root_.PFunctor.OpSpec.toMAlgOrdered {l : Type v} [CompleteLattice l]
    (Φ : OpSpec P l) (hΦ : Φ.Mono) : MAlgOrdered (FreeM P) l where
  μ x := wpFold Φ x id
  μ_pure _ := rfl
  μ_bind_mono f g hfg x := by
    rw [wpFold_bind, wpFold_bind]
    exact wpFold_mono hΦ x hfg

/-- The `MAlgOrdered.wp` induced by a per-operation spec is its syntactic fold. -/
theorem wp_toMAlgOrdered {l : Type v} [CompleteLattice l]
    (Φ : OpSpec P l) (hΦ : Φ.Mono) (x : FreeM P α) (post : α → l) :
    letI := Φ.toMAlgOrdered hΦ
    MAlgOrdered.wp x post = wpFold Φ x post := by
  change wpFold Φ (x >>= fun a => pure (post a)) id = _
  rw [wpFold_bind]
  rfl

/-! ## Semantic weakest precondition through a handler -/

section wpVia

variable {m : Type uB → Type w} [Monad m] [LawfulMonad m]
  {l : Type uB} [CompleteLattice l] [MAlgOrdered m l] {α β : Type uB}

/-- The semantic weakest precondition of a free program interpreted through a
handler into a monad carrying an ordered algebra. -/
def wpVia (s : Handler m P) (x : FreeM P α) (post : α → l) : l :=
  MAlgOrdered.wp (x.liftM s) post

@[simp]
theorem wpVia_pure (s : Handler m P) (x : α) (post : α → l) :
    wpVia s (pure x : FreeM P α) post = post x := by
  rw [wpVia, FreeM.liftM_pure, MAlgOrdered.wp_pure]

theorem wpVia_bind (s : Handler m P) (x : FreeM P α) (f : α → FreeM P β)
    (post : β → l) :
    wpVia s (x >>= f) post = wpVia s x fun a => wpVia s (f a) post := by
  rw [wpVia, FreeM.liftM_bind, MAlgOrdered.wp_bind]
  rfl

theorem wpVia_liftBind (s : Handler m P) (a : P.A) (r : P.B a → FreeM P α)
    (post : α → l) :
    wpVia s (FreeM.liftBind a r) post =
      MAlgOrdered.wp (s a) fun b => wpVia s (r b) post := by
  rw [wpVia, show (FreeM.liftBind a r : FreeM P α) = FreeM.lift a >>= r from rfl,
    FreeM.liftM_bind, FreeM.liftM_lift, MAlgOrdered.wp_bind]
  rfl

/-- **Soundness of per-operation specs against a handler**: specs that lower-bound
the handler's wp at every operation give a syntactic wp lower-bounding the
semantic wp of the interpreted program. -/
theorem wpFold_le_wpVia {Φ : OpSpec P l} (s : Handler m P)
    (h : ∀ (a : P.A) (k : P.B a → l), Φ a k ≤ MAlgOrdered.wp (s a) k)
    (x : FreeM P α) (post : α → l) :
    wpFold Φ x post ≤ wpVia s x post := by
  induction x with
  | pure x => rw [wpFold_pure, wpVia_pure]
  | lift_bind a r ih =>
      calc Φ a (fun b => wpFold Φ (r b) post)
          ≤ MAlgOrdered.wp (s a) fun b => wpFold Φ (r b) post := h a _
        _ ≤ MAlgOrdered.wp (s a) fun b => wpVia s (r b) post :=
            MAlgOrdered.wp_mono _ fun b => ih b
        _ = wpVia s (FreeM.liftBind a r) post := (wpVia_liftBind s a r post).symm

/-- Exact per-operation specs give the semantic wp exactly. -/
theorem wpFold_eq_wpVia {Φ : OpSpec P l} (s : Handler m P)
    (h : ∀ (a : P.A) (k : P.B a → l), Φ a k = MAlgOrdered.wp (s a) k)
    (x : FreeM P α) (post : α → l) :
    wpFold Φ x post = wpVia s x post := by
  induction x with
  | pure x => rw [wpFold_pure, wpVia_pure]
  | lift_bind a r ih =>
      rw [show ((FreeM.lift a).bind r : FreeM P α) = FreeM.liftBind a r from rfl,
        wpFold_liftBind, wpVia_liftBind, h a]
      exact congrArg _ (funext fun b => ih b)

end wpVia

/-! ## Coherence with the canonical support -/

section Support

variable {α : Type uB}

/-- The demonic fold is the "always" judgment over the canonical support. -/
theorem wpFold_demonic_iff_allOutputs (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.demonic P) x post ↔ AllOutputs post x := by
  induction x with
  | pure x => simp
  | lift_bind a r ih =>
      rw [show ((FreeM.lift a).bind r : FreeM P α) = FreeM.liftBind a r from rfl,
        wpFold_liftBind, allOutputs_liftBind]
      exact forall_congr' fun b => ih b

/-- The angelic fold is the "some output" judgment over the canonical support. -/
theorem wpFold_angelic_iff_someOutput (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.angelic P) x post ↔ SomeOutput post x := by
  induction x with
  | pure x => simp
  | lift_bind a r ih =>
      rw [show ((FreeM.lift a).bind r : FreeM P α) = FreeM.liftBind a r from rfl,
        wpFold_liftBind, someOutput_liftBind]
      exact exists_congr fun b => ih b

/-- The demonic fold of a negated postcondition is the "never" judgment. -/
theorem wpFold_demonic_not_iff_noOutput (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.demonic P) x (fun a => ¬ post a) ↔ NoOutput post x :=
  wpFold_demonic_iff_allOutputs x fun a => ¬ post a

end Support

end FreeM

end PFunctor
