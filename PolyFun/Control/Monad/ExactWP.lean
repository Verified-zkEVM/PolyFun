/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom.IsMonadHom
public import Std.WP

/-!
# Exact weakest-precondition monads

Core's `WPMonad m Pred EPred` (`Std.WP`) requires
its interpretation to be *sound* for `pure` and `bind`: `post x ⊑ wp (pure x) post epost` and
`wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost`. Soundness is what `vcgen`
needs to decompose a lower bound `pre ⊑ wp prog post epost`, and leaving the reverse inequalities
out is what admits separation-logic and support-style interpretations.

`ExactWPMonad m Pred EPred` is the `Prop`-valued mixin asserting both inequalities as equations.
Equivalently (`ExactWPMonad.isMonadHom`), the interpretation `fun x => WP.wpTrans x` is a monad
morphism into core's predicate-transformer monad `PredTrans Pred EPred`. Exactness is what an
upper bound `wp prog post epost ⊑ c`, an exact value, and a rewriting normal form need.

## Automation contract

The `@[simp]` set drives `wp` inwards through program structure until it meets a leaf, as
`MAlgOrdered.wp`'s set does: `wp_pure` and `wp_bind` (the fields), `wp_map`, `wp_seq`,
`wp_seqLeft`, `wp_seqRight`, and the control-flow equations `wp_ite`, `wp_dite`,
`wp_option_elim`, `wp_sum_elim`. The control-flow equations hold for every `WP` interpretation
and need no exactness. Each rewrite strictly decreases the program argument. No `grind`
annotations: `wp_bind` introduces a fresh higher-order argument on its right-hand side.

## Instances

Core's concrete interpretations of `Id`, `Option`, `Except ε`, and `EStateM ε σ` are exact, and
core's `StateT`, `ReaderT`, `ExceptT`, and `OptionT` lifts preserve exactness. Exact
interpretations are also produced by `MAlgOrdered.toWPMonad`, by the demonic and angelic support
readings over an `ExactMonadAttach`, and by transport along a monad morphism
(`PolyFun/Control/Monad/{Algebra,Support,Hom}/WP.lean`).
-/

@[expose] public section

universe u v w w' z

open Std.WP Lean.Order

/-- A weakest-precondition monad whose interpretation distributes over `pure` and `bind` with
equality: the inequalities `WPMonad.pure_le_wp_pure` and `WPMonad.bind_le_wp_bind` are equations.
-/
class ExactWPMonad (m : Type u → Type v) (Pred : Type w) (EPred : Type w') [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] : Prop where
  /-- The interpretation of `pure a` applies the postcondition to `a`. -/
  wp_pure {α : Type u} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a
  /-- The interpretation of `x >>= f` is the interpretation of `x` against the interpretations of
  the continuations. -/
  wp_bind {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost

attribute [simp] ExactWPMonad.wp_pure ExactWPMonad.wp_bind

namespace ExactWPMonad

section Laws

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred] {α β : Type u}

@[simp]
theorem wp_map (f : α → β) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <$> x) post epost = wp x (fun a => post (f a)) epost := by
  rw [← bind_pure_comp, wp_bind]
  simp only [wp_pure]

@[simp]
theorem wp_seq (f : m (α → β)) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <*> x) post epost = wp f (fun g => wp x (fun a => post (g a)) epost) epost := by
  rw [← bind_map, wp_bind]
  simp only [wp_map]

@[simp]
theorem wp_seqLeft (x : m α) (y : m β) (post : α → Pred) (epost : EPred) :
    wp (x <* y) post epost = wp x (fun a => wp y (fun _ => post a) epost) epost := by
  rw [seqLeft_eq, wp_seq, wp_map]
  rfl

@[simp]
theorem wp_seqRight (x : m α) (y : m β) (post : β → Pred) (epost : EPred) :
    wp (x *> y) post epost = wp x (fun _ => wp y post epost) epost := by
  rw [seqRight_eq, wp_seq, wp_map]
  rfl

/-- Exactness is exactly the statement that the interpretation is a monad morphism into
core's predicate-transformer monad. -/
theorem isMonadHom :
    Cslib.IsMonadHom m (PredTrans Pred EPred) (fun x => WP.wpTrans x) :=
  Cslib.IsMonadHom.mk' (fun a => PredTrans.ext fun post epost => wp_pure a post epost)
    (fun x f => PredTrans.ext fun post epost => wp_bind x f post epost)

end Laws

/-- An interpretation that is a monad morphism into `PredTrans Pred EPred` is exact. -/
theorem ofIsMonadHom {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (h : Cslib.IsMonadHom m (PredTrans Pred EPred) (fun x => WP.wpTrans x)) :
    ExactWPMonad m Pred EPred where
  wp_pure a post epost := congrArg (fun t => PredTrans.apply t post epost) (h.map_pure a)
  wp_bind x f post epost := congrArg (fun t => PredTrans.apply t post epost) (h.map_bind x f)

end ExactWPMonad

/-! ## Control flow

These equations hold for every `WP` interpretation, exact or not. -/

section ControlFlow

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'} [Assertion Pred]
  [Assertion EPred] [WP Prog Value Pred EPred]

@[simp]
theorem ExactWPMonad.wp_ite (c : Prop) [Decidable c] (x y : Prog) (post : Value → Pred)
    (epost : EPred) :
    wp (if c then x else y) post epost = if c then wp x post epost else wp y post epost := by
  split <;> rfl

@[simp]
theorem ExactWPMonad.wp_dite (c : Prop) [Decidable c] (x : c → Prog) (y : ¬c → Prog)
    (post : Value → Pred) (epost : EPred) :
    wp (if h : c then x h else y h) post epost =
      if h : c then wp (x h) post epost else wp (y h) post epost := by
  split <;> rfl

@[simp]
theorem ExactWPMonad.wp_option_elim {γ : Type z} (o : Option γ) (x : Prog) (f : γ → Prog)
    (post : Value → Pred) (epost : EPred) :
    wp (o.elim x f) post epost = o.elim (wp x post epost) (fun c => wp (f c) post epost) := by
  cases o <;> rfl

@[simp]
theorem ExactWPMonad.wp_sum_elim {γ : Type z} {δ : Type z} (s : γ ⊕ δ) (f : γ → Prog)
    (g : δ → Prog) (post : Value → Pred) (epost : EPred) :
    wp (s.elim f g) post epost =
      s.elim (fun c => wp (f c) post epost) (fun d => wp (g d) post epost) := by
  cases s <;> rfl

end ControlFlow

/-! ## Core's concrete interpretations -/

instance ExactWPMonad.instId : ExactWPMonad Id.{u} Prop EStack⟨⟩ where
  wp_pure _ _ _ := rfl
  wp_bind _ _ _ _ := rfl

instance ExactWPMonad.instOption : ExactWPMonad Option.{u} Prop (Unit → Prop) where
  wp_pure _ _ _ := rfl
  wp_bind x _ _ _ := by cases x <;> rfl

instance ExactWPMonad.instExcept {ε : Type u} : ExactWPMonad (Except ε) Prop (ε → Prop) where
  wp_pure _ _ _ := rfl
  wp_bind x _ _ _ := by cases x <;> rfl

instance ExactWPMonad.instEStateM {ε σ : Type} :
    ExactWPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wp_pure _ _ _ := rfl
  wp_bind x f post epost := by
    funext s
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases x s <;> rfl

/-! ## Core's transformer lifts preserve exactness -/

section Transformers

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

instance ExactWPMonad.instStateT {σ : Type u} : ExactWPMonad (StateT σ m) (σ → Pred) EPred where
  wp_pure a post epost := by
    funext s
    simp [StateT.wp_apply_eq, StateT.run_pure]
  wp_bind x f post epost := by
    funext s
    simp [StateT.wp_apply_eq, StateT.run_bind]

instance ExactWPMonad.instReaderT {ρ : Type u} : ExactWPMonad (ReaderT ρ m) (ρ → Pred) EPred where
  wp_pure a post epost := by
    funext r
    simp [ReaderT.wp_apply_eq, ReaderT.run_pure]
  wp_bind x f post epost := by
    funext r
    simp [ReaderT.wp_apply_eq, ReaderT.run_bind]

instance ExactWPMonad.instExceptT {ε : Type u} :
    ExactWPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  wp_pure a post epost := by
    simp [ExceptT.wp_apply_eq, ExceptT.run_pure]
  wp_bind x f post epost := by
    simp only [ExceptT.wp_apply_eq, ExceptT.run_bind, wp_bind]
    congr 1
    funext r
    cases r <;> simp

end Transformers

section OptionTransformer

variable {m : Type u → Type v} {Pred : Type u} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

instance ExactWPMonad.instOptionT :
    ExactWPMonad (OptionT m) Pred ((Unit → Pred) × EPred) where
  wp_pure a post epost := by
    simp [OptionT.wp_apply_eq, OptionT.run_pure]
  wp_bind x f post epost := by
    simp only [OptionT.wp_apply_eq, OptionT.run_bind, Option.elimM, wp_bind]
    congr 1
    funext o
    cases o <;> simp

end OptionTransformer
