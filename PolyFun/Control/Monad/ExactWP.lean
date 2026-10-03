/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom.IsMonadHom
public import Std.WP
public import ToCslib.Order.LeanOrder

/-!
# Exact weakest-precondition monads

Core's `WPMonad m Pred EPred` (`Std.WP`) requires its interpretation to be *sound* for `pure` and
`bind`: `post x ⊑ wp (pure x) post epost` and
`wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost`. These are the laws of a lax
monad morphism into core's predicate-transformer monad `PredTrans Pred EPred`. Soundness is what
`vcgen` needs to decompose a lower bound `pre ⊑ wp prog post epost`, and leaving the reverse
inequalities out is what admits separation-logic and support-style interpretations.

`ExactWPMonad m Pred EPred` is the `Prop`-valued mixin asserting the reverse, oplax, laws:
`wp (pure a) post epost ⊑ post a` and
`wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost`. They are core's soundness
laws read in the order dual, so an exact interpretation is one that is sound on both `Pred` and
`Predᵒᵈ`:

* `ExactWPMonad.dual` is the same interpretation as a core `WPMonad m Predᵒᵈ EPredᵒᵈ`, whose
  triples are upper bounds `wp prog post epost ⊑ pre`;
* `ExactWPMonad.of_dual` recovers exactness from a sound interpretation over the duals that agrees
  with the original, and `exactWPMonad_iff_dual` states both directions.

The lax and oplax laws together make `wp_pure` and `wp_bind` equations, so the interpretation
`fun x => WP.wpTrans x` is a monad morphism into `PredTrans Pred EPred` (`isMonadHom`,
`ofIsMonadHom`). Three uses need exactness: upper bounds through a `bind`, exact values, and a
rewriting normal form for `simp`.

## Automation contract

The `@[simp]` set drives `wp` inwards through program structure until it meets a leaf. It
consists of `wp_pure`, `wp_bind`, `wp_map`, `wp_seq`, `wp_seqLeft`, and `wp_seqRight`, together
with the control-flow equations `wp_ite`, `wp_dite`, `wp_option_elim`, and `wp_sum_elim`, which
hold for every `WP` interpretation and need no exactness. Each rewrite strictly shrinks the
program argument. The equations carry no `grind` annotations, because `wp_bind` introduces a
fresh higher-order argument on its right-hand side.

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

/-- A weakest-precondition monad whose interpretation also satisfies the reverse, oplax, laws:
core's soundness laws read in the order dual. With `WPMonad.pure_le_wp_pure` and
`WPMonad.bind_le_wp_bind` they make the interpretation distribute over `pure` and `bind` with
equality (`ExactWPMonad.wp_pure`, `ExactWPMonad.wp_bind`). -/
class ExactWPMonad (m : Type u → Type v) (Pred : Type w) (EPred : Type w') [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] : Prop where
  /-- The interpretation of `pure a` is at most the postcondition at `a`. -/
  pure_wp_le {α : Type u} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost ⊑ post a
  /-- The interpretation of `x >>= f` is at most the interpretation of `x` against the
  interpretations of the continuations. -/
  wp_bind_le {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost

namespace ExactWPMonad

/-- An interpretation for which `wp_pure` and `wp_bind` hold as equations is exact. -/
theorem of_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_pure : ∀ {α : Type u} (a : α) (post : α → Pred) (epost : EPred),
      wp (pure a : m α) post epost = post a)
    (wp_bind : ∀ {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred),
      wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost) :
    ExactWPMonad m Pred EPred where
  pure_wp_le a post epost := PartialOrder.rel_of_eq (wp_pure a post epost)
  wp_bind_le x f post epost := PartialOrder.rel_of_eq (wp_bind x f post epost)

section Laws

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred] {α β : Type u}

/-- The interpretation of `pure a` applies the postcondition to `a`. -/
@[simp]
theorem wp_pure (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (pure_wp_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

/-- The interpretation of `x >>= f` is the interpretation of `x` against the interpretations of
the continuations. -/
@[simp]
theorem wp_bind (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (wp_bind_le x f post epost) (WPMonad.bind_le_wp_bind x f post epost)

/-- The interpretation of `f <$> x` is the interpretation of `x` against the postcondition
composed with `f`. -/
@[simp]
theorem wp_map (f : α → β) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <$> x) post epost = wp x (fun a => post (f a)) epost := by
  rw [← bind_pure_comp, wp_bind]
  simp only [wp_pure]

/-- The interpretation of `f <*> x` is the interpretation of `f` against, for each function `g`
that `f` returns, the interpretation of `x` against the postcondition composed with `g`. -/
@[simp]
theorem wp_seq (f : m (α → β)) (x : m α) (post : β → Pred) (epost : EPred) :
    wp (f <*> x) post epost = wp f (fun g => wp x (fun a => post (g a)) epost) epost := by
  rw [← bind_map, wp_bind]
  simp only [wp_map]

/-- The interpretation of `x <* y` is the interpretation of `x` against, for each value `a` that
`x` returns, the interpretation of `y` against the postcondition at `a`. -/
@[simp]
theorem wp_seqLeft (x : m α) (y : m β) (post : α → Pred) (epost : EPred) :
    wp (x <* y) post epost = wp x (fun a => wp y (fun _ => post a) epost) epost := by
  rw [seqLeft_eq, wp_seq, wp_map]
  rfl

/-- The interpretation of `x *> y` is the interpretation of `x` against the interpretation of
`y`, whatever value `x` returns. -/
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
    ExactWPMonad m Pred EPred :=
  of_eq (fun a post epost => congrArg (fun t => PredTrans.apply t post epost) (h.map_pure a))
    (fun x f post epost => congrArg (fun t => PredTrans.apply t post epost) (h.map_bind x f))

/-! ## Exactness as soundness on the dual -/

section Dual

open OrderDual

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred]

/-- The interpretation read in the order duals: the same weakest precondition, with
postconditions and preconditions compared backwards. -/
@[instance_reducible]
def dualWP (α : Type u) : WP (m α) α Predᵒᵈ EPredᵒᵈ where
  wpTrans x := ⟨fun post epost => toDual (wp x (fun a => ofDual (post a)) (ofDual epost))⟩
  wp_trans_monotone x _ _ _ _ hepost hpost := WP.wp_trans_monotone x _ _ _ _ hepost hpost

/-- The dual reading of an exact interpretation: the same interpretation as a core `WPMonad` over
the order duals, which is sound because the original satisfies the oplax laws. Its triples
`⦃ pre ⦄ x ⦃ post ⦄` state the upper bound `wp x post epost ⊑ pre` in the original order. It is
not an instance: core's assertion types are output parameters, so a global dual would compete
with the original interpretation of `m`. -/
@[instance_reducible]
def dual [ExactWPMonad m Pred EPred] : WPMonad m Predᵒᵈ EPredᵒᵈ where
  toLawfulMonad := inferInstance
  toWP := dualWP
  pure_le_wp_pure a post epost := pure_wp_le a (fun a => ofDual (post a)) (ofDual epost)
  bind_le_wp_bind x f post epost := wp_bind_le x f (fun a => ofDual (post a)) (ofDual epost)

/-- The dual reading is exact: its oplax laws are the original interpretation's soundness laws. -/
instance instExactWPMonadDual [ExactWPMonad m Pred EPred] :
    @ExactWPMonad m Predᵒᵈ EPredᵒᵈ _ _ _ (dual (m := m) (Pred := Pred) (EPred := EPred)) :=
  @ExactWPMonad.mk m Predᵒᵈ EPredᵒᵈ _ _ _ dual
    (fun a post epost =>
      WPMonad.pure_le_wp_pure (m := m) a (fun a => ofDual (post a)) (ofDual epost))
    (fun x f post epost =>
      WPMonad.bind_le_wp_bind (m := m) x f (fun a => ofDual (post a)) (ofDual epost))

end Dual

/-! The characterization takes both interpretations explicitly: with one of them in the local
context, instance search for the other would find it first, since core's assertion types are output
parameters. -/

section DualCharacterization

open OrderDual

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred]

/-- Exactness from soundness on the dual: an interpretation over the order duals that agrees with
`inst` and satisfies core's laws there supplies the oplax laws. -/
theorem of_dual (inst : WPMonad m Pred EPred) (d : WPMonad m Predᵒᵈ EPredᵒᵈ)
    (h : ∀ {α : Type u} (x : m α) (post : α → Predᵒᵈ) (epost : EPredᵒᵈ),
      (d.toWP α).wp x post epost =
        toDual ((inst.toWP α).wp x (fun a => ofDual (post a)) (ofDual epost))) :
    @ExactWPMonad m Pred EPred _ _ _ inst :=
  @ExactWPMonad.mk m Pred EPred _ _ _ inst
    (fun a post epost => by
      have hd := d.pure_le_wp_pure a (fun a => toDual (post a)) (toDual epost)
      rw [h] at hd
      exact hd)
    (fun x f post epost => by
      have hd := d.bind_le_wp_bind x f (fun a => toDual (post a)) (toDual epost)
      simp only [h] at hd
      exact hd)

/-- An interpretation is exact exactly when it is also sound, as the same interpretation, on the
order duals. -/
theorem exactWPMonad_iff_dual (inst : WPMonad m Pred EPred) :
    @ExactWPMonad m Pred EPred _ _ _ inst ↔
      ∃ d : WPMonad m Predᵒᵈ EPredᵒᵈ,
        ∀ {α : Type u} (x : m α) (post : α → Predᵒᵈ) (epost : EPredᵒᵈ),
          (d.toWP α).wp x post epost =
            toDual ((inst.toWP α).wp x (fun a => ofDual (post a)) (ofDual epost)) :=
  ⟨fun _ => ⟨dual, fun _ _ _ => rfl⟩, fun ⟨d, h⟩ => of_dual inst d h⟩

end DualCharacterization

end ExactWPMonad

/-! ## Control flow

These equations hold for every `WP` interpretation, exact or not. -/

section ControlFlow

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'} [Assertion Pred]
  [Assertion EPred] [WP Prog Value Pred EPred]

/-- The interpretation of a conditional program is the conditional of the interpretations of its
branches. -/
@[simp]
theorem ExactWPMonad.wp_ite (c : Prop) [Decidable c] (x y : Prog) (post : Value → Pred)
    (epost : EPred) :
    wp (if c then x else y) post epost = if c then wp x post epost else wp y post epost := by
  split <;> rfl

/-- The interpretation of a dependent conditional program is the dependent conditional of the
interpretations of its branches. -/
@[simp]
theorem ExactWPMonad.wp_dite (c : Prop) [Decidable c] (x : c → Prog) (y : ¬c → Prog)
    (post : Value → Pred) (epost : EPred) :
    wp (if h : c then x h else y h) post epost =
      if h : c then wp (x h) post epost else wp (y h) post epost := by
  split <;> rfl

/-- The interpretation of `o.elim x f` eliminates `o` into the interpretation of `x` and the
interpretations of the programs `f c`. -/
@[simp]
theorem ExactWPMonad.wp_option_elim {γ : Type z} (o : Option γ) (x : Prog) (f : γ → Prog)
    (post : Value → Pred) (epost : EPred) :
    wp (o.elim x f) post epost = o.elim (wp x post epost) (fun c => wp (f c) post epost) := by
  cases o <;> rfl

/-- The interpretation of `s.elim f g` eliminates `s` into the interpretations of the programs
`f c` and `g d`. -/
@[simp]
theorem ExactWPMonad.wp_sum_elim {γ : Type z} {δ : Type z} (s : γ ⊕ δ) (f : γ → Prog)
    (g : δ → Prog) (post : Value → Pred) (epost : EPred) :
    wp (s.elim f g) post epost =
      s.elim (fun c => wp (f c) post epost) (fun d => wp (g d) post epost) := by
  cases s <;> rfl

end ControlFlow

/-! ## Core's concrete interpretations -/

instance ExactWPMonad.instId : ExactWPMonad Id.{u} Prop EStack⟨⟩ where
  pure_wp_le _ _ _ := PartialOrder.rel_of_eq <| rfl
  wp_bind_le _ _ _ _ := PartialOrder.rel_of_eq <| rfl

instance ExactWPMonad.instOption : ExactWPMonad Option.{u} Prop (Unit → Prop) where
  pure_wp_le _ _ _ := PartialOrder.rel_of_eq <| rfl
  wp_bind_le x _ _ _ := PartialOrder.rel_of_eq <| by cases x <;> rfl

instance ExactWPMonad.instExcept {ε : Type u} : ExactWPMonad (Except ε) Prop (ε → Prop) where
  pure_wp_le _ _ _ := PartialOrder.rel_of_eq <| rfl
  wp_bind_le x _ _ _ := PartialOrder.rel_of_eq <| by cases x <;> rfl

instance ExactWPMonad.instEStateM {ε σ : Type} :
    ExactWPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  pure_wp_le _ _ _ := PartialOrder.rel_of_eq <| rfl
  wp_bind_le x f post epost := PartialOrder.rel_of_eq <| by
    funext s
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases x s <;> rfl

/-! ## Core's transformer lifts preserve exactness -/

section Transformers

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} [Monad m] [Assertion Pred]
  [Assertion EPred] [WPMonad m Pred EPred] [ExactWPMonad m Pred EPred]

instance ExactWPMonad.instStateT {σ : Type u} : ExactWPMonad (StateT σ m) (σ → Pred) EPred where
  pure_wp_le a post epost := PartialOrder.rel_of_eq <| by
    funext s
    simp [StateT.wp_apply_eq, StateT.run_pure]
  wp_bind_le x f post epost := PartialOrder.rel_of_eq <| by
    funext s
    simp [StateT.wp_apply_eq, StateT.run_bind]

instance ExactWPMonad.instReaderT {ρ : Type u} : ExactWPMonad (ReaderT ρ m) (ρ → Pred) EPred where
  pure_wp_le a post epost := PartialOrder.rel_of_eq <| by
    funext r
    simp [ReaderT.wp_apply_eq, ReaderT.run_pure]
  wp_bind_le x f post epost := PartialOrder.rel_of_eq <| by
    funext r
    simp [ReaderT.wp_apply_eq, ReaderT.run_bind]

instance ExactWPMonad.instExceptT {ε : Type u} :
    ExactWPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  pure_wp_le a post epost := PartialOrder.rel_of_eq <| by
    simp [ExceptT.wp_apply_eq, ExceptT.run_pure]
  wp_bind_le x f post epost := PartialOrder.rel_of_eq <| by
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
  pure_wp_le a post epost := PartialOrder.rel_of_eq <| by
    simp [OptionT.wp_apply_eq, OptionT.run_pure]
  wp_bind_le x f post epost := PartialOrder.rel_of_eq <| by
    simp only [OptionT.wp_apply_eq, OptionT.run_bind, Option.elimM, wp_bind]
    congr 1
    funext o
    cases o <;> simp

end OptionTransformer
