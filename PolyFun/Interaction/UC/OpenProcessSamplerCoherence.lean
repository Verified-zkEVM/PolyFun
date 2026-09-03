/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.Basic.Sampler
import all PolyFun.Interaction.UC.OpenProcess
import all PolyFun.Interaction.UC.OpenProcessSamplerEquiv
public import PolyFun.Interaction.Basic.Sampler
public import PolyFun.Interaction.UC.OpenProcessCoherence
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Coherence of interleaving up to sampler equivalence

`OpenProcessCoherence` proves the coherence shapes of `OpenProcess.interleave`
up to activation equivalence, which erases sampler effects. This module proves
the same shapes up to `OpenProcessSamplerEquiv R`, the strong one-step matching
that retains sampled paths relative to a relation family `R`.

A regrouping of nested interleavings only moves scheduler nodes, so the two
sides decorate every leaf identically once the injections are composed. That
is the hypothesis form used here: the composite injections of a leaf on the two
sides are *equal*, and every scheduler node is an internal node
(`OpenNodeContext.IsInternalNode`: silent and emitting nothing). What a
regrouping does change is the encoding of the scheduler draw, and the single
remaining hypothesis of each shape is that the two nested draws are `R`-related:

* `interleave_factorLeft_samplerEquiv`: `(p₁ ∥ p₂) ∥ p₃ ≈ p₁ ∥ (p₃ ∥ p₂)`,
  the left plug factorization, given
  `R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorLeft τOut τIn)`;
* `interleave_factorRight_samplerEquiv`: `(p₁ ∥ p₂) ∥ p₃ ≈ p₂ ∥ (p₃ ∥ p₁)`,
  the right plug factorization;
* `interleave_comm_samplerEquiv`: `p₁ ∥ p₂ ≈ p₂ ∥ p₁`, given
  `R.rel (schedulerFlip <$> σ) τ`;
* `interleave_rehome_samplerEquiv`: the same interleaving under another
  internal scheduler node, given `R.rel σ τ`;
* `interleave_assoc_samplerEquiv`: `(p₁ ∥ p₂) ∥ p₃ ≈ p₁ ∥ (p₂ ∥ p₃)`, derived
  from the left factorization and commutation of the inner pair.

The draws take two scheduler samplers per nesting so that both the shared
sampler of `openTheory` and the mass-dependent samplers of
`scheduledOpenTheory` are instances. Unit absorption has no sampler-level
version: a silent unit adds a path to every step, so no path bijection exists.

Sampler equivalence is also a congruence for `interleave` and `mapHom`
(`OpenProcess.interleave_congr_{left,right}_samplerEquiv`,
`OpenProcess.mapHom_congr_samplerEquiv`), which needs the relation family to be
a congruence for the continuation of `bind` as well
(`MonadRelFamily.IsBindCongr`) and the injections to act on boundary traces by
relabelling (`OpenNodeContext.EmitsAlong`).
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent
open PFunctor.FreeM.Displayed (Decoration)

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the proofs below rewrite through the interleaved dynamical model there.
`implicit_reducible` (unlike `reducible`) stays invisible to simp validation and
instance search. -/
attribute [local implicit_reducible] PFunctor.DynSystem.expose PFunctor.DynSystem.update
  PFunctor.DynSystem.mk' Concurrent.ProcessOver.interleave OpenProcess.mapHom
  OpenProcess.interleave

/-! ## Right-continuation congruence -/

/-- A relation family is **bind-congruent on the right** when binding a common
computation against pointwise related continuations gives related results.
Together with `MonadRelFamily.bind_congr` this makes the family a congruence
for `bind`. Equality and the everything-relation satisfy it, as does equality
of output distributions. -/
class MonadRelFamily.IsBindCongr {m : Type w → Type w'} [Monad m]
    (R : MonadRelFamily m) : Prop where
  /-- Binding against pointwise related continuations preserves the relation. -/
  bind_congr_right : ∀ {α β : Type w} (x : m α) {f g : α → m β},
    (∀ a, R.rel (f a) (g a)) → R.rel (x >>= f) (x >>= g)

theorem MonadRelFamily.bind_congr_right {m : Type w → Type w'} [Monad m]
    (R : MonadRelFamily m) [R.IsBindCongr] {α β : Type w} (x : m α) {f g : α → m β}
    (h : ∀ a, R.rel (f a) (g a)) : R.rel (x >>= f) (x >>= g) :=
  IsBindCongr.bind_congr_right x h

instance MonadRelFamily.eq_isBindCongr {m : Type w → Type w'} [Monad m] :
    (MonadRelFamily.eq m).IsBindCongr where
  bind_congr_right := by
    intro α β x f g h
    exact (MonadRelFamily.eq_rel _ _).mpr
      (congrArg (x >>= ·) (funext fun a => (MonadRelFamily.eq_rel _ _).mp (h a)))

instance MonadRelFamily.top_isBindCongr {m : Type w → Type w'} [Monad m] :
    (MonadRelFamily.top m).IsBindCongr where
  bind_congr_right := by
    intro α β x f g _
    exact MonadRelFamily.top_rel _ _

/-! ## Leaves and nested scheduler draws -/

namespace OpenProcessFactorization

/-- The leaf selected by a ternary regrouping of interleavings. `context` names
the third leaf; in the plug factorizations it is the closing context. -/
inductive Leaf where
  | first
  | second
  | context
  deriving DecidableEq, Repr

end OpenProcessFactorization

open OpenProcessFactorization (Leaf)

/-- The leaf reached by the source nesting `(first ∥ second) ∥ context`: the
outer coin selects the pair, the inner coin its component. -/
@[expose]
def nestedDrawLeft {m : Type w → Type w'} [Monad m] (σOut σIn : m (ULift.{w, 0} Bool)) :
    m (ULift.{w, 0} Leaf) :=
  σOut >>= fun
    | ⟨true⟩ => σIn >>= fun
      | ⟨true⟩ => pure ⟨.first⟩
      | ⟨false⟩ => pure ⟨.second⟩
    | ⟨false⟩ => pure ⟨.context⟩

/-- The leaf reached by the left-factored nesting `first ∥ (context ∥ second)`. -/
@[expose]
def nestedDrawFactorLeft {m : Type w → Type w'} [Monad m] (τOut τIn : m (ULift.{w, 0} Bool)) :
    m (ULift.{w, 0} Leaf) :=
  τOut >>= fun
    | ⟨true⟩ => pure ⟨.first⟩
    | ⟨false⟩ => τIn >>= fun
      | ⟨true⟩ => pure ⟨.context⟩
      | ⟨false⟩ => pure ⟨.second⟩

/-- The leaf reached by the right-factored nesting `second ∥ (context ∥ first)`. -/
@[expose]
def nestedDrawFactorRight {m : Type w → Type w'} [Monad m] (τOut τIn : m (ULift.{w, 0} Bool)) :
    m (ULift.{w, 0} Leaf) :=
  τOut >>= fun
    | ⟨true⟩ => pure ⟨.second⟩
    | ⟨false⟩ => τIn >>= fun
      | ⟨true⟩ => pure ⟨.context⟩
      | ⟨false⟩ => pure ⟨.first⟩

/-- Binding the source nesting's draw against a per-leaf continuation is the
flattened two-coin computation. -/
theorem nestedDrawLeft_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (σOut σIn : m (ULift.{w, 0} Bool)) {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    nestedDrawLeft σOut σIn >>= h =
      σOut >>= fun
        | ⟨true⟩ => σIn >>= fun
          | ⟨true⟩ => h ⟨.first⟩
          | ⟨false⟩ => h ⟨.second⟩
        | ⟨false⟩ => h ⟨.context⟩ := by
  simp only [nestedDrawLeft, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [pure_bind]
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]

/-- Binding the left-factored draw against a per-leaf continuation is the
flattened two-coin computation. -/
theorem nestedDrawFactorLeft_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (τOut τIn : m (ULift.{w, 0} Bool)) {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    nestedDrawFactorLeft τOut τIn >>= h =
      τOut >>= fun
        | ⟨true⟩ => h ⟨.first⟩
        | ⟨false⟩ => τIn >>= fun
          | ⟨true⟩ => h ⟨.context⟩
          | ⟨false⟩ => h ⟨.second⟩ := by
  simp only [nestedDrawFactorLeft, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]
  · simp only [pure_bind]

/-- Binding the right-factored draw against a per-leaf continuation is the
flattened two-coin computation. -/
theorem nestedDrawFactorRight_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (τOut τIn : m (ULift.{w, 0} Bool)) {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    nestedDrawFactorRight τOut τIn >>= h =
      τOut >>= fun
        | ⟨true⟩ => h ⟨.second⟩
        | ⟨false⟩ => τIn >>= fun
          | ⟨true⟩ => h ⟨.context⟩
          | ⟨false⟩ => h ⟨.first⟩ := by
  simp only [nestedDrawFactorRight, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]
  · simp only [pure_bind]

/-! ## Scheduler re-encodings -/

/-- Negate a lifted scheduler coin: the path re-encoding of commutation. -/
@[expose]
def schedulerFlip : ULift.{w, 0} Bool → ULift.{w, 0} Bool :=
  fun b => ULift.up !b.down

@[simp] theorem schedulerFlip_up_true :
    schedulerFlip.{w} (ULift.up true) = ULift.up false := rfl

@[simp] theorem schedulerFlip_up_false :
    schedulerFlip.{w} (ULift.up false) = ULift.up true := rfl

/-- Flip the scheduler coin at the root of a binary-choice interleaving tree,
exchanging the two branches. -/
@[expose]
def flipInterleavePathEquiv (t₁ t₂ : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₂
      | ⟨false⟩ => t₁) where
  toFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨true⟩, tr⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨true⟩, tr⟩
  left_inv := by rintro ⟨⟨b⟩, tr⟩; cases b <;> rfl
  right_inv := by rintro ⟨⟨b⟩, tr⟩; cases b <;> rfl

theorem flipInterleavePathEquiv_apply_true (t₁ t₂ : TypeTree.{w})
    (tr : TypeTree.Path t₁) :
    flipInterleavePathEquiv t₁ t₂ ⟨⟨true⟩, tr⟩ = ⟨⟨false⟩, tr⟩ := rfl

theorem flipInterleavePathEquiv_apply_false (t₁ t₂ : TypeTree.{w})
    (tr : TypeTree.Path t₂) :
    flipInterleavePathEquiv t₁ t₂ ⟨⟨false⟩, tr⟩ = ⟨⟨true⟩, tr⟩ := rfl

/-- Regroup the nested scheduler coins of `(t₁ ∥ t₂) ∥ tk` onto the
left-factored shape `t₁ ∥ (tk ∥ t₂)`: the first leaf keeps a single `true`
coin, the second moves under two `false` coins, and the third under
`false, true`. -/
@[expose]
def parLeftPathEquiv (t₁ t₂ tk : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => t₁
        | ⟨false⟩ => t₂
      | ⟨false⟩ => tk) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => tk
        | ⟨false⟩ => t₂) where
  toFun := fun
    | ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩
    | ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
    · rfl

theorem parLeftPathEquiv_apply_first (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path t₁) :
    parLeftPathEquiv t₁ t₂ tk ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ = ⟨⟨true⟩, tr⟩ := rfl

theorem parLeftPathEquiv_apply_second (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path t₂) :
    parLeftPathEquiv t₁ t₂ tk ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ = ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ := rfl

theorem parLeftPathEquiv_apply_context (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path tk) :
    parLeftPathEquiv t₁ t₂ tk ⟨⟨false⟩, tr⟩ = ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ := rfl

/-- Regroup the nested scheduler coins of `(t₁ ∥ t₂) ∥ tk` onto the
right-factored shape `t₂ ∥ (tk ∥ t₁)`: the second leaf keeps a single `true`
coin, the first moves under two `false` coins, and the third under
`false, true`. -/
@[expose]
def parRightPathEquiv (t₁ t₂ tk : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => t₁
        | ⟨false⟩ => t₂
      | ⟨false⟩ => tk) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₂
      | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => tk
        | ⟨false⟩ => t₁) where
  toFun := fun
    | ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
    · rfl

theorem parRightPathEquiv_apply_first (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path t₁) :
    parRightPathEquiv t₁ t₂ tk ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ = ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ := rfl

theorem parRightPathEquiv_apply_second (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path t₂) :
    parRightPathEquiv t₁ t₂ tk ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ = ⟨⟨true⟩, tr⟩ := rfl

theorem parRightPathEquiv_apply_context (t₁ t₂ tk : TypeTree.{w})
    (tr : TypeTree.Path tk) :
    parRightPathEquiv t₁ t₂ tk ⟨⟨false⟩, tr⟩ = ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ := rfl

/-- Re-encode the left branch of a binary-choice interleaving tree along a
path equivalence of the left subtree. -/
@[expose]
def leftBranchPathEquiv {t₁ t₁' : TypeTree.{w}} (e : TypeTree.Path t₁ ≃ TypeTree.Path t₁')
    (t₂ : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁'
      | ⟨false⟩ => t₂) where
  toFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, e tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, tr⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, e.symm tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, tr⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · change (⟨⟨true⟩, e.symm (e tr)⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => t₁
          | ⟨false⟩ => t₂)) = ⟨⟨true⟩, tr⟩
      rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · change (⟨⟨true⟩, e (e.symm tr)⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => t₁'
          | ⟨false⟩ => t₂)) = ⟨⟨true⟩, tr⟩
      rw [Equiv.apply_symm_apply]

theorem leftBranchPathEquiv_apply_true {t₁ t₁' : TypeTree.{w}}
    (e : TypeTree.Path t₁ ≃ TypeTree.Path t₁') (t₂ : TypeTree.{w}) (tr : TypeTree.Path t₁) :
    leftBranchPathEquiv e t₂ ⟨⟨true⟩, tr⟩ = ⟨⟨true⟩, e tr⟩ := rfl

theorem leftBranchPathEquiv_apply_false {t₁ t₁' : TypeTree.{w}}
    (e : TypeTree.Path t₁ ≃ TypeTree.Path t₁') (t₂ : TypeTree.{w}) (tr : TypeTree.Path t₂) :
    leftBranchPathEquiv e t₂ ⟨⟨false⟩, tr⟩ = ⟨⟨false⟩, tr⟩ := rfl

/-- Re-encode the right branch of a binary-choice interleaving tree along a
path equivalence of the right subtree. -/
@[expose]
def rightBranchPathEquiv (t₁ : TypeTree.{w}) {t₂ t₂' : TypeTree.{w}}
    (e : TypeTree.Path t₂ ≃ TypeTree.Path t₂') :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂') where
  toFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, e tr⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, e.symm tr⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · change (⟨⟨false⟩, e.symm (e tr)⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => t₁
          | ⟨false⟩ => t₂)) = ⟨⟨false⟩, tr⟩
      rw [Equiv.symm_apply_apply]
    · rfl
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · change (⟨⟨false⟩, e (e.symm tr)⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => t₁
          | ⟨false⟩ => t₂')) = ⟨⟨false⟩, tr⟩
      rw [Equiv.apply_symm_apply]
    · rfl

theorem rightBranchPathEquiv_apply_true (t₁ : TypeTree.{w}) {t₂ t₂' : TypeTree.{w}}
    (e : TypeTree.Path t₂ ≃ TypeTree.Path t₂') (tr : TypeTree.Path t₁) :
    rightBranchPathEquiv t₁ e ⟨⟨true⟩, tr⟩ = ⟨⟨true⟩, tr⟩ := rfl

theorem rightBranchPathEquiv_apply_false (t₁ : TypeTree.{w}) {t₂ t₂' : TypeTree.{w}}
    (e : TypeTree.Path t₂ ≃ TypeTree.Path t₂') (tr : TypeTree.Path t₂) :
    rightBranchPathEquiv t₁ e ⟨⟨false⟩, tr⟩ = ⟨⟨false⟩, e tr⟩ := rfl

/-! ## Sampled paths of nested interleavings -/

section SampledPaths

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m]

/-- Flipping the scheduler coin of an interleaved sample is sampling the
branch-swapped interleave under the flipped scheduler draw. -/
theorem samplePath_interleave_flip {spec₁ spec₂ : TypeTree.{w}}
    (σ : m (ULift.{w, 0} Bool))
    (samp₁ : TypeTree.Sampler m spec₁) (samp₂ : TypeTree.Sampler m spec₂) :
    (fun tr => flipInterleavePathEquiv spec₁ spec₂ tr) <$>
        TypeTree.samplePath _ (TypeTree.Sampler.interleave σ samp₁ samp₂) =
      TypeTree.samplePath _
        (TypeTree.Sampler.interleave (schedulerFlip <$> σ) samp₂ samp₁) := by
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind,
    bind_map_left]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb <;> simp only [map_pure] <;> rfl

omit [LawfulMonad m] in
/-- Interleaved samples with the same branch samplers and `R`-related
scheduler draws are `R`-related. -/
theorem samplePath_interleave_congr_scheduler (R : MonadRelFamily m)
    {spec₁ spec₂ : TypeTree.{w}} {σ σ' : m (ULift.{w, 0} Bool)}
    (h : R.rel σ' σ)
    (samp₁ : TypeTree.Sampler m spec₁) (samp₂ : TypeTree.Sampler m spec₂) :
    R.rel
      (TypeTree.samplePath _ (TypeTree.Sampler.interleave σ' samp₁ samp₂))
      (TypeTree.samplePath _ (TypeTree.Sampler.interleave σ samp₁ samp₂)) := by
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
  exact R.bind_congr _ h

variable {t₁ t₂ tk : TypeTree.{w}}
  (samp₁ : TypeTree.Sampler m t₁) (samp₂ : TypeTree.Sampler m t₂) (sampk : TypeTree.Sampler m tk)

/-- The source nesting `(t₁ ∥ t₂) ∥ tk` of three step trees. -/
abbrev nestedLeftTree (t₁ t₂ tk : TypeTree.{w}) : TypeTree.{w} :=
  TypeTree.node (ULift.{w, 0} Bool) fun
    | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂
    | ⟨false⟩ => tk

/-- The left-factored nesting `t₁ ∥ (tk ∥ t₂)` of three step trees. -/
abbrev factorLeftTree (t₁ t₂ tk : TypeTree.{w}) : TypeTree.{w} :=
  TypeTree.node (ULift.{w, 0} Bool) fun
    | ⟨true⟩ => t₁
    | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => tk
      | ⟨false⟩ => t₂

/-- The right-factored nesting `t₂ ∥ (tk ∥ t₁)` of three step trees. -/
abbrev factorRightTree (t₁ t₂ tk : TypeTree.{w}) : TypeTree.{w} :=
  TypeTree.node (ULift.{w, 0} Bool) fun
    | ⟨true⟩ => t₂
    | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => tk
      | ⟨false⟩ => t₁

/-- Inject a leaf's sampled path into the left-factored nesting
`t₁ ∥ (tk ∥ t₂)`. -/
def factorLeftContinuation : ULift.{w, 0} Leaf → m (TypeTree.Path (factorLeftTree t₁ t₂ tk))
  | ⟨.first⟩ => TypeTree.samplePath _ samp₁ >>= fun tr =>
      pure (⟨⟨true⟩, tr⟩ : TypeTree.Path (factorLeftTree t₁ t₂ tk))
  | ⟨.second⟩ => TypeTree.samplePath _ samp₂ >>= fun tr =>
      pure (⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ : TypeTree.Path (factorLeftTree t₁ t₂ tk))
  | ⟨.context⟩ => TypeTree.samplePath _ sampk >>= fun tr =>
      pure (⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ : TypeTree.Path (factorLeftTree t₁ t₂ tk))

/-- Inject a leaf's sampled path into the right-factored nesting
`t₂ ∥ (tk ∥ t₁)`. -/
def factorRightContinuation :
    ULift.{w, 0} Leaf → m (TypeTree.Path (factorRightTree t₁ t₂ tk))
  | ⟨.first⟩ => TypeTree.samplePath _ samp₁ >>= fun tr =>
      pure (⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ : TypeTree.Path (factorRightTree t₁ t₂ tk))
  | ⟨.second⟩ => TypeTree.samplePath _ samp₂ >>= fun tr =>
      pure (⟨⟨true⟩, tr⟩ : TypeTree.Path (factorRightTree t₁ t₂ tk))
  | ⟨.context⟩ => TypeTree.samplePath _ sampk >>= fun tr =>
      pure (⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ : TypeTree.Path (factorRightTree t₁ t₂ tk))

/-- The source nesting's sample, re-encoded onto the left-factored shape, is
the source draw bound against the leaf samplers. -/
theorem samplePath_nestedLeft_factorLeft (σOut σIn : m (ULift.{w, 0} Bool)) :
    (fun tr => parLeftPathEquiv t₁ t₂ tk tr) <$>
        TypeTree.samplePath (nestedLeftTree t₁ t₂ tk)
          (TypeTree.Sampler.interleave σOut
            (TypeTree.Sampler.interleave σIn samp₁ samp₂) sampk) =
      nestedDrawLeft σOut σIn >>= factorLeftContinuation samp₁ samp₂ sampk := by
  rw [nestedDrawLeft_bind]
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [map_pure]
    rfl
  · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> rfl

/-- The left-factored nesting's sample is the left-factored draw bound against
the leaf samplers. -/
theorem samplePath_factorLeft (τOut τIn : m (ULift.{w, 0} Bool)) :
    TypeTree.samplePath (factorLeftTree t₁ t₂ tk)
        (TypeTree.Sampler.interleave τOut samp₁
          (TypeTree.Sampler.interleave τIn sampk samp₂)) =
      nestedDrawFactorLeft τOut τIn >>= factorLeftContinuation samp₁ samp₂ sampk := by
  rw [nestedDrawFactorLeft_bind]
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> rfl
  · rfl

/-- The source nesting's sample, re-encoded onto the right-factored shape, is
the source draw bound against the leaf samplers. -/
theorem samplePath_nestedLeft_factorRight (σOut σIn : m (ULift.{w, 0} Bool)) :
    (fun tr => parRightPathEquiv t₁ t₂ tk tr) <$>
        TypeTree.samplePath (nestedLeftTree t₁ t₂ tk)
          (TypeTree.Sampler.interleave σOut
            (TypeTree.Sampler.interleave σIn samp₁ samp₂) sampk) =
      nestedDrawLeft σOut σIn >>= factorRightContinuation samp₁ samp₂ sampk := by
  rw [nestedDrawLeft_bind]
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [map_pure]
    rfl
  · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> rfl

/-- The right-factored nesting's sample is the right-factored draw bound
against the leaf samplers. -/
theorem samplePath_factorRight (τOut τIn : m (ULift.{w, 0} Bool)) :
    TypeTree.samplePath (factorRightTree t₁ t₂ tk)
        (TypeTree.Sampler.interleave τOut samp₂
          (TypeTree.Sampler.interleave τIn sampk samp₁)) =
      nestedDrawFactorRight τOut τIn >>= factorRightContinuation samp₁ samp₂ sampk := by
  rw [nestedDrawFactorRight_bind]
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> rfl
  · rfl

/-- Source and left-factored nested samples are related whenever their draws
are. -/
theorem samplePath_factorLeft_rel (R : MonadRelFamily m)
    {σOut σIn τOut τIn : m (ULift.{w, 0} Bool)}
    (hσ : R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorLeft τOut τIn)) :
    R.rel
      ((fun tr => parLeftPathEquiv t₁ t₂ tk tr) <$>
        TypeTree.samplePath (nestedLeftTree t₁ t₂ tk)
          (TypeTree.Sampler.interleave σOut
            (TypeTree.Sampler.interleave σIn samp₁ samp₂) sampk))
      (TypeTree.samplePath (factorLeftTree t₁ t₂ tk)
        (TypeTree.Sampler.interleave τOut samp₁
          (TypeTree.Sampler.interleave τIn sampk samp₂))) := by
  rw [samplePath_nestedLeft_factorLeft, samplePath_factorLeft]
  exact R.bind_congr _ hσ

/-- Source and right-factored nested samples are related whenever their draws
are. -/
theorem samplePath_factorRight_rel (R : MonadRelFamily m)
    {σOut σIn τOut τIn : m (ULift.{w, 0} Bool)}
    (hσ : R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorRight τOut τIn)) :
    R.rel
      ((fun tr => parRightPathEquiv t₁ t₂ tk tr) <$>
        TypeTree.samplePath (nestedLeftTree t₁ t₂ tk)
          (TypeTree.Sampler.interleave σOut
            (TypeTree.Sampler.interleave σIn samp₁ samp₂) sampk))
      (TypeTree.samplePath (factorRightTree t₁ t₂ tk)
        (TypeTree.Sampler.interleave τOut samp₂
          (TypeTree.Sampler.interleave τIn sampk samp₁))) := by
  rw [samplePath_nestedLeft_factorRight, samplePath_factorRight]
  exact R.bind_congr _ hσ

end SampledPaths

/-! ## The coherence shapes up to sampler equivalence -/

section Shapes

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m] {Party : Type u}
  {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₃₂ Δ : PortBoundary}
  (R : MonadRelFamily m)
  (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
  (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  (p₃ : OpenProcess.{u, v, w, w'} m Party Δ₃)

open OpenProcess OpenNodeContext

/-- **Left factorization.** `(p₁ ∥ p₂) ∥ p₃` is sampler equivalent to
`p₁ ∥ (p₃ ∥ p₂)` when both sides decorate each leaf identically, every
scheduler node is internal, and the source and left-factored scheduler draws
are related. -/
theorem interleave_factorLeft_samplerEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {cIn : OpenNodeContext.{u, w} Party Δ₁₂ (ULift.{w, 0} Bool)}
    {cOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (σIn σOut : m (ULift.{w, 0} Bool))
    {f₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ₃₂)}
    {f₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₃₂)}
    {g₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {dIn : OpenNodeContext.{u, w} Party Δ₃₂ (ULift.{w, 0} Bool)}
    {dOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (τIn τOut : m (ULift.{w, 0} Bool))
    (h₁ : TypeTree.Node.ContextHom.comp g₁ f₁ = g₁')
    (h₂ : TypeTree.Node.ContextHom.comp g₁ f₂ = TypeTree.Node.ContextHom.comp g₂' f₂')
    (h₃ : g₂ = TypeTree.Node.ContextHom.comp g₂' f₁')
    (hcOut : IsInternalNode cOut) (hcIn : IsInternalNode (g₁ _ cIn))
    (hdOut : IsInternalNode dOut) (hdIn : IsInternalNode (g₂' _ dIn))
    (hσ : R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorLeft τOut τIn)) :
    OpenProcessSamplerEquiv R
      ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
      (p₁.interleave (p₃.interleave p₂ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut) := by
  refine ⟨fun (⟨⟨s₁, s₂⟩, s₃⟩ : (p₁.Proc × p₂.Proc) × p₃.Proc)
      (⟨s₁', s₃', s₂'⟩ : p₁.Proc × p₃.Proc × p₂.Proc) => s₁ = s₁' ∧ s₂ = s₂' ∧ s₃ = s₃',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, s₃⟩ => ⟨⟨s₁, s₃, s₂⟩, rfl, rfl, rfl⟩,
    fun ⟨s₁, s₃, s₂⟩ => ⟨⟨⟨s₁, s₂⟩, s₃⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₁', s₃', s₂'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parLeftPathEquiv (p₁.step s₁).tree (p₂.step s₂).tree (p₃.step s₃).tree,
    ?_, ?_, ?_, ?_⟩
  · -- silence: the regrouping only moves internal nodes
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · rw [parLeftPathEquiv_apply_context, isSilentStep_interleave_right_iff_decoration,
        isSilentStep_interleave_right_iff_decoration, isSilentDecoration_map_interleave_left,
        hcOut.isActivated, hdOut.isActivated, hdIn.isActivated,
        OpenNodeContext.decoration_map_map, ← h₃]
      simp
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · rw [parLeftPathEquiv_apply_second, isSilentStep_interleave_left_iff_decoration,
          isSilentDecoration_map_interleave_right, isSilentStep_interleave_right_iff_decoration,
          isSilentDecoration_map_interleave_right, hcOut.isActivated, hcIn.isActivated,
          hdOut.isActivated, hdIn.isActivated, OpenNodeContext.decoration_map_map,
          OpenNodeContext.decoration_map_map, h₂]
      · rw [parLeftPathEquiv_apply_first, isSilentStep_interleave_left_iff_decoration,
          isSilentDecoration_map_interleave_left, isSilentStep_interleave_left_iff_decoration,
          hcOut.isActivated, hcIn.isActivated, hdOut.isActivated,
          OpenNodeContext.decoration_map_map, h₁]
        simp
  · -- boundary traces: internal nodes emit nothing
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · rw [parLeftPathEquiv_apply_context, boundaryTrace_interleave_right,
        boundaryTrace_interleave_right, boundaryTrace_map_interleave_left, hcOut.emit, hdOut.emit,
        hdIn.emit, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map, ← h₃]
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · rw [parLeftPathEquiv_apply_second, boundaryTrace_interleave_left,
          boundaryTrace_map_interleave_right, boundaryTrace_interleave_right,
          boundaryTrace_map_interleave_right, hcOut.emit, hcIn.emit, hdOut.emit, hdIn.emit,
          one_mul, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map,
          OpenNodeContext.decoration_map_map, h₂]
      · rw [parLeftPathEquiv_apply_first, boundaryTrace_interleave_left,
          boundaryTrace_map_interleave_left, boundaryTrace_interleave_left, hcOut.emit, hcIn.emit,
          hdOut.emit, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map, h₁]
  · -- successors are componentwise equal after the regrouping
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · -- sampled paths are related by the draw transport fact
    exact samplePath_factorLeft_rel (p₁.stepSampler s₁) (p₂.stepSampler s₂) (p₃.stepSampler s₃)
      R hσ

/-- **Right factorization.** `(p₁ ∥ p₂) ∥ p₃` is sampler equivalent to
`p₂ ∥ (p₃ ∥ p₁)` when both sides decorate each leaf identically, every
scheduler node is internal, and the source and right-factored scheduler draws
are related. -/
theorem interleave_factorRight_samplerEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {cIn : OpenNodeContext.{u, w} Party Δ₁₂ (ULift.{w, 0} Bool)}
    {cOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (σIn σOut : m (ULift.{w, 0} Bool))
    {f₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ₃₂)}
    {f₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₃₂)}
    {g₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {dIn : OpenNodeContext.{u, w} Party Δ₃₂ (ULift.{w, 0} Bool)}
    {dOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (τIn τOut : m (ULift.{w, 0} Bool))
    (h₁ : TypeTree.Node.ContextHom.comp g₁ f₁ = TypeTree.Node.ContextHom.comp g₂' f₂')
    (h₂ : TypeTree.Node.ContextHom.comp g₁ f₂ = g₁')
    (h₃ : g₂ = TypeTree.Node.ContextHom.comp g₂' f₁')
    (hcOut : IsInternalNode cOut) (hcIn : IsInternalNode (g₁ _ cIn))
    (hdOut : IsInternalNode dOut) (hdIn : IsInternalNode (g₂' _ dIn))
    (hσ : R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorRight τOut τIn)) :
    OpenProcessSamplerEquiv R
      ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
      (p₂.interleave (p₃.interleave p₁ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut) := by
  refine ⟨fun (⟨⟨s₁, s₂⟩, s₃⟩ : (p₁.Proc × p₂.Proc) × p₃.Proc)
      (⟨s₂', s₃', s₁'⟩ : p₂.Proc × p₃.Proc × p₁.Proc) => s₁ = s₁' ∧ s₂ = s₂' ∧ s₃ = s₃',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, s₃⟩ => ⟨⟨s₂, s₃, s₁⟩, rfl, rfl, rfl⟩,
    fun ⟨s₂, s₃, s₁⟩ => ⟨⟨⟨s₁, s₂⟩, s₃⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₂', s₃', s₁'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parRightPathEquiv (p₁.step s₁).tree (p₂.step s₂).tree (p₃.step s₃).tree,
    ?_, ?_, ?_, ?_⟩
  · -- silence: the regrouping only moves internal nodes
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · rw [parRightPathEquiv_apply_context, isSilentStep_interleave_right_iff_decoration,
        isSilentStep_interleave_right_iff_decoration, isSilentDecoration_map_interleave_left,
        hcOut.isActivated, hdOut.isActivated, hdIn.isActivated,
        OpenNodeContext.decoration_map_map, ← h₃]
      simp
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · rw [parRightPathEquiv_apply_second, isSilentStep_interleave_left_iff_decoration,
          isSilentDecoration_map_interleave_right, isSilentStep_interleave_left_iff_decoration,
          hcOut.isActivated, hcIn.isActivated, hdOut.isActivated,
          OpenNodeContext.decoration_map_map, h₂]
        simp
      · rw [parRightPathEquiv_apply_first, isSilentStep_interleave_left_iff_decoration,
          isSilentDecoration_map_interleave_left, isSilentStep_interleave_right_iff_decoration,
          isSilentDecoration_map_interleave_right, hcOut.isActivated, hcIn.isActivated,
          hdOut.isActivated, hdIn.isActivated, OpenNodeContext.decoration_map_map,
          OpenNodeContext.decoration_map_map, h₁]
  · -- boundary traces: internal nodes emit nothing
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · rw [parRightPathEquiv_apply_context, boundaryTrace_interleave_right,
        boundaryTrace_interleave_right, boundaryTrace_map_interleave_left, hcOut.emit, hdOut.emit,
        hdIn.emit, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map, ← h₃]
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · rw [parRightPathEquiv_apply_second, boundaryTrace_interleave_left,
          boundaryTrace_map_interleave_right, boundaryTrace_interleave_left, hcOut.emit, hcIn.emit,
          hdOut.emit, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map, h₂]
      · rw [parRightPathEquiv_apply_first, boundaryTrace_interleave_left,
          boundaryTrace_map_interleave_left, boundaryTrace_interleave_right,
          boundaryTrace_map_interleave_right, hcOut.emit, hcIn.emit, hdOut.emit, hdIn.emit,
          one_mul, one_mul, one_mul, one_mul, OpenNodeContext.decoration_map_map,
          OpenNodeContext.decoration_map_map, h₁]
  · -- successors are componentwise equal after the regrouping
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · -- sampled paths are related by the draw transport fact
    exact samplePath_factorRight_rel (p₁.stepSampler s₁) (p₂.stepSampler s₂) (p₃.stepSampler s₃)
      R hσ

/-- **Commutation.** Interleaving in either order gives sampler-equivalent
composites when both scheduler nodes are internal and the flipped draw of one
side is related to the draw of the other. -/
theorem interleave_comm_samplerEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (σ : m (ULift.{w, 0} Bool))
    {d : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (τ : m (ULift.{w, 0} Bool))
    (hc : IsInternalNode c) (hd : IsInternalNode d)
    (hστ : R.rel (schedulerFlip <$> σ) τ) :
    OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ f₂ f₁ d τ) := by
  refine ⟨fun (⟨s₁, s₂⟩ : p₁.Proc × p₂.Proc) (⟨s₂', s₁'⟩ : p₂.Proc × p₁.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂',
    ⟨?_⟩,
    fun ⟨s₁, s₂⟩ => ⟨⟨s₂, s₁⟩, rfl, rfl⟩,
    fun ⟨s₂, s₁⟩ => ⟨⟨s₁, s₂⟩, rfl, rfl⟩⟩
  rintro ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ ⟨h1, h2⟩
  subst h1
  subst h2
  refine ⟨flipInterleavePathEquiv (p₁.step s₁).tree (p₂.step s₂).tree, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨b⟩, tr⟩
    cases b
    · rw [flipInterleavePathEquiv_apply_false, isSilentStep_interleave_right_iff_decoration,
        isSilentStep_interleave_left_iff_decoration, hc.isActivated, hd.isActivated]
    · rw [flipInterleavePathEquiv_apply_true, isSilentStep_interleave_left_iff_decoration,
        isSilentStep_interleave_right_iff_decoration, hc.isActivated, hd.isActivated]
  · rintro ⟨⟨b⟩, tr⟩
    cases b
    · rw [flipInterleavePathEquiv_apply_false, boundaryTrace_interleave_right,
        boundaryTrace_interleave_left, hc.emit, hd.emit]
    · rw [flipInterleavePathEquiv_apply_true, boundaryTrace_interleave_left,
        boundaryTrace_interleave_right, hc.emit, hd.emit]
  · rintro ⟨⟨b⟩, tr⟩
    cases b <;> exact ⟨rfl, rfl⟩
  · change R.rel
      ((fun tr => flipInterleavePathEquiv (p₁.step s₁).tree (p₂.step s₂).tree tr) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave τ (p₂.stepSampler s₂) (p₁.stepSampler s₁)))
    rw [samplePath_interleave_flip]
    exact samplePath_interleave_congr_scheduler R hστ _ _

/-- **Re-homing.** The same interleaving under another internal scheduler node
and a related scheduler draw is sampler equivalent. -/
theorem interleave_rehome_samplerEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (σ : m (ULift.{w, 0} Bool))
    {d : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (τ : m (ULift.{w, 0} Bool))
    (hc : IsInternalNode c) (hd : IsInternalNode d) (hστ : R.rel σ τ) :
    OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (p₁.interleave p₂ f₁ f₂ d τ) := by
  refine ⟨fun s s' => s = s', ⟨?_⟩, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩⟩
  rintro ⟨s₁, s₂⟩ _ rfl
  refine ⟨Equiv.refl _, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨b⟩, tr⟩
    cases b
    · rw [Equiv.refl_apply, isSilentStep_interleave_right_iff_decoration,
        isSilentStep_interleave_right_iff_decoration, hc.isActivated, hd.isActivated]
    · rw [Equiv.refl_apply, isSilentStep_interleave_left_iff_decoration,
        isSilentStep_interleave_left_iff_decoration, hc.isActivated, hd.isActivated]
  · rintro ⟨⟨b⟩, tr⟩
    cases b
    · rw [Equiv.refl_apply, boundaryTrace_interleave_right, boundaryTrace_interleave_right,
        hc.emit, hd.emit]
    · rw [Equiv.refl_apply, boundaryTrace_interleave_left, boundaryTrace_interleave_left,
        hc.emit, hd.emit]
  · rintro ⟨⟨b⟩, tr⟩
    cases b <;> rfl
  · change R.rel
      ((fun tr => (Equiv.refl _) tr) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave τ (p₁.stepSampler s₁) (p₂.stepSampler s₂)))
    have heq : (fun tr => (Equiv.refl _) tr) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)) =
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)) := by
      simp only [Equiv.refl_apply, id_map']
    rw [heq]
    exact samplePath_interleave_congr_scheduler R hστ _ _

end Shapes

/-! ## Congruence -/

section Congruence

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m] {Party : Type u}
  {Δ₁ Δ₂ Δ : PortBoundary} (R : MonadRelFamily m) [R.IsBindCongr]
  (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
  (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
    (OpenNodeContext.{u, w} Party Δ)}
  {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
    (OpenNodeContext.{u, w} Party Δ)}
  {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}

open OpenProcess OpenNodeContext

/-- Sampler equivalence is preserved by interleaving on the left, when the
left injection preserves activation and relabels traces. The scheduler node
is arbitrary: both sides carry the same one. -/
theorem OpenProcess.interleave_congr_left_samplerEquiv
    (hf₁ : PreservesActivation f₁)
    {g : PFunctor.Idx Δ₁.Out → Option (PFunctor.Idx Δ.Out)} (hg : EmitsAlong f₁ g)
    (σ : m (ULift.{w, 0} Bool))
    {q₁ : OpenProcess.{u, v, w, w'} m Party Δ₁} (h : OpenProcessSamplerEquiv R p₁ q₁) :
    OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (q₁.interleave p₂ f₁ f₂ c σ) := by
  obtain ⟨rel, hbisim, htot₁, htot₂⟩ := h
  refine ⟨fun (⟨s₁, s₂⟩ : p₁.Proc × p₂.Proc) (⟨s₁', s₂'⟩ : q₁.Proc × p₂.Proc) =>
      rel s₁ s₁' ∧ s₂ = s₂', ⟨?_⟩, ?_, ?_⟩
  · rintro ⟨s₁, s₂⟩ ⟨s₁', s₂'⟩ ⟨hrel, h2⟩
    subst h2
    obtain ⟨e, hsil, htr, hnext, hsam⟩ := hbisim.step_equiv s₁ s₁' hrel
    refine ⟨leftBranchPathEquiv e (p₂.step s₂).tree, ?_, ?_, ?_, ?_⟩
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · rw [leftBranchPathEquiv_apply_false, isSilentStep_interleave_right_iff_decoration,
          isSilentStep_interleave_right_iff_decoration]
      · rw [leftBranchPathEquiv_apply_true, isSilentStep_interleave_left_iff_decoration,
          isSilentStep_interleave_left_iff_decoration, isSilentDecoration_iff_map f₁ hf₁,
          isSilentDecoration_iff_map f₁ hf₁]
        have hs := hsil tr
        unfold IsSilentStep at hs
        exact and_congr Iff.rfl hs
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · rw [leftBranchPathEquiv_apply_false, boundaryTrace_interleave_right,
          boundaryTrace_interleave_right]
      · rw [leftBranchPathEquiv_apply_true, boundaryTrace_interleave_left,
          boundaryTrace_interleave_left, boundaryTrace_map_of_emitsAlong hg,
          boundaryTrace_map_of_emitsAlong hg, htr tr]
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · exact ⟨hrel, rfl⟩
      · exact ⟨hnext tr, rfl⟩
    · change R.rel
        ((fun tr => leftBranchPathEquiv e (p₂.step s₂).tree tr) <$>
          TypeTree.samplePath _
            (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)))
        (TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (q₁.stepSampler s₁') (p₂.stepSampler s₂)))
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine R.bind_congr_right σ fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        change R.rel
          (TypeTree.samplePath _ (p₂.stepSampler s₂) >>= fun tr =>
            pure (⟨⟨false⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (q₁.step s₁').tree
              | ⟨false⟩ => (p₂.step s₂).tree)))
          (TypeTree.samplePath _ (p₂.stepSampler s₂) >>= fun tr =>
            pure (⟨⟨false⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (q₁.step s₁').tree
              | ⟨false⟩ => (p₂.step s₂).tree)))
        exact R.refl _
      · simp only [map_pure]
        change R.rel
          (TypeTree.samplePath _ (p₁.stepSampler s₁) >>= fun tr =>
            pure (⟨⟨true⟩, e tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (q₁.step s₁').tree
              | ⟨false⟩ => (p₂.step s₂).tree)))
          (TypeTree.samplePath _ (q₁.stepSampler s₁') >>= fun tr =>
            pure (⟨⟨true⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (q₁.step s₁').tree
              | ⟨false⟩ => (p₂.step s₂).tree)))
        have h' := R.bind_congr (fun tr => pure (⟨⟨true⟩, tr⟩ :
          TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (q₁.step s₁').tree
              | ⟨false⟩ => (p₂.step s₂).tree))) hsam
        rw [bind_map_left] at h'
        exact h'
  · rintro ⟨s₁, s₂⟩
    obtain ⟨s₁', hs⟩ := htot₁ s₁
    exact ⟨⟨s₁', s₂⟩, hs, rfl⟩
  · rintro ⟨s₁', s₂⟩
    obtain ⟨s₁, hs⟩ := htot₂ s₁'
    exact ⟨⟨s₁, s₂⟩, hs, rfl⟩

/-- Sampler equivalence is preserved by interleaving on the right, when the
right injection preserves activation and relabels traces. -/
theorem OpenProcess.interleave_congr_right_samplerEquiv
    (hf₂ : PreservesActivation f₂)
    {g : PFunctor.Idx Δ₂.Out → Option (PFunctor.Idx Δ.Out)} (hg : EmitsAlong f₂ g)
    (σ : m (ULift.{w, 0} Bool))
    {q₂ : OpenProcess.{u, v, w, w'} m Party Δ₂} (h : OpenProcessSamplerEquiv R p₂ q₂) :
    OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (p₁.interleave q₂ f₁ f₂ c σ) := by
  obtain ⟨rel, hbisim, htot₁, htot₂⟩ := h
  refine ⟨fun (⟨s₁, s₂⟩ : p₁.Proc × p₂.Proc) (⟨s₁', s₂'⟩ : p₁.Proc × q₂.Proc) =>
      s₁ = s₁' ∧ rel s₂ s₂', ⟨?_⟩, ?_, ?_⟩
  · rintro ⟨s₁, s₂⟩ ⟨s₁', s₂'⟩ ⟨h1, hrel⟩
    subst h1
    obtain ⟨e, hsil, htr, hnext, hsam⟩ := hbisim.step_equiv s₂ s₂' hrel
    refine ⟨rightBranchPathEquiv (p₁.step s₁).tree e, ?_, ?_, ?_, ?_⟩
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · rw [rightBranchPathEquiv_apply_false, isSilentStep_interleave_right_iff_decoration,
          isSilentStep_interleave_right_iff_decoration, isSilentDecoration_iff_map f₂ hf₂,
          isSilentDecoration_iff_map f₂ hf₂]
        have hs := hsil tr
        unfold IsSilentStep at hs
        exact and_congr Iff.rfl hs
      · rw [rightBranchPathEquiv_apply_true, isSilentStep_interleave_left_iff_decoration,
          isSilentStep_interleave_left_iff_decoration]
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · rw [rightBranchPathEquiv_apply_false, boundaryTrace_interleave_right,
          boundaryTrace_interleave_right, boundaryTrace_map_of_emitsAlong hg,
          boundaryTrace_map_of_emitsAlong hg, htr tr]
      · rw [rightBranchPathEquiv_apply_true, boundaryTrace_interleave_left,
          boundaryTrace_interleave_left]
    · rintro ⟨⟨b⟩, tr⟩
      cases b
      · exact ⟨rfl, hnext tr⟩
      · exact ⟨rfl, hrel⟩
    · change R.rel
        ((fun tr => rightBranchPathEquiv (p₁.step s₁).tree e tr) <$>
          TypeTree.samplePath _
            (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)))
        (TypeTree.samplePath _
          (TypeTree.Sampler.interleave σ (p₁.stepSampler s₁) (q₂.stepSampler s₂')))
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine R.bind_congr_right σ fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        change R.rel
          (TypeTree.samplePath _ (p₂.stepSampler s₂) >>= fun tr =>
            pure (⟨⟨false⟩, e tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (p₁.step s₁).tree
              | ⟨false⟩ => (q₂.step s₂').tree)))
          (TypeTree.samplePath _ (q₂.stepSampler s₂') >>= fun tr =>
            pure (⟨⟨false⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (p₁.step s₁).tree
              | ⟨false⟩ => (q₂.step s₂').tree)))
        have h' := R.bind_congr (fun tr => pure (⟨⟨false⟩, tr⟩ :
          TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (p₁.step s₁).tree
              | ⟨false⟩ => (q₂.step s₂').tree))) hsam
        rw [bind_map_left] at h'
        exact h'
      · simp only [map_pure]
        change R.rel
          (TypeTree.samplePath _ (p₁.stepSampler s₁) >>= fun tr =>
            pure (⟨⟨true⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (p₁.step s₁).tree
              | ⟨false⟩ => (q₂.step s₂').tree)))
          (TypeTree.samplePath _ (p₁.stepSampler s₁) >>= fun tr =>
            pure (⟨⟨true⟩, tr⟩ : TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (p₁.step s₁).tree
              | ⟨false⟩ => (q₂.step s₂').tree)))
        exact R.refl _
  · rintro ⟨s₁, s₂⟩
    obtain ⟨s₂', hs⟩ := htot₁ s₂
    exact ⟨⟨s₁, s₂'⟩, rfl, hs⟩
  · rintro ⟨s₁, s₂'⟩
    obtain ⟨s₂, hs⟩ := htot₂ s₂'
    exact ⟨⟨s₁, s₂⟩, rfl, hs⟩

omit [LawfulMonad m] [R.IsBindCongr] in
/-- Sampler equivalence is preserved by re-decoration along an
activation-preserving hom that relabels traces. -/
theorem OpenProcess.mapHom_congr_samplerEquiv
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂)}
    (hh : PreservesActivation h)
    {g : PFunctor.Idx Δ₁.Out → Option (PFunctor.Idx Δ₂.Out)} (hg : EmitsAlong h g)
    {p q : OpenProcess.{u, v, w, w'} m Party Δ₁} (hpq : OpenProcessSamplerEquiv R p q) :
    OpenProcessSamplerEquiv R (p.mapHom h) (q.mapHom h) := by
  obtain ⟨rel, hbisim, htot₁, htot₂⟩ := hpq
  refine ⟨rel, ⟨?_⟩, htot₁, htot₂⟩
  intro s₁ s₂ hrel
  obtain ⟨e, hsil, htr, hnext, hsam⟩ := hbisim.step_equiv s₁ s₂ hrel
  refine ⟨e, ?_, ?_, hnext, hsam⟩
  · intro tr
    exact (isSilentStep_mapHom_iff hh p s₁ tr).trans
      ((hsil tr).trans (isSilentStep_mapHom_iff hh q s₂ (e tr)).symm)
  · intro tr
    exact (boundaryTrace_map_of_emitsAlong hg (p.step s₁).semantics tr).trans
      ((congrArg (PFunctor.TraceList.mapPartial g) (htr tr)).trans
        (boundaryTrace_map_of_emitsAlong hg (q.step s₂).semantics (e tr)).symm)

end Congruence

/-! ## Derived reassociation -/

section Assoc

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m] {Party : Type u}
  {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ : PortBoundary}
  (R : MonadRelFamily m) [R.IsBindCongr]
  (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
  (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  (p₃ : OpenProcess.{u, v, w, w'} m Party Δ₃)

open OpenProcess OpenNodeContext

/-- **Reassociation.** `(p₁ ∥ p₂) ∥ p₃` is sampler equivalent to
`p₁ ∥ (p₂ ∥ p₃)`: the left factorization followed by commutation of the inner
pair under the congruence. The inner scheduler draw `τIn'` of the factored
shape is related to the flipped inner draw `τIn` of the target. -/
theorem interleave_assoc_samplerEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {cIn : OpenNodeContext.{u, w} Party Δ₁₂ (ULift.{w, 0} Bool)}
    {cOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (σIn σOut : m (ULift.{w, 0} Bool))
    {f₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₂₃)}
    {f₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ₂₃)}
    {g₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {dIn : OpenNodeContext.{u, w} Party Δ₂₃ (ULift.{w, 0} Bool)}
    {dOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (τIn τIn' τOut : m (ULift.{w, 0} Bool))
    (h₁ : TypeTree.Node.ContextHom.comp g₁ f₁ = g₁')
    (h₂ : TypeTree.Node.ContextHom.comp g₁ f₂ = TypeTree.Node.ContextHom.comp g₂' f₁')
    (h₃ : g₂ = TypeTree.Node.ContextHom.comp g₂' f₂')
    (hcOut : IsInternalNode cOut) (hcIn : IsInternalNode (g₁ _ cIn))
    (hdOut : IsInternalNode dOut) (hdIn : IsInternalNode dIn)
    (hdIn' : IsInternalNode (g₂' _ dIn))
    (hg₂' : PreservesActivation g₂')
    {gg : PFunctor.Idx Δ₂₃.Out → Option (PFunctor.Idx Δ.Out)} (hgg : EmitsAlong g₂' gg)
    (hσ : R.rel (nestedDrawLeft σOut σIn) (nestedDrawFactorLeft τOut τIn'))
    (hτ : R.rel (schedulerFlip <$> τIn') τIn) :
    OpenProcessSamplerEquiv R
      ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
      (p₁.interleave (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut) :=
  (interleave_factorLeft_samplerEquiv R p₁ p₂ p₃ σIn σOut τIn' τOut h₁ h₂ h₃ hcOut hcIn hdOut
    hdIn' hσ).trans
    (OpenProcess.interleave_congr_right_samplerEquiv R p₁ _ hg₂' hgg τOut
      (interleave_comm_samplerEquiv R p₃ p₂ τIn' τIn hdIn hdIn hτ))

end Assoc

end UC
end Interaction
