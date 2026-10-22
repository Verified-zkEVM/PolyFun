/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Order.Monotone.Defs
public import PolyFun.Control.Monad.Algebra
public import PolyFun.Control.Monad.Relation

/-!
# Ordered monads

An ordered monad carries a preorder on each type of computations, and its `bind` is monotone in
both the computation and the continuation. Core's `Lean.Order.MonoBind` states the same
monotonicity over core's `Lean.Order.PartialOrder`, the order `partial_fixpoint` uses;
`OrderedMonad` uses Mathlib's `Preorder`.

## Main definitions

- `OrderedMonad`, a monad with a preorder on each `m α` and monotone `bind`, and its unbundled
  form `Monad.IsOrdered`, which `OrderedMonad.ofIsOrdered` bundles. The scoped instance
  `OrderedMonad.Discrete.instDiscreteMonad` orders any monad by equality.
- `OrderedMonadAlgebra`, a monad algebra that is monotone in the computation and the map.
- `MonadLift.LE`, comparing two lifts; the preorder on the lifts into an ordered monad; and the
  monotone lifts `OrderedMonadLift` and `OrderedMonadLiftT`.
- `MonadRelation.ofOrderedMonadLiftT`, the monad relation `monadLift ma ≤ₘ na`, and
  `MonadRelation.IsUpperClosed`, a relation closed upwards in the order of its target.
- `AssertAssume` and `Monad.AssertAssume`: assertion and assumption operators that are adjoint on
  a preorder.
- `OrderedMonad.LeftKanExtension` and `OrderedMonad.RightKanExtension`: the greatest continuation
  that keeps `p >>= ext` below `f`, and its dual.

`OrderedMonadLiftT` has only its reflexive instance. A transitive instance would need the
`OrderedMonad` instance of the intermediate monad before instance search determines that monad
from the outer `OrderedMonadLift`, so chains of lifts are composed by hand.
-/

@[expose] public section

universe u v w

/-- An ordered monad `m` is a monad equipped with a preorder on each type `m α`, such that the bind
operation preserves the order. -/
class OrderedMonad (m : Type u → Type v) extends Monad m where
  /-- The preorder on the computations at each result type. -/
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

export OrderedMonad (monadOrder bind_mono)

instance {m} [OrderedMonad m] {α : Type u} : Preorder (m α) := monadOrder

attribute [simp] bind_mono

/-- The unbundled form of `OrderedMonad`: a preorder on each type of computations of a monad,
preserved by `bind`. `OrderedMonad.ofIsOrdered` bundles it. -/
class Monad.IsOrdered (m : Type u → Type v) [Monad m] where
  /-- The preorder on the computations at each result type. -/
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'

namespace OrderedMonad

/-- Bundle an ordered monad from its unbundled form. It is a definition rather than an instance,
so that the search for `Monad m` does not cycle through `OrderedMonad m`. -/
@[reducible] def ofIsOrdered (m : Type u → Type v) [Monad m] [Monad.IsOrdered m] :
    OrderedMonad m where
  monadOrder := Monad.IsOrdered.monadOrder
  bind_mono := Monad.IsOrdered.bind_mono

/-- The less-than-or-equal relation on an ordered monad `m`. -/
@[reducible] def monadLE {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.le

/-- The less-than relation on an ordered monad `m`. -/
@[reducible] def monadLT {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.lt

@[inherit_doc] scoped infix:50 " ≤ₘ " => OrderedMonad.monadLE
@[inherit_doc] scoped infix:50 " <ₘ " => OrderedMonad.monadLT

macro_rules | `($x ≤ₘ $y)  => `(binrel% OrderedMonad.monadLE $x $y)
macro_rules | `($x <ₘ $y)  => `(binrel% OrderedMonad.monadLT $x $y)

namespace Discrete

/-- Any monad can be given the discrete preorder, where `a ≤ b` if and only if `a = b`.

This is put into the `Discrete` scope in order to avoid conflicts with other instances. This
instance should only be used as a last resort. -/
scoped instance (priority := low) instDiscreteMonad (m) [Monad m] : OrderedMonad m where
  monadOrder := {
    le := (· = ·)
    le_refl _ := rfl
    le_trans _ _ _ hab hbc := hab.trans hbc
  }
  bind_mono h hf := by
    subst h
    rename_i f g
    have hfg : f = g := funext hf
    subst hfg
    rfl

end Discrete

end OrderedMonad

export OrderedMonad (monadLE monadLT)

open OrderedMonad

/-- A monad algebra over an ordered monad, with a preorder on every carrier, whose structure map
is monotone in both the computation and the map applied before it. -/
class OrderedMonadAlgebra (m : Type u → Type v) [OrderedMonad m] [MonadAlgebra m] where
  /-- The preorder on every carrier. -/
  [carrierOrder {α : Type u} : Preorder α]
  monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
    (hm : ma ≤ₘ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))

export OrderedMonadAlgebra (monadAlg_mono)

attribute [simp] monadAlg_mono

section MonadLift

/-- Two lifts into an ordered monad, the first below the second at every computation. -/
class MonadLift.LE (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [φ : MonadLift m n] [ψ : MonadLift m n] where
  /-- The first lift of `a` is below the second. -/
  monadLift_le {α} (a : m α) : φ.monadLift a ≤ₘ ψ.monadLift a

/-- If the target monad `n` is ordered, then we have a preorder on the monad lifts from `m`
to `n`. -/
instance {m n} [OrderedMonad n] : Preorder (MonadLift m n) where
  le := fun φ ψ => ∀ {α : Type u} (a : m α), φ.monadLift a ≤ₘ ψ.monadLift a
  le_refl _ := by intro α a; simp only [ge_iff_le, le_refl]
  le_trans _ _ _ h1 h2 := by
    intro α a
    exact (h1 a).trans (h2 a)

/-- A monad lift between ordered monads that is monotone at every result type. -/
class OrderedMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLift m n where
  monadLift_mono {α} : Monotone (@monadLift α)

/-- A transitive monad lift between ordered monads that is monotone at every result type. -/
class OrderedMonadLiftT (m : Type u → Type v) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLiftT m n where
  monadLift_mono {α} : Monotone (@monadLift α)

export OrderedMonadLiftT (monadLift_mono)

attribute [simp] monadLift_mono

@[simp] theorem monadLift_mono' {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n]
    {α} {a b : m α} (h : a ≤ₘ b) : monadLift a ≤ₘ (monadLift b : n α) :=
  (monadLift_mono (m := m) (n := n) (α := α)) h

instance {m} [OrderedMonad m] : OrderedMonadLiftT m m where
  monadLift_mono h := by simp only [monadLift_self, h]

open OrderedMonad Discrete in
/--
Given the (default) discrete preorder on the beginning monad `m`, we can have a preorder on the
monad lifts from `m` to `n`.

This is stated as a definition and not an instance, since oftentimes we want to have another
instance on the monad lift.
-/
@[reducible] def instDiscreteMonadLift {m n} [Monad m] [h : OrderedMonad n] [MonadLift m n] :
    OrderedMonadLift m n where
  monadLift_mono h := by rename_i a b; have : a = b := h; simp only [this, le_refl]

end MonadLift

namespace MonadRelation

open scoped MonadRelation

/-- A monad relation that is closed upwards in the order of the target monad. -/
class IsUpperClosed (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [MonadRelation m n] where
  monadRel_upper_closed {α} {ma : m α} {na na' : n α} (hr : ma ∼ₘ na) (hn : na ≤ₘ na') : ma ∼ₘ na'

/-- The monad relation of a lift into an ordered monad: `ma` is related to every computation above
its lift. It is a definition rather than an instance, because the graph of the lift,
`MonadRelation.instOfMonadLiftT`, is the instance on the same pair of monads. -/
@[reducible] def ofOrderedMonadLiftT (m n) [OrderedMonad n] [MonadLiftT m n] :
    MonadRelation m n where
  monadRel := fun a b => monadLift a ≤ₘ b

/-- The relation `monadLift ma ≤ₘ na` of a lawful lift is lawful. -/
theorem lawfulMonadRelation_ofOrderedMonadLiftT (m n) [Monad m] [OrderedMonad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] :
    @LawfulMonadRelation m n _ _ (ofOrderedMonadLiftT m n) :=
  letI := ofOrderedMonadLiftT m n
  { monadRel_pure := by
      simp only [monadRel, liftM_pure, ge_iff_le, le_refl, implies_true]
    monadRel_bind := fun ha hb => by
      simp_all only [monadRel, ge_iff_le, liftM_bind, implies_true, bind_mono] }

end MonadRelation

/-- Assertion and assumption operators on a preorder: `assert p` strengthens, `assume p` weakens,
and the two are adjoint. -/
class AssertAssume (α : Type u) [Preorder α] where
  /-- Strengthen an element by an assertion. -/
  assert : Prop → α → α
  /-- Weaken an element by an assumption. -/
  assume : Prop → α → α
  assert_strengthen : ∀ p x, assert p x ≤ x
  assume_weaken : ∀ p x, x ≤ assume p x
  assert_assume_iff : ∀ p x y, assert p x ≤ y ↔ x ≤ assume p y

/-- Assertion and assumption operators on every type of computations of `m`. -/
class Monad.AssertAssume (m : Type u → Type v) [∀ α, Preorder (m α)] where
  /-- The assertion and assumption operators at each result type. -/
  assertAssume {α} : _root_.AssertAssume (m α)

namespace OrderedMonad

section KanExtension

variable {w : Type u → Type v} [OrderedMonad w]

/-- The left Kan extension of `f` along `p`: a continuation `ext` with `p >>= ext ≤ₘ f` that lies
above every other such continuation. -/
def LeftKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : α → w β // p >>= ext ≤ₘ f ∧ (∀ w', p >>= w' ≤ₘ f → ∀ b, w' b ≤ₘ ext b) }

/-- The right Kan extension of `p` along `f`: a continuation `ext` with `f >>= ext ≤ₘ p` that lies
above every other such continuation. -/
def RightKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : β → w α // f >>= ext ≤ₘ p ∧ (∀ w', f >>= w' ≤ₘ p → ∀ a, w' a ≤ₘ ext a) }

end KanExtension

end OrderedMonad
