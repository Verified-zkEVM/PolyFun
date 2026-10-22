/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Monad relations

`MonadRelation m n` relates computations of two monads at each result type, written `ma ∼ₘ na`
under `open MonadRelation`. `LawfulMonadRelation` asks that the relation hold of `pure` and be
preserved by `bind`, which makes it a lax morphism between the two monads; the graph of a lawful
monad lift is the motivating instance (`MonadRelation.instOfMonadLiftT`). `MonadRelationHom` maps
one relation into another, and `LawfulMonadRelationHom` asks that related computations stay
related. A lawful monad relation presents a Dijkstra monad (`PolyFun.Control.Monad.Dijkstra`), and
the order of an ordered target monad gives another relation
(`MonadRelation.ofOrderedMonadLiftT` in `PolyFun.Control.Monad.Ordered`).
-/

@[expose] public section

universe u v w v₁ w₁ v₂ w₂

/-- A relation between the computations of `m` and of `n` at each result type. -/
class MonadRelation (m : Type u → Type v) (n : Type u → Type w) where
  /-- The relation at result type `α`. -/
  monadRel {α : Type u} : m α → n α → Prop

export MonadRelation (monadRel)

namespace MonadRelation

@[inherit_doc] scoped infix:50 " ∼ₘ " => monadRel

end MonadRelation

/-- A monad relation that holds of `pure` and is preserved by `bind`. -/
class LawfulMonadRelation (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadRelation m n] where
  /-- `pure a` is related to `pure a`. -/
  monadRel_pure {α : Type u} (a : α) : monadRel (pure a : m α) (pure a : n α)
  /-- Binding related computations to pointwise related continuations gives related results. -/
  monadRel_bind {α β : Type u} {ma : m α} {mb : α → m β} {na : n α} {nb : α → n β}
    (ha : monadRel ma na) (hb : ∀ a, monadRel (mb a) (nb a)) : monadRel (ma >>= mb) (na >>= nb)

export LawfulMonadRelation (monadRel_pure monadRel_bind)

attribute [simp] monadRel_pure monadRel_bind

namespace MonadRelation

/-- A (transitive) monad lift defines a monad relation via its graph. -/
instance instOfMonadLiftT {m n} [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun ma na => liftM ma = na

/-- A (transitive) lawful monad lift defines a lawful monad relation via its graph. -/
instance instOfLawfulMonadLiftT {m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
    LawfulMonadRelation m n where
  monadRel_pure _ := by simp only [monadRel, liftM_pure]
  monadRel_bind _ _ := by simp_all only [monadRel, liftM_bind]

end MonadRelation

/-- A pair of maps sending computations of `m₁` and `n₁` to computations of `m₂` and `n₂`. -/
class MonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂) where
  /-- The map on the left-hand monad. -/
  monadRelHomFst {α : Type u} : m₁ α → m₂ α
  /-- The map on the right-hand monad. -/
  monadRelHomSnd {α : Type u} : n₁ α → n₂ α

export MonadRelationHom (monadRelHomFst monadRelHomSnd)

open MonadRelation in
/-- A `MonadRelationHom` that sends related computations to related computations. -/
class LawfulMonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂)
    [MonadRelation m₁ n₁] [MonadRelation m₂ n₂]
    [MonadRelationHom m₁ n₁ m₂ n₂] where
  /-- Related computations have related images. -/
  monadRel_hom {α : Type u} {ma : m₁ α} {na : n₁ α} (h : ma ∼ₘ na) :
    (monadRelHomFst n₁ n₂ ma : m₂ α) ∼ₘ (monadRelHomSnd m₁ m₂ na : n₂ α)
