/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Lawful monad functors

`MonadFunctor m n` maps an endo-transformation `{β : Type u} → m β → m β` of the inner monad over
the outer one. `LawfulMonadFunctor m n` states that this map preserves the identity and
composites, and `LawfulMonadFunctorT m n` states the same for the reflexive-transitive closure
`MonadFunctorT`, with instances for its reflexive and transitive steps. The classes parallel core's
`LawfulMonadLift` and `LawfulMonadLiftT`.
-/

@[expose] public section

universe u v w

/-- A `MonadFunctor` whose map preserves the identity and composites of endo-transformations. -/
class LawfulMonadFunctor (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadFunctor m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    MonadFunctor.monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@MonadFunctor.monadMap m n _ α f) ∘ (@MonadFunctor.monadMap m n _ α g) =
      @MonadFunctor.monadMap m n _ α (f ∘ g)

/-- A `MonadFunctorT` whose map preserves the identity and composites of endo-transformations. -/
class LawfulMonadFunctorT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadFunctorT m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@monadMap m n _ α f) ∘ (@monadMap m n _ α g) = @monadMap m n _ α (f ∘ g)

export LawfulMonadFunctorT (monadMap_id monadMap_comp)

attribute [simp] monadMap_id monadMap_comp

/-- The transitive step of `MonadFunctorT` preserves lawfulness. -/
instance {m n o} [Monad m] [Monad n] [Monad o] [MonadFunctor n o] [MonadFunctorT m n]
    [LawfulMonadFunctor n o] [LawfulMonadFunctorT m n] : LawfulMonadFunctorT m o where
  monadMap_id := by
    intro α
    change
      @MonadFunctor.monadMap n o _ α
          (fun {β} => @monadMap m n _ β (fun {γ} => (id : m γ → m γ))) = id
    have hmn :
        (fun {β} => @monadMap m n _ β (fun {γ} => (id : m γ → m γ))) =
          fun {β} => (id : n β → n β) := by
      funext β
      exact LawfulMonadFunctorT.monadMap_id (m := m) (n := n) (α := β)
    rw [hmn]
    simpa using (LawfulMonadFunctor.monadMap_id (m := n) (n := o) (α := α))
  monadMap_comp := by
    intro α f g
    change
      (@MonadFunctor.monadMap n o _ α
          (fun {β} => @monadMap m n _ β f)) ∘
        (@MonadFunctor.monadMap n o _ α
          (fun {β} => @monadMap m n _ β g)) =
      @MonadFunctor.monadMap n o _ α
        (fun {β} => @monadMap m n _ β (f ∘ g))
    rw [LawfulMonadFunctor.monadMap_comp
      (m := n) (n := o) (α := α)
      (f := fun {β} => @monadMap m n _ β f)
      (g := fun {β} => @monadMap m n _ β g)]
    have hmn :
        (fun {β} => (@monadMap m n _ β f) ∘ (@monadMap m n _ β g)) =
          fun {β} => @monadMap m n _ β (f ∘ g) := by
      funext β
      exact LawfulMonadFunctorT.monadMap_comp (m := m) (n := n) (α := β) f g
    rw [hmn]

/-- The reflexive step of `MonadFunctorT` is lawful. -/
instance lawfulMonadFunctorRefl {m} [Monad m] : LawfulMonadFunctorT m m where
  monadMap_id := by intro α; rfl
  monadMap_comp := by intro α f g; rfl
