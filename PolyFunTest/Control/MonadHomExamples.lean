/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import PolyFun.Control.Monad.Hom.Writer

/-!
# Examples for the monad-morphism hierarchy

These examples pin the division of labour documented in
`PolyFun/Control/Monad/Hom.lean`: core's `MonadLift` / `LawfulMonadLift` family
supplies the *unbundled*, instance-found morphisms, `MonadHom` supplies the
*bundled* arrow, and `MonadHom.ofLift` is the only bridge between them.
-/

@[expose] public section

universe u v w

namespace Control.MonadHomExamples

section Bridge

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]

/-- Core finds the lift; `ofLift` turns it into an arrow. -/
example [MonadLiftT m n] [LawfulMonadLiftT m n] : m →ᵐ n := MonadHom.ofLift m n

/-- The arrow really is `liftM`, definitionally. -/
example [MonadLiftT m n] [LawfulMonadLiftT m n] {α : Type u} (x : m α) :
    MonadHom.ofLift m n x = liftM x := rfl

/-- Core's transformer instances are enough for the bridge to fire: no PolyFun
instance is involved in producing this arrow. -/
example (σ : Type u) [LawfulMonad m] : m →ᵐ StateT σ m := MonadHom.ofLift m (StateT σ m)

example (ε : Type u) [LawfulMonad m] : m →ᵐ ExceptT ε m := MonadHom.ofLift m (ExceptT ε m)

example (ρ : Type u) [LawfulMonad m] : m →ᵐ ReaderT ρ m := MonadHom.ofLift m (ReaderT ρ m)

/-- Lawfulness of the lift is what the two `MonadHom` fields consume, so the
core simp set discharges them. -/
example [MonadLiftT m n] [LawfulMonadLiftT m n] {α : Type u} (a : α) :
    liftM (pure a : m α) = (pure a : n α) := by simp

end Bridge

section Structure

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Bundled morphisms compose and have identities, which is what makes them
usable as data rather than as instances. -/
example (σ : Type u) : Id →ᵐ StateT σ m :=
  MonadHom.ofLift m (StateT σ m) ∘ₘ MonadHom.pure m

example {α : Type u} (σ : Type u) (x : Id α) :
    (MonadHom.ofLift m (StateT σ m) ∘ₘ MonadHom.pure m) x = liftM (pure x.run : m α) := rfl

/-- `StateT σ` transports a morphism, acting on the state-run. -/
example {n : Type u → Type w} [Monad n] [LawfulMonad n] (σ : Type u) (φ : m →ᵐ n) :
    StateT σ m →ᵐ StateT σ n := StateT.mapHom φ

example {n : Type u → Type w} [Monad n] [LawfulMonad n] {α σ : Type u}
    (φ : m →ᵐ n) (x : StateT σ m α) (s : σ) :
    (StateT.mapHom φ x).run s = φ (x.run s) := rfl

end Structure

section TransformerMaps

/-- A nonidentity target effect makes it observable that each transformer map acts on
the underlying monad rather than merely repackaging its source representation. -/
def idToOption : Id →ᵐ Option := MonadHom.pure Option

/-- The environment still selects the source value before the underlying morphism runs. -/
def branchReader : ReaderT Bool Id Nat :=
  ReaderT.mk fun flag => if flag then 7 else 11

example : (ReaderT.mapHom idToOption branchReader).run true = some 7 := rfl
example : (ReaderT.mapHom idToOption branchReader).run false = some 11 := rfl

/-- Source-level `none` remains a successful target effect carrying `none`; it is not
confused with failure in the target `Option` monad. -/
def absent : OptionT Id Nat := OptionT.mk none

example : (OptionT.mapHom idToOption absent).run = some none := rfl

/-- Likewise, an `ExceptT` error remains data inside the successful target effect. -/
def rejected : ExceptT String Id Nat := ExceptT.mk (.error "rejected")

example : (ExceptT.mapHom idToOption rejected).run = some (.error "rejected") := rfl

/-- Writer output remains data while the underlying effect is transported. -/
def logged : WriterT Nat Id Nat := WriterT.mk (7, 3)

example : (WriterT.mapHom idToOption logged).run = some (7, 3) := rfl

end TransformerMaps

end Control.MonadHomExamples
