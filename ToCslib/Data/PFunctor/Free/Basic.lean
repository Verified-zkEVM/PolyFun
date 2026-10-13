/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Algebraic operations on the free polynomial monad

The catamorphism `foldFreeM` evaluates a tree in an arbitrary algebra of its signature.
Its substitution law describes sequencing by substitution in the leaf handler.
The node mapping equation supplements cslib's universe-polymorphic functor laws.
Monadic interpretation and handler fusion use cslib's `FreeM.liftM` and `IsMonadHom` API.
-/

public section

universe u v w uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type*}

/-! ## Bind and functor equations -/

/-- Mapping through a node maps every continuation, in constructor spelling. -/
theorem map_liftBind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f (FreeM.liftBind a cont) = FreeM.liftBind a fun b => map f (cont b) :=
  rfl

/-! ## The catamorphism

`FreeM P α` is the initial algebra of `β ↦ α ⊕ Σ a, (P.B a → β)`. An algebra is a value handler
`onValue : α → β` together with a node handler `onEffect : (a : P.A) → (P.B a → β) → β`, and
`foldFreeM` is the unique algebra morphism out of the free tree. -/

/-- Fold a free polynomial tree into any algebra of its signature. -/
@[expose]
def foldFreeM (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) : P.FreeM α → β
  | .pure a => onValue a
  | .liftBind a cont => onEffect a fun b => foldFreeM onValue onEffect (cont b)

@[simp]
theorem foldFreeM_pure (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) (a : α) :
    foldFreeM onValue onEffect (pure a) = onValue a :=
  rfl

theorem foldFreeM_liftBind (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (FreeM.liftBind a cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

/-- Sequencing substitutes the fold of the continuation for the leaf handler. -/
theorem foldFreeM_bind (onValue : β → γ) (onEffect : (a : P.A) → (P.B a → γ) → γ)
    (x : P.FreeM α) (k : α → P.FreeM β) :
    foldFreeM onValue onEffect (x.bind k) =
      foldFreeM (fun a => foldFreeM onValue onEffect (k a)) onEffect x := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => exact congrArg (onEffect a) (funext ih)

@[simp]
theorem foldFreeM_lift (a : P.A) (onValue : P.B a → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) :
    foldFreeM (α := no_index (P.B a)) onValue onEffect (FreeM.lift a) = onEffect a onValue :=
  rfl

/-- **Universal property of the fold**: a function agreeing with the algebra on leaves and on
nodes is the fold. -/
theorem foldFreeM_unique (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (h : P.FreeM α → β) (h_pure : ∀ a, h (pure a) = onValue a)
    (h_lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α),
      h ((FreeM.lift a).bind cont) = onEffect a fun b => h (cont b)) :
    h = foldFreeM onValue onEffect := by
  funext x
  induction x with
  | pure a => rw [foldFreeM_pure, h_pure]
  | lift_bind a cont ih =>
      exact (h_lift_bind a cont).trans (congrArg (onEffect a) (funext ih))

end PFunctor.FreeM
