/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Foundations.Data.PFunctor.Free.Fold

/-!
# Algebraic operations on the free polynomial monad

cslib's catamorphism `FreeM.foldFreeM` evaluates a tree in an arbitrary algebra of its signature,
with its universal property `foldFreeM_unique` and substitution law `foldFreeM_bind`. This module
adds the constructor-spelled node equations for the fold and for `FreeM.map`, which supplement
cslib's `(lift a).bind` spellings and universe-polymorphic functor laws.
Heterogeneous map composition and bind-after-map laws support changes of leaf universe.
Monadic interpretation and handler fusion use cslib's `FreeM.liftM` and `IsMonadHom` API.
-/

public section

universe u v w uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type*}

/-- Mapping twice composes the leaf functions, including across independent universes. -/
theorem map_map {γ : Type*} (f : β → γ) (g : α → β) (program : P.FreeM α) :
    map f (map g program) = map (f ∘ g) program := by
  induction program with
  | pure _ => rfl
  | lift_bind a next ih => exact congrArg (FreeM.liftBind a) (funext ih)

/-- A heterogeneous leaf map can be absorbed by the subsequent continuation. -/
theorem bind_map {γ : Type*} (f : α → β) (program : P.FreeM α) (next : β → P.FreeM γ) :
    (map f program).bind next = program.bind (next ∘ f) := by
  induction program with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind a) (funext ih)

/-! ## Constructor-spelled node equations -/

/-- Mapping through a node maps every continuation, in constructor spelling. -/
theorem map_liftBind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f (FreeM.liftBind a cont) = FreeM.liftBind a fun b => map f (cont b) :=
  rfl

/-- Folding a node applies the node handler to the folded continuation, in constructor
spelling. -/
theorem foldFreeM_liftBind (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (FreeM.liftBind a cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

end PFunctor.FreeM
