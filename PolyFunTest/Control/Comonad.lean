/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Control.Comonad.Instances
import PolyFun.PFunctor.Cofree

/-! # Comonads and independent choices of context pairing

Generic comonad consumers and transformers need no pairing policy. Concrete
pairing instances retain their chosen behavior and share the functor operations.
-/

@[expose] public section

universe u v

example (w : Type u → Type v) [Comonad w] : True := by
  fail_if_success have : Coapplicative w := inferInstance
  trivial

example (w : Type u → Type v) [Comonad w] [LawfulComonad w] (ε : Type u) :
    LawfulComonad (EnvT ε w) := inferInstance

example (w : Type u → Type v) [Comonad w] [LawfulComonad w] (σ : Type u) :
    LawfulComonad (StoreT σ w) := inferInstance

example (w : Type u → Type v) [Coapplicative w] [LawfulCoapplicative w] (σ : Type u) :
    LawfulCoapplicative (StoreT σ w) := inferInstance

example (w : Type u → Type u) [Comonad w] [LawfulComonad w]
    {α : Type u} (x : w α) :
    extract (duplicate x) = x ∧
      Functor.map extract (duplicate x) = x ∧
      duplicate (duplicate x) = Functor.map duplicate (duplicate x) :=
  ⟨extract_duplicate_eq_id x, map_extract_duplicate_eq_id x,
    duplicate_duplicate_eq_map_duplicate x⟩

/-- Stream pairing observes both streams at the same index. -/
example {α β : Type u} (xs : Stream' α) (ys : Stream' β) (n : Nat) :
    Stream'.get (xs <@> ys) n = (Stream'.get xs n, Stream'.get ys n) := rfl

/-- The independent hierarchy paths share exactly the same mapping operation. -/
example {α β : Type u} (f : α → β) (xs : Stream' α) :
    @Functor.map Stream' (Comonad.toFunctor (w := Stream')) α β f xs =
      @Functor.map Stream' (Coapplicative.toFunctor (w := Stream')) α β f xs := rfl

example {P : PFunctor.{u, u}} {α β : Type u} (f : α → β) (x : PFunctor.CofreeC P α) :
    @Functor.map (PFunctor.CofreeC P) (Comonad.toFunctor) α β f x =
      @Functor.map (PFunctor.CofreeC P) (Coapplicative.toFunctor) α β f x := rfl
