/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Interaction.TwoParty.Compose

/-!
# Monad laws against `do`-notation goals

Ordinary-import canaries for the standard monad laws used by two-party strategy
composition. The goals quantify over an arbitrary lawful monad with independent
universes. The associativity and mapped-bind laws apply directly to `do` forms;
the dependent-pair goal follows from its equality hypothesis and `pure_bind`.
-/

@[expose] public section

universe u v

namespace PolyFunTest.Control.LawfulDo

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β γ : Type u}

example (x : m α) (f : α → m β) (g : β → m γ) :
    (do let b ← (do let a ← x; f a); g b) = (do let a ← x; let b ← f a; g b) :=
  bind_assoc x f g

example (f : α → β) (x : m α) :
    (do let a ← x; pure (f a)) = f <$> x :=
  bind_pure_comp f x

example (f : α → β) (x : m α) (g : β → m γ) :
    (do let b ← f <$> x; g b) = (do let a ← x; g (f a)) :=
  bind_map_left f x g

example {δ : α → Type u} (x : α) {tail : δ x} {action : m (δ x)} (h : action = pure tail) :
    (do let rest ← action; pure (Sigma.mk x rest)) = pure (Sigma.mk x tail) := by
  simp only [h, pure_bind]

/-- The `do` forms are also reachable by `simp` alone. -/
example (x : m α) (f : α → m β) (g : β → m γ) :
    (do let b ← (do let a ← x; f a); g b) = (do let a ← x; let b ← f a; g b) := by
  simp

end PolyFunTest.Control.LawfulDo
