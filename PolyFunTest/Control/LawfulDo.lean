/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import PolyFun.Control.Monad.Free

/-!
# Monad laws against `do`-notation goals

Canaries that core's `LawfulMonad` lemmas close goals stated with `do` notation directly:
the `Bind` instance the `do` elaborator picks is the one `Monad.toBind` provides, so
`bind_assoc`, `bind_pure_comp`, and `bind_map_left` apply by `exact`, and the dependent-pair
shape used by two-party strategy composition (`PolyFun/Interaction/TwoParty/Compose.lean`)
is one `simp only` step.
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
