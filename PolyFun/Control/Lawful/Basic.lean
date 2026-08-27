/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Monad laws restated via `do` notation

Lean's `do`-notation elaboration may choose a `Bind` instance that differs syntactically
from `Monad.toBind`. This prevents the standard
`pure_bind`, `bind_assoc`, and `bind_pure` lemmas from matching `do`-block goals via
`simp` or `rw`.

The lemmas in this file state the associative, mapped-bind, bind-pure-map, and
dependent-pair laws using `do` notation, so the elaborated `Bind` instance matches
the one produced in proof goals.
-/

@[expose] public section

namespace LawfulMonad

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem do_bind_assoc {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ) :
    (do let b ← (do let a ← x; f a); g b) = (do let a ← x; let b ← f a; g b) := by simp

theorem do_bind_pure_comp {α β : Type u} (f : α → β) (x : m α) :
    (do let a ← x; pure (f a)) = f <$> x := by simp

theorem do_bind_map_left {α β γ : Type u} (f : α → β) (x : m α) (g : β → m γ) :
    (do let b ← f <$> x; g b) = (do let a ← x; g (f a)) := by simp

theorem bind_pure_sigma_mk {α : Type u} {β : α → Type u} (x : α)
    {tail : β x} {action : m (β x)} (h : action = pure tail) :
    (do
      let rest ← action
      pure (Sigma.mk x rest)) = pure (Sigma.mk x tail) := by
  simp [h]

end LawfulMonad

end
