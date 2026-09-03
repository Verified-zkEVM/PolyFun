/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Internal.ForIn

/-!
# Transport of loops along monad morphisms

A function `F : ∀ {β}, m β → n β` that preserves `pure` and `bind` commutes with every loop
combinator that `do`-notation elaborates to: `forIn'` and `forIn` over lists, `forM`, `foldlM`,
`mapM`, and `forIn` over any container whose `PureForIn` instance reduces its loop to the list
`ForIn.toList` computes. The morphism hypotheses are stated inline, so a bundled monad
homomorphism and cslib's unbundled `IsMonadHom` predicate instantiate the same lemmas.

The list lemmas for `forM`, `foldlM`, and `mapM` follow the shapes of cslib's in-flight
`IsMonadHom.map_list*` lemmas so that the restatement on that predicate is mechanical; the
`forIn'` / `forIn` lemmas and the `PureForIn` transport are new.
-/

public section

universe u v w u₁ w₁

namespace Cslib

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  (F : ∀ {β : Type u}, m β → n β)
  (hpure : ∀ {β : Type u} (b : β), F (pure b) = pure b)
  (hbind : ∀ {β γ : Type u} (x : m β) (g : β → m γ), F (x >>= g) = F x >>= fun b => F (g b))

include hpure hbind

/-! ## Lists -/

-- upstream candidate (complements cslib#856, which covers `mapM`, `forM`, and `foldlM`)
theorem map_listForIn' {α : Type u₁} {β : Type u} (l : List α) (init : β)
    (f : (a : α) → a ∈ l → β → m (ForInStep β)) :
    F (forIn' l init f) = forIn' l init fun a h b => F (f a h b) := by
  induction l generalizing init with
  | nil => simp [hpure]
  | cons a l ih =>
    simp only [List.forIn'_cons, hbind]
    congr 1
    funext r
    cases r <;> simp [hpure, ih]

theorem map_listForIn {α : Type u₁} {β : Type u} (l : List α) (init : β)
    (f : α → β → m (ForInStep β)) :
    F (forIn l init f) = forIn l init fun a b => F (f a b) := by
  induction l generalizing init with
  | nil => simp [hpure]
  | cons a l ih =>
    simp only [List.forIn_cons, hbind]
    congr 1
    funext r
    cases r <;> simp [hpure, ih]

-- upstream: cslib#856 (`IsMonadHom.map_listForM`)
theorem map_listForM {α : Type u₁} (l : List α) (f : α → m PUnit) :
    F (l.forM f) = l.forM (F ∘ f) := by
  induction l with
  | nil => simp only [List.forM_eq_forM, List.forM_nil, hpure]
  | cons a l ih =>
    simp only [List.forM_eq_forM] at ih ⊢
    simp only [List.forM_cons, hbind, ih, Function.comp_apply]

-- upstream: cslib#856 (`IsMonadHom.map_listFoldlM`)
theorem map_listFoldlM {s : Type u} {α : Type u₁} (f : s → α → m s) (init : s) (l : List α) :
    F (l.foldlM f init) = l.foldlM (fun s a => F (f s a)) init := by
  induction l generalizing init with
  | nil => simp [hpure]
  | cons a l ih => simp [hbind, ih]

-- upstream: cslib#856 (`IsMonadHom.map_listMapM'`)
theorem map_listMapM' {α : Type u₁} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapM' f) = l.mapM' (F ∘ f) := by
  induction l with
  | nil => simp [hpure]
  | cons a l ih => simp [hbind, hpure, ih]

/-- A function preserving `pure` and `bind` preserves `Functor.map`. -/
theorem map_functorMap [LawfulMonad m] [LawfulMonad n] {β γ : Type u} (g : β → γ) (x : m β) :
    F (g <$> x) = g <$> F x := by
  rw [← bind_pure_comp, hbind, ← bind_pure_comp]
  simp only [hpure]

-- upstream: cslib#856 (`IsMonadHom.map_listMapM`)
theorem map_listMapM [LawfulMonad m] [LawfulMonad n] {α : Type u₁} {β : Type u}
    (f : α → m β) (l : List α) :
    F (l.mapM f) = l.mapM (F ∘ f) := by
  induction l with
  | nil => simp only [List.mapM_nil, hpure]
  | cons a l ih => simp only [List.mapM_cons, hbind, hpure, ih, Function.comp_apply]

/-! ## Containers iterating over a list

`Std.Internal.PureForIn` identifies the containers (arrays, ranges, iterators, …) whose loop is
the loop over the list `ForIn.toList` computes; transport then reduces to the list case. -/

theorem map_forIn_of_pureForIn {ρ : Type w₁} {α : Type u₁} {β : Type u}
    [ForIn m ρ α] [ForIn n ρ α] [ForIn Id ρ α]
    [Std.Internal.PureForIn m ρ α] [Std.Internal.PureForIn n ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β)) :
    F (forIn xs init f) = forIn xs init fun a b => F (f a b) := by
  rw [Std.Internal.PureForIn.forIn_eq (m := m) xs init f,
    Std.Internal.PureForIn.forIn_eq (m := n) xs init]
  exact map_listForIn F hpure hbind _ init f

theorem map_forIn'_of_pureForIn' {ρ : Type w₁} {α : Type u₁} {β : Type u}
    {d : Membership α ρ} [ForIn' m ρ α d] [ForIn' n ρ α d] [ForIn Id ρ α]
    [Std.Internal.LawfulMemForInId ρ α]
    [Std.Internal.PureForIn' m ρ α] [Std.Internal.PureForIn' n ρ α]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    F (forIn' xs init f) = forIn' xs init fun a h b => F (f a h b) := by
  rw [Std.Internal.PureForIn'.forIn'_eq (m := m) xs init f,
    Std.Internal.PureForIn'.forIn'_eq (m := n) xs init]
  exact map_listForIn' F hpure hbind _ init _

end Cslib
