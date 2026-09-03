/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Std.Internal.ForIn

/-!
# Transport of loops along monad morphisms

A monad morphism `F : ∀ {β}, m β → n β` (cslib's `IsMonadHom` predicate) commutes with every
loop combinator that `do`-notation elaborates to. cslib's `IsMonadHom.map_listMapM`,
`map_listForM`, `map_listFoldlM` and their relatives cover the list functions; this module adds
the `forIn'` / `forIn` loops over lists and, through `Std.Internal.PureForIn`, over every
container whose loop is the loop over the list `ForIn.toList` computes (arrays, ranges,
iterators, …).
-/

public section

universe u v w u₁ w₁

namespace Cslib.IsMonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {F : ∀ {β : Type u}, m β → n β} (hf : IsMonadHom m n F)

include hf

/-! ## Lists -/

-- upstream candidate (complements cslib#856, which covers `mapM`, `forM`, and `foldlM`)
theorem map_listForIn' {α : Type u₁} {β : Type u} (l : List α) (init : β)
    (f : (a : α) → a ∈ l → β → m (ForInStep β)) :
    F (forIn' l init f) = forIn' l init fun a h b => F (f a h b) := by
  induction l generalizing init with
  | nil => simp [hf.map_pure]
  | cons a l ih =>
    simp only [List.forIn'_cons, hf.map_bind]
    congr 1
    funext r
    cases r <;> simp [hf.map_pure, ih]

-- upstream candidate
theorem map_listForIn {α : Type u₁} {β : Type u} (l : List α) (init : β)
    (f : α → β → m (ForInStep β)) :
    F (forIn l init f) = forIn l init fun a b => F (f a b) := by
  induction l generalizing init with
  | nil => simp [hf.map_pure]
  | cons a l ih =>
    simp only [List.forIn_cons, hf.map_bind]
    congr 1
    funext r
    cases r <;> simp [hf.map_pure, ih]

/-! ## Containers iterating over a list

`Std.Internal.PureForIn` identifies the containers (arrays, ranges, iterators, …) whose loop is
the loop over the list `ForIn.toList` computes; transport then reduces to the list case. -/

-- upstream candidate
theorem map_forIn_of_pureForIn {ρ : Type w₁} {α : Type u₁} {β : Type u}
    [ForIn m ρ α] [ForIn n ρ α] [ForIn Id ρ α]
    [Std.Internal.PureForIn m ρ α] [Std.Internal.PureForIn n ρ α]
    (xs : ρ) (init : β) (f : α → β → m (ForInStep β)) :
    F (forIn xs init f) = forIn xs init fun a b => F (f a b) := by
  rw [Std.Internal.PureForIn.forIn_eq (m := m) xs init f,
    Std.Internal.PureForIn.forIn_eq (m := n) xs init]
  exact hf.map_listForIn _ init f

-- upstream candidate
theorem map_forIn'_of_pureForIn' {ρ : Type w₁} {α : Type u₁} {β : Type u}
    {d : Membership α ρ} [ForIn' m ρ α d] [ForIn' n ρ α d] [ForIn Id ρ α]
    [Std.Internal.LawfulMemForInId ρ α]
    [Std.Internal.PureForIn' m ρ α] [Std.Internal.PureForIn' n ρ α]
    (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    F (forIn' xs init f) = forIn' xs init fun a h b => F (f a h b) := by
  rw [Std.Internal.PureForIn'.forIn'_eq (m := m) xs init f,
    Std.Internal.PureForIn'.forIn'_eq (m := n) xs init]
  exact hf.map_listForIn' _ init _

end Cslib.IsMonadHom
