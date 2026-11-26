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

For lists, applying a monad morphism to a `forIn` or `forIn'` loop gives the loop with
the morphism applied to each step. The corresponding laws for `mapM`, `forM`, and `foldlM`
are in `Cslib.Foundations.Control.Monad.IsMonadHom.List`.

The container versions require the loops in both monads to traverse the list computed by
`ForIn.toList`. For `forIn`, this is the `Std.Internal.PureForIn` hypothesis.
The body of `forIn'` also receives a proof that its element belongs to the container.
Transport uses `Std.Internal.PureForIn'` in both monads and `Std.Internal.LawfulMemForInId`
to turn membership in the list into the proof expected by the body.
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

The source and target loops both reduce to list loops over `ForIn.toList xs`, so the list
transport laws apply. -/

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
