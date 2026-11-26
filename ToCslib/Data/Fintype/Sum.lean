/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Fintype.Defs

/-!
# Finite families defined by cases on a sum

A family of types `Sum.rec f g` over `α ⊕ β` is finite at each point when every `f a` and every
`g b` is finite. The instance is stated at the recursor. Instance search therefore finds it at a
point that is not a constructor, for a family written directly with `Sum.rec`, such as the
response or argument types of a coproduct of polynomial functors.
-/

public section

-- upstream candidate: Mathlib's `Mathlib/Data/Fintype/Sum.lean`.

namespace Sum

universe u v w

/-- A family defined by cases on a sum is finite at each point when both of its branches are. -/
instance instFintypeRec {α : Type u} {β : Type v} {f : α → Type w} {g : β → Type w}
    [∀ a, Fintype (f a)] [∀ b, Fintype (g b)] :
    ∀ x : α ⊕ β, Fintype (@Sum.rec α β (fun _ => Type w) f g x)
  | .inl a => inferInstanceAs (Fintype (f a))
  | .inr b => inferInstanceAs (Fintype (g b))

end Sum
