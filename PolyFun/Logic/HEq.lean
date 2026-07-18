/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Heterogeneous equality helper lemmas

This file contains small `HEq` lemmas that belong in Mathlib rather than in
domain-specific developments.
-/

@[expose] public section

universe u v w

namespace PolyFun
namespace Logic

/-- Apply a dependent binary function to equal indices and heterogeneously
equal arguments. -/
theorem dependent_apply_heq
    {A : Sort u} {B : A → Sort v} {C : A → Sort w}
    (function : (a : A) → B a → C a)
    {a a' : A} (ha : a = a') {b : B a} {b' : B a'} (hb : b ≍ b') :
    function a b ≍ function a' b' := by
  subst a'
  cases hb
  rfl

end Logic
end PolyFun

namespace Prod

/-- Build a heterogeneous equality between pairs with the same first component
from a heterogeneous equality between their second components. -/
theorem mk_heq {α : Type u} {β β' : Type v}
    {a : α} {b : β} {b' : β'} (h : b ≍ b') :
    ((a, b) : α × β) ≍ ((a, b') : α × β') := by
  cases h
  rfl

end Prod
