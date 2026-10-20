/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Basic

/-!
# Deprecated polynomial compatibility

Ordinary-import canaries for old-spelling instance search and explicit unfolding.
-/

@[expose] public section

set_option linter.deprecated false

universe uA uB uA₁ uA₂

namespace PFunctor

-- Old-spelling polynomial instance search: finite directions.
example (A : Type uA) (B : Type uB) [Fintype B] :
    (ofConst A B).Fintype := inferInstance

-- Old-spelling polynomial instance search: decidable positions and directions.
example (A : Type uA) (B : Type uB) [DecidableEq A] [DecidableEq B] :
    (ofConst A B).DecidableEq := inferInstance

-- Old-spelling polynomial instance search: inhabited directions.
example (A : Type uA) (B : Type uB) [Inhabited B] :
    (ofConst A B).Inhabited := inferInstance

-- Old-spelling direction instance search at distinct position universes.
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A)
    [Unique (Q.B a)] : Unique ((sum P Q).B (.inr a)) := inferInstance

-- Old explicit unfolding exposes reducible coproduct directions.
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A)
    [Unique (Q.B a)] : Unique ((coprod P Q).B (.inr a)) := by
  unfold coprod
  infer_instance

-- Old binder names on the sum projection equations.
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (sum P Q).A = (P.A ⊕ Q.A) := sum_A (P := P) (Q := Q)

example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (sum P Q).B (.inl a) = P.B a := sum_B_inl (P := P) (Q := Q) (a := a)

example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A) :
    (sum P Q).B (.inr a) = Q.B a := sum_B_inr (P := P) (Q := Q) (a := a)

-- Old projection rewrites on the old constructor spelling.
example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (sum P Q).A = (P.A ⊕ Q.A) := by
  rw [sum_A]

example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (sum P Q).B (.inl a) = P.B a := by
  rw [sum_B_inl]

example (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A) :
    (sum P Q).B (.inr a) = Q.B a := by
  rw [sum_B_inr]

end PFunctor
