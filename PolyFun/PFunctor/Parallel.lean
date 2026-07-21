/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# One-or-both parallel interfaces

Aberlé's parallel sum permits a call to the left interface, the right
interface, or both interfaces simultaneously.  It is not the coproduct and it
is not the Dirichlet tensor; rather,

```text
P ∥ Q ≃ (P + Q) + (P ⊗ Q).
```

The direct `ParallelChoice` presentation keeps the three operational cases
visible.  The equivalence with the sum/tensor expression and the symmetric
monoidal unit, symmetry, and associator are provided explicitly.  As with
`PFunctor.sum`, the two interfaces share one direction universe; their
position universes remain independent.
-/

@[expose] public section

universe uA uB uA₁ uA₂ uA₃

namespace PFunctor

/-- A choice of a left value, a right value, or both values simultaneously. -/
inductive ParallelChoice (A : Type uA₁) (B : Type uA₂) :
    Type (max uA₁ uA₂) where
  | left (value : A)
  | right (value : B)
  | both (left : A) (right : B)
deriving DecidableEq

namespace ParallelChoice

/-- `ParallelChoice A B` is the direct presentation of
`A + B + (A × B)`. -/
def sumProdEquiv (A : Type uA₁) (B : Type uA₂) :
    ParallelChoice A B ≃ Sum (Sum A B) (A × B) where
  toFun
    | .left a => .inl (.inl a)
    | .right b => .inl (.inr b)
    | .both a b => .inr (a, b)
  invFun
    | .inl (.inl a) => .left a
    | .inl (.inr b) => .right b
    | .inr (a, b) => .both a b
  left_inv
    | .left _ | .right _ | .both _ _ => rfl
  right_inv
    | .inl (.inl _) | .inl (.inr _) | .inr (_, _) => rfl

/-- Symmetry of one-or-both choices. -/
def comm (A : Type uA₁) (B : Type uA₂) :
    ParallelChoice A B ≃ ParallelChoice B A where
  toFun
    | .left a => .right a
    | .right b => .left b
    | .both a b => .both b a
  invFun
    | .left b => .right b
    | .right a => .left a
    | .both b a => .both a b
  left_inv
    | .left _ | .right _ | .both _ _ => rfl
  right_inv
    | .left _ | .right _ | .both _ _ => rfl

/-- Associativity of one-or-both choices.  Both sides encode the seven
nonempty subsets of three components. -/
def assoc (A : Type uA₁) (B : Type uA₂) (C : Type uA₃) :
    ParallelChoice (ParallelChoice A B) C ≃
      ParallelChoice A (ParallelChoice B C) where
  toFun
    | .left (.left a) => .left a
    | .left (.right b) => .right (.left b)
    | .left (.both a b) => .both a (.left b)
    | .right c => .right (.right c)
    | .both (.left a) c => .both a (.right c)
    | .both (.right b) c => .right (.both b c)
    | .both (.both a b) c => .both a (.both b c)
  invFun
    | .left a => .left (.left a)
    | .right (.left b) => .left (.right b)
    | .right (.right c) => .right c
    | .right (.both b c) => .both (.right b) c
    | .both a (.left b) => .left (.both a b)
    | .both a (.right c) => .both (.left a) c
    | .both a (.both b c) => .both (.both a b) c
  left_inv
    | .left (.left _) | .left (.right _) | .left (.both _ _) |
      .right _ | .both (.left _) _ | .both (.right _) _ |
      .both (.both _ _) _ => rfl
  right_inv
    | .left _ | .right (.left _) | .right (.right _) |
      .right (.both _ _) | .both _ (.left _) | .both _ (.right _) |
      .both _ (.both _ _) => rfl

end ParallelChoice

/-- The parallel sum of polynomial interfaces: a position calls the left
interface, the right interface, or both simultaneously; the response type is
respectively the left response, right response, or their product. -/
def parallelSum (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} where
  A := ParallelChoice P.A Q.A
  B
    | .left a => P.B a
    | .right b => Q.B b
    | .both a b => P.B a × Q.B b

@[inherit_doc] scoped[PFunctor] infixr:62 " ∥ " => parallelSum

@[simp]
theorem parallelSum_B_left (P : PFunctor.{uA₁, uB})
    (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (P ∥ Q).B (.left a) = P.B a :=
  rfl

@[simp]
theorem parallelSum_B_right (P : PFunctor.{uA₁, uB})
    (Q : PFunctor.{uA₂, uB}) (b : Q.A) :
    (P ∥ Q).B (.right b) = Q.B b :=
  rfl

@[simp]
theorem parallelSum_B_both (P : PFunctor.{uA₁, uB})
    (Q : PFunctor.{uA₂, uB}) (a : P.A) (b : Q.A) :
    (P ∥ Q).B (.both a b) = (P.B a × Q.B b) :=
  rfl

namespace Equiv

/-- The parallel sum decomposes as the coproduct of the two one-sided cases
and the joint Dirichlet-tensor case. -/
def parallelSumDecomposition
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (P ∥ Q : PFunctor.{max uA₁ uA₂, uB}) ≃ₚ
      ((P + Q) + (P ⊗ Q) : PFunctor.{max uA₁ uA₂, uB}) where
  equivA := ParallelChoice.sumProdEquiv P.A Q.A
  equivB
    | .left _ | .right _ | .both _ _ => _root_.Equiv.refl _

/-- The zero polynomial is the right unit for parallel sum. -/
def parallelSumZero
    (P : PFunctor.{uA₁, uB}) :
    (P ∥ (0 : PFunctor.{uA₂, uB})) ≃ₚ P where
  equivA :=
    { toFun := fun
        | .left a => a
        | .right b => PEmpty.elim b
        | .both _ b => PEmpty.elim b
      invFun := .left
      left_inv := fun
        | .left _ => rfl
        | .right b => PEmpty.elim b
        | .both _ b => PEmpty.elim b
      right_inv := fun _ => rfl }
  equivB
    | .left _ => _root_.Equiv.refl _
    | .right b => PEmpty.elim b
    | .both _ b => PEmpty.elim b

/-- The zero polynomial is the left unit for parallel sum. -/
def zeroParallelSum
    (P : PFunctor.{uA₁, uB}) :
    ((0 : PFunctor.{uA₂, uB}) ∥ P) ≃ₚ P where
  equivA :=
    { toFun := fun
        | .left a => PEmpty.elim a
        | .right b => b
        | .both a _ => PEmpty.elim a
      invFun := .right
      left_inv := fun
        | .left a => PEmpty.elim a
        | .right _ => rfl
        | .both a _ => PEmpty.elim a
      right_inv := fun _ => rfl }
  equivB
    | .left a => PEmpty.elim a
    | .right _ => _root_.Equiv.refl _
    | .both a _ => PEmpty.elim a

/-- Symmetry of parallel sum. -/
def parallelSumComm
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (P ∥ Q) ≃ₚ (Q ∥ P) where
  equivA := ParallelChoice.comm P.A Q.A
  equivB
    | .left _ | .right _ => _root_.Equiv.refl _
    | .both _ _ => _root_.Equiv.prodComm _ _

/-- Associativity of parallel sum. -/
def parallelSumAssoc
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (R : PFunctor.{uA₃, uB}) :
    ((P ∥ Q) ∥ R) ≃ₚ (P ∥ (Q ∥ R)) where
  equivA := ParallelChoice.assoc P.A Q.A R.A
  equivB
    | .left (.left _) | .left (.right _) | .left (.both _ _) |
      .right _ | .both (.left _) _ | .both (.right _) _ =>
        _root_.Equiv.refl _
    | .both (.both _ _) _ => _root_.Equiv.prodAssoc _ _ _

end Equiv
end PFunctor
