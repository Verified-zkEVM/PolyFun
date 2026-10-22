/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Coherence

/-!
# Ordinary-import canaries for monoidal coherence

The coherence laws of the parallel and composition products and the action of `◃` are
definitional. These examples check by `rfl`, through ordinary imports and at independent
universes, that a consumer sees the pentagons, the triangle for `◃`, and the
`Obj.compEquiv` round trip.
-/

@[expose] public section

universe v uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PolyFunTest.ModuleAPI.Lens.Coherence

open _root_.PFunctor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

example :
    (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R ⊗ S)).toLens ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P ⊗ Q) (Q := R) (R := S)).toLens =
      (Lens.id P ⊗ₗ (Lens.Equiv.tensorAssoc (P := Q) (Q := R) (R := S)).toLens) ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P) (Q := Q ⊗ R) (R := S)).toLens ∘ₗ
          ((Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ⊗ₗ Lens.id S) :=
  rfl

example :
    (Lens.Equiv.compAssoc (P := P) (Q := Q) (R := R ◃ S)).toLens ∘ₗ
        (Lens.Equiv.compAssoc (P := P ◃ Q) (Q := R) (R := S)).toLens =
      (Lens.id P ◃ₗ (Lens.Equiv.compAssoc (P := Q) (Q := R) (R := S)).toLens) ∘ₗ
        (Lens.Equiv.compAssoc (P := P) (Q := Q ◃ R) (R := S)).toLens ∘ₗ
          ((Lens.Equiv.compAssoc (P := P) (Q := Q) (R := R)).toLens ◃ₗ Lens.id S) :=
  rfl

example :
    (Lens.id P ◃ₗ (Lens.Equiv.yComp (P := Q)).toLens) ∘ₗ
        (Lens.Equiv.compAssoc (P := P) (Q := y.{uA₃, uB₃}) (R := Q)).toLens =
      (Lens.Equiv.compY (P := P)).toLens ◃ₗ Lens.id Q :=
  rfl

example {X : Type v} (x : (P ◃ Q).Obj X) :
    (Obj.compEquiv P Q X).symm (Obj.compEquiv P Q X x) = x := rfl

end PolyFunTest.ModuleAPI.Lens.Coherence
