/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Coherence of the parallel and composition products

The parallel product `⊗` with unit `y` is a symmetric monoidal structure on lenses (Niu–Spivak
§3.10, p. 65), and the composition product `◃` with unit `y` is a monoidal structure
(Niu–Spivak §6.1–§6.3, pp. 177–213). This file states the coherence laws for the structural
lenses of `Lens/Basic.lean` at independent universes:

* for `⊗`: `tensorAssoc_pentagon`, `tensor_triangle`, `tensorComm_natural`, `tensorComm_symm`,
  `tensorComm_hexagon`, and `tensorComm_hexagon_reverse`;
* for `◃`: `compAssoc_natural`, `compY_natural`, `yComp_natural`, `compAssoc_pentagon`, and
  `comp_triangle`.

The naturality of the `⊗` associator and unitors is in `Lens/Basic.lean`. Every law holds
definitionally. Unitor naturality across universes compares the two copies of `y` along
`unitComparison`.

The composition product of polynomials is the composite of their actions:
`Obj.compEquiv : (P ◃ Q).Obj X ≃ P.Obj (Q.Obj X)` (Prop 6.2, p. 178), and `◃ₗ` acts as the
horizontal composite of natural transformations (`Obj.compEquiv_mapObj_compMap`).
`Lens.Equiv.compCongr` composes lens equivalences, and `Lens.Equiv.compNthAdd` splits a
composition power, `P ◃^ (m + l) ≃ₗ P ◃^ l ◃ P ◃^ m`.
-/

@[expose] public section

universe v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆

namespace PFunctor

namespace Lens

/-! ## The parallel product -/

section Tensor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

/-- Mac Lane's pentagon for the `⊗` associator. -/
theorem tensorAssoc_pentagon :
    (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R ⊗ S)).toLens ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P ⊗ Q) (Q := R) (R := S)).toLens =
      (Lens.id P ⊗ₗ (Lens.Equiv.tensorAssoc (P := Q) (Q := R) (R := S)).toLens) ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P) (Q := Q ⊗ R) (R := S)).toLens ∘ₗ
          ((Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ⊗ₗ Lens.id S) :=
  rfl

/-- The triangle law relating the `⊗` associator and unitors. -/
theorem tensor_triangle :
    (Lens.id P ⊗ₗ (Lens.Equiv.yTensor (P := Q)).toLens) ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P) (Q := y.{uA₃, uB₃}) (R := Q)).toLens =
      (Lens.Equiv.tensorY (P := P)).toLens ⊗ₗ Lens.id Q :=
  rfl

/-- Naturality of the braiding `P ⊗ Q ⇆ Q ⊗ P`. -/
theorem tensorComm_natural {P' : PFunctor.{uA₃, uB₃}} {Q' : PFunctor.{uA₄, uB₄}}
    (f : Lens P P') (g : Lens Q Q') :
    (g ⊗ₗ f) ∘ₗ (Lens.Equiv.tensorComm P Q).toLens =
      (Lens.Equiv.tensorComm P' Q').toLens ∘ₗ (f ⊗ₗ g) :=
  rfl

/-- The braiding is its own inverse: `⊗` is symmetric. -/
theorem tensorComm_symm :
    (Lens.Equiv.tensorComm Q P).toLens ∘ₗ (Lens.Equiv.tensorComm P Q).toLens =
      Lens.id (P ⊗ Q) :=
  rfl

/-- The hexagon law for the braiding of `⊗`. -/
theorem tensorComm_hexagon :
    (Lens.Equiv.tensorAssoc (P := Q) (Q := R) (R := P)).toLens ∘ₗ
        (Lens.Equiv.tensorComm P (Q ⊗ R)).toLens ∘ₗ
          (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens =
      (Lens.id Q ⊗ₗ (Lens.Equiv.tensorComm P R).toLens) ∘ₗ
        (Lens.Equiv.tensorAssoc (P := Q) (Q := P) (R := R)).toLens ∘ₗ
          ((Lens.Equiv.tensorComm P Q).toLens ⊗ₗ Lens.id R) :=
  rfl

/-- The second hexagon law, stated with the inverse associators. -/
theorem tensorComm_hexagon_reverse :
    (Lens.Equiv.tensorAssoc (P := R) (Q := P) (R := Q)).invLens ∘ₗ
        (Lens.Equiv.tensorComm (P ⊗ Q) R).toLens ∘ₗ
          (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).invLens =
      ((Lens.Equiv.tensorComm P R).toLens ⊗ₗ Lens.id Q) ∘ₗ
        (Lens.Equiv.tensorAssoc (P := P) (Q := R) (R := Q)).invLens ∘ₗ
          (Lens.id P ⊗ₗ (Lens.Equiv.tensorComm Q R).toLens) :=
  rfl

end Tensor

/-! ## The composition product -/

section Comp

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

/-- Naturality of the `◃` associator across lenses whose source and target polynomials occupy
six independent universe pairs. -/
theorem compAssoc_natural {P' : PFunctor.{uA₄, uB₄}} {Q' : PFunctor.{uA₅, uB₅}}
    {R' : PFunctor.{uA₆, uB₆}} (f : Lens P P') (g : Lens Q Q') (h : Lens R R') :
    (f ◃ₗ (g ◃ₗ h)) ∘ₗ (Lens.Equiv.compAssoc (P := P) (Q := Q) (R := R)).toLens =
      (Lens.Equiv.compAssoc (P := P') (Q := Q') (R := R')).toLens ∘ₗ ((f ◃ₗ g) ◃ₗ h) :=
  rfl

/-- Naturality of the right `◃` unitor. The unit component is the canonical comparison between
the independently instantiated copies of `y`. -/
theorem compY_natural (f : Lens P Q) :
    f ∘ₗ (Lens.Equiv.compY (P := P)).toLens =
      (Lens.Equiv.compY (P := Q)).toLens ∘ₗ
        (f ◃ₗ (unitComparison : Lens y.{uA₃, uB₃} y.{uA₄, uB₄})) :=
  rfl

/-- Naturality of the left `◃` unitor. -/
theorem yComp_natural (f : Lens P Q) :
    f ∘ₗ (Lens.Equiv.yComp (P := P)).toLens =
      (Lens.Equiv.yComp (P := Q)).toLens ∘ₗ
        ((unitComparison : Lens y.{uA₃, uB₃} y.{uA₄, uB₄}) ◃ₗ f) :=
  rfl

/-- Mac Lane's pentagon for the `◃` associator. -/
theorem compAssoc_pentagon :
    (Lens.Equiv.compAssoc (P := P) (Q := Q) (R := R ◃ S)).toLens ∘ₗ
        (Lens.Equiv.compAssoc (P := P ◃ Q) (Q := R) (R := S)).toLens =
      (Lens.id P ◃ₗ (Lens.Equiv.compAssoc (P := Q) (Q := R) (R := S)).toLens) ∘ₗ
        (Lens.Equiv.compAssoc (P := P) (Q := Q ◃ R) (R := S)).toLens ∘ₗ
          ((Lens.Equiv.compAssoc (P := P) (Q := Q) (R := R)).toLens ◃ₗ Lens.id S) :=
  rfl

/-- The triangle law relating the `◃` associator and unitors. -/
theorem comp_triangle :
    (Lens.id P ◃ₗ (Lens.Equiv.yComp (P := Q)).toLens) ∘ₗ
        (Lens.Equiv.compAssoc (P := P) (Q := y.{uA₃, uB₃}) (R := Q)).toLens =
      (Lens.Equiv.compY (P := P)).toLens ◃ₗ Lens.id Q :=
  rfl

end Comp

/-! ## Composing lens equivalences -/

namespace Equiv

/-- The composition product of two lens equivalences. -/
def compCongr {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (e₁ : P ≃ₗ R) (e₂ : Q ≃ₗ S) : P ◃ Q ≃ₗ R ◃ S where
  toLens := e₁.toLens ◃ₗ e₂.toLens
  invLens := e₁.invLens ◃ₗ e₂.invLens
  left_inv := by rw [← compMap_comp, e₁.left_inv, e₂.left_inv, compMap_id]
  right_inv := by rw [← compMap_comp, e₁.right_inv, e₂.right_inv, compMap_id]

/-- A composition power splits along a sum of exponents:
`P ◃^ (m + l) ≃ₗ P ◃^ l ◃ P ◃^ m`. -/
def compNthAdd (P : PFunctor.{uA, uB}) (m : ℕ) :
    (l : ℕ) → compNth P (m + l) ≃ₗ compNth P l ◃ compNth P m
  | 0 => (Lens.Equiv.yComp (P := compNth P m)).symm
  | l + 1 =>
    (compCongr (Lens.Equiv.refl P) (compNthAdd P m l)).trans
      (Lens.Equiv.compAssoc (P := P) (Q := compNth P l) (R := compNth P m)).symm

end Equiv

end Lens

/-! ## The composition product as a composite of actions -/

namespace Obj

/-- The action of `P ◃ Q` is the composite of the actions (Niu–Spivak Prop 6.2). -/
def compEquiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (X : Type v) :
    (P ◃ Q).Obj X ≃ P.Obj (Q.Obj X) where
  toFun := comp.get P Q
  invFun := comp.mk P Q
  left_inv _ := rfl
  right_inv _ := rfl

/-- The composition product of lenses acts as the horizontal composite of their natural
transformations: first `g` inside, then `f` outside. -/
theorem compEquiv_mapObj_compMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₄}} (f : Lens P R) (g : Lens Q W)
    {X : Type v} (x : (P ◃ Q).Obj X) :
    compEquiv R W X ((f ◃ₗ g).mapObj x) = f.mapObj (P.map g.mapObj (compEquiv P Q X x)) :=
  rfl

end Obj

end PFunctor
