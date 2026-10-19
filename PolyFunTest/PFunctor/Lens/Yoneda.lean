/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Yoneda
public import PolyFun.PFunctor.Equiv.Special

/-!
# Examples for Yoneda, lenses as natural transformations, and special classes

Regression tests for `PFunctor/Lens/Yoneda.lean` and `PFunctor/Equiv/Special.lean` on small
concrete polynomials. The positive class examples come with negative ones, so a
characterization that accepted every polynomial would fail here.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Yoneda

open _root_.PFunctor

/-- Positions and directions both `Bool`. -/
abbrev qBool : PFunctor.{0, 0} := Bool y^ Bool

/-- A lens `qBool ⇆ qBool` that negates positions and returns the direction unchanged. -/
def negLens : Lens qBool qBool := (fun b => !b) ⇆ fun _ d => d

/-! ## The action, `p(1)` and `p(0)` -/

example : Obj.punitEquiv qBool (Obj.mk true fun _ => PUnit.unit) = true := rfl
example : (Obj.punitEquiv.{0} qBool).symm false = Obj.mk false fun _ => PUnit.unit := rfl

/-- `(C Bool + y)(0)` keeps exactly the two constant positions. -/
example : Nonempty ((C Bool + y : PFunctor.{0, 0}).Obj PEmpty ≃ Bool) :=
  ⟨(Obj.pemptyEquiv _).trans
    { toFun := fun a => match a with
        | ⟨.inl b, _⟩ => b
        | ⟨.inr _, h⟩ => (h.false PUnit.unit).elim
      invFun := fun b => ⟨.inl b, inferInstanceAs (IsEmpty PEmpty)⟩
      left_inv := fun a => match a with
        | ⟨.inl _, _⟩ => rfl
        | ⟨.inr _, h⟩ => (h.false PUnit.unit).elim
      right_inv := fun _ => rfl }⟩

/-! ## Representable maps and Yoneda -/

/-- `Lens.purePowerMap` pulls directions back along the function. -/
example : (Lens.purePowerMap (fun n : Fin 2 => decide (n = 1)) :
    Lens (y^Bool : PFunctor.{0, 0}) (y^(Fin 2))).toFunB PUnit.unit 1 = true := rfl

/-- The Yoneda bijection sends a lens out of `y^Bool` to its image of the generic element. -/
example : Lens.purePowerEquiv (negLens ∘ₗ ((fun _ => true) ⇆ fun _ d => !d :
    Lens (y^Bool : PFunctor.{0, 0}) qBool)) = Obj.mk false fun d => !d := rfl

example (l : Lens (y^Bool : PFunctor.{0, 0}) qBool) :
    Lens.purePowerEquiv.symm (Lens.purePowerEquiv l) = l := rfl

/-- `equivPiObj` reads off the forward and backward maps at each position. -/
example : Lens.equivPiObj negLens true = Obj.mk false id := rfl

/-! ## Lenses as natural transformations -/

/-- The natural transformation on `y^Bool` that precomposes with negation. -/
def negNat : ObjHom (y^Bool : PFunctor.{0, 0}) (y^Bool) where
  app _ x := Obj.mk PUnit.unit (x.snd ∘ fun d => !d)
  naturality _ _ := rfl

/-- Its lens negates directions. -/
example : negNat.toLens.toFunB PUnit.unit true = false := rfl

/-- Converting a lens to a natural transformation and back is the identity. -/
example : Lens.objHomEquiv.symm (Lens.objHomEquiv negLens) = negLens := rfl

/-- Converting a natural transformation to a lens and back is the identity. -/
example : Lens.objHomEquiv negNat.toLens = negNat :=
  Lens.objHomEquiv.apply_symm_apply negNat

example : (negLens ∘ₗ negLens).toObjHom = negLens.toObjHom.comp negLens.toObjHom := rfl

/-! ## The normal form -/

example : (Equiv.sigmaPurePower qBool).equivA (sigma.mk true PUnit.unit) = true := rfl
example : (Equiv.sigmaPurePower qBool).equivA.symm false = sigma.mk false PUnit.unit := rfl

/-! ## Special classes, with counterexamples -/

example : IsRepresentable (y^Bool : PFunctor.{0, 0}) := isRepresentable_purePower Bool
example : IsConstant (C Bool : PFunctor.{0, 0}) := isConstant_C Bool
example : IsLinear (linear Bool : PFunctor.{0, 0}) := isLinear_linear Bool
example : IsMonomial qBool := isMonomial_monomial Bool Bool

/-- `Bool y^ Bool` has two positions, so it is not representable. -/
example : ¬ IsRepresentable qBool := by
  rw [isRepresentable_iff]
  rintro ⟨u⟩
  exact Bool.noConfusion (u.uniq true ▸ (u.uniq false).symm : true = false)

/-- `Bool y^ Bool` has directions, so it is not constant. -/
example : ¬ IsConstant qBool := by
  rw [isConstant_iff]
  intro h
  exact (h true).false true

/-- `y + 1` has one position with one direction and one with none, so it is not a monomial. -/
example : ¬ IsMonomial (y + 1 : PFunctor.{0, 0}) := by
  rw [isMonomial_iff]
  rintro ⟨A, h⟩
  obtain ⟨e₁⟩ := h (.inl PUnit.unit)
  obtain ⟨e₂⟩ := h (.inr PUnit.unit)
  exact (e₂.symm (e₁ PUnit.unit)).elim

/-- A representable polynomial is a monomial. -/
example : IsMonomial (y^Bool : PFunctor.{0, 0}) := (isRepresentable_purePower Bool).isMonomial

end PolyFunTest.PFunctor.Yoneda
