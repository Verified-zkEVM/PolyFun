/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Comonoid.Tensor

/-!
# Tensor products of state comonoids

The state comonoid `stateComonoid S` on `S y^S` is the contractible groupoid on `S`
(Niu–Spivak Ex 7.19). In `Cat♯`, the state comonoid of `S × T` is the tensor product of the
state comonoids of `S` and `T` (Niu–Spivak Prop 8.79). Both retrofunctors of
`stateProdTensorIso` are the identity on positions and on directions.

A bijection of state sets gives an isomorphism of state comonoids, `stateEquivIso`, through
the very-well-behaved state lens `Lens.State.ofEquiv`. The middle-four interchange of the
tensor of comonoids is `Comonoid.tensorTensorTensorComm`. By
`stateEquivIso_prodProdProdComm`, the state permutation `Equiv.prodProdProdComm` is that
interchange, conjugated by the product isomorphisms.

## Main definitions

* `Lens.State.ofEquiv` — the state lens of a bijection of states.
* `Comonoid.stateEquivIso` — the isomorphism of state comonoids given by a bijection.
* `Comonoid.stateProdTensorIso` — `stateComonoid (S × T) ≅ tensor (stateComonoid S)
  (stateComonoid T)`.
* `Comonoid.tensorTensorTensorComm` — the middle-four interchange of the tensor product of
  comonoids, with the lenses of `Lens.Equiv.tensorTensorTensorComm`.
* `Comonoid.tensorIso` — the tensor product of two isomorphisms of comonoids.

## Main results

* `Comonoid.stateEquivIso_prodProdProdComm` — the permutation `Equiv.prodProdProdComm` of
  states is the middle-four interchange of the tensor.
-/

@[expose] public section

universe u uA uB uA₁ uB₁ uA₂ uB₂

open CategoryTheory

namespace PFunctor

/-! ## The state lens of a bijection -/

namespace Lens.State

variable {σ τ : Type u}

/-- The state lens of a bijection `e`: `get` is `e`, and `put t` replaces the state by
`e.symm t`. -/
def ofEquiv (e : σ ≃ τ) : State σ τ :=
  mk e fun t _ => e.symm t

@[simp] theorem ofEquiv_get (e : σ ≃ τ) (s : σ) : (ofEquiv e).get s = e s := rfl

@[simp] theorem ofEquiv_put (e : σ ≃ τ) (t : τ) (s : σ) : (ofEquiv e).put t s = e.symm t :=
  rfl

instance ofEquiv_isVeryWellBehaved (e : σ ≃ τ) : (ofEquiv e).IsVeryWellBehaved where
  get_put _ _ := e.apply_symm_apply _
  put_get _ := e.symm_apply_apply _
  put_put _ _ _ := rfl

/-- The state lens of `e` followed by that of `e.symm` is the identity state lens. -/
theorem ofEquiv_symm_comp_ofEquiv (e : σ ≃ τ) :
    (ofEquiv e.symm).comp (ofEquiv e) = State.id σ := by
  change ((fun s => e.symm (e s)) ⇆ fun _ d => e.symm (e d) : State σ σ) = Lens.id _
  rw [funext e.symm_apply_apply]
  simp only [Equiv.symm_apply_apply]

end Lens.State

namespace Comonoid

/-! ## Isomorphisms of state comonoids -/

section StateIso

variable {S T : Type u}

/-- The isomorphism of state comonoids given by a bijection of states: the retrofunctors of the
state lenses of the bijection and of its inverse. -/
def stateEquivIso (e : S ≃ T) : stateComonoid S ≅ stateComonoid T where
  hom := Hom.ofStateLens (Lens.State.ofEquiv e)
  inv := Hom.ofStateLens (Lens.State.ofEquiv e.symm)
  hom_inv_id := hom_ext (Lens.State.ofEquiv_symm_comp_ofEquiv e)
  inv_hom_id := hom_ext (Lens.State.ofEquiv_symm_comp_ofEquiv e.symm)

@[simp] theorem stateEquivIso_hom_toLens (e : S ≃ T) :
    (stateEquivIso e).hom.toLens = Lens.State.ofEquiv e := rfl

@[simp] theorem stateEquivIso_inv_toLens (e : S ≃ T) :
    (stateEquivIso e).inv.toLens = Lens.State.ofEquiv e.symm := rfl

end StateIso

/-! ## The state comonoid of a product -/

section ProdTensor

variable (S T : Type u)

/-- The state comonoid of `S × T` is the tensor product of the state comonoids of `S` and `T`
(Niu–Spivak Prop 8.79). Both retrofunctors are the identity on positions and on directions. -/
def stateProdTensorIso :
    stateComonoid (S × T) ≅ tensor (stateComonoid S) (stateComonoid T) where
  hom := { toLens := (fun p => p) ⇆ fun _ d => d, map_counit := rfl, map_comul := rfl }
  inv := { toLens := (fun p => p) ⇆ fun _ d => d, map_counit := rfl, map_comul := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simp] theorem stateProdTensorIso_hom_toLens :
    (stateProdTensorIso S T).hom.toLens = ((fun p => p) ⇆ fun _ d => d) := rfl

@[simp] theorem stateProdTensorIso_inv_toLens :
    (stateProdTensorIso S T).inv.toLens = ((fun p => p) ⇆ fun _ d => d) := rfl

end ProdTensor

/-! ## The middle-four interchange of comonoids -/

/-- The middle-four interchange `(A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D)` of the tensor product
of comonoids, with the lenses of `Lens.Equiv.tensorTensorTensorComm`. -/
def tensorTensorTensorComm (A B C D : Comonoid.{uA, uB}) :
    tensor (tensor A B) (tensor C D) ≅ tensor (tensor A C) (tensor B D) where
  hom :=
    { toLens :=
        (Lens.Equiv.tensorTensorTensorComm A.carrier B.carrier C.carrier D.carrier).toLens
      map_counit := rfl
      map_comul := rfl }
  inv :=
    { toLens :=
        (Lens.Equiv.tensorTensorTensorComm A.carrier B.carrier C.carrier D.carrier).invLens
      map_counit := rfl
      map_comul := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The tensor product of two isomorphisms of comonoids, with the componentwise retrofunctors
`Hom.tensor` in both directions. -/
def tensorIso {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}} (f : C₁ ≅ D₁)
    (g : C₂ ≅ D₂) : tensor C₁ C₂ ≅ tensor D₁ D₂ where
  hom := Hom.tensor f.hom g.hom
  inv := Hom.tensor f.inv g.inv
  hom_inv_id := (Hom.tensor_comp f.hom f.inv g.hom g.inv).symm.trans
    ((congrArg₂ Hom.tensor f.hom_inv_id g.hom_inv_id).trans (Hom.tensor_id _ _))
  inv_hom_id := (Hom.tensor_comp f.inv f.hom g.inv g.hom).symm.trans
    ((congrArg₂ Hom.tensor f.inv_hom_id g.inv_hom_id).trans (Hom.tensor_id _ _))

@[simp] theorem tensorIso_hom {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : C₁ ≅ D₁) (g : C₂ ≅ D₂) : (tensorIso f g).hom = Hom.tensor f.hom g.hom := rfl

@[simp] theorem tensorIso_inv {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : C₁ ≅ D₁) (g : C₂ ≅ D₂) : (tensorIso f g).inv = Hom.tensor f.inv g.inv := rfl

/-- The isomorphism of state comonoids given by the permutation `Equiv.prodProdProdComm` of
states is the middle-four interchange of the tensor, conjugated by the product isomorphisms. -/
theorem stateEquivIso_prodProdProdComm (S₁ T₁ S₂ T₂ : Type u) :
    stateEquivIso (_root_.Equiv.prodProdProdComm S₁ T₁ S₂ T₂) =
      (stateProdTensorIso (S₁ × T₁) (S₂ × T₂) ≪≫
          tensorIso (stateProdTensorIso S₁ T₁) (stateProdTensorIso S₂ T₂)) ≪≫
        tensorTensorTensorComm (stateComonoid S₁) (stateComonoid T₁) (stateComonoid S₂)
          (stateComonoid T₂) ≪≫
        (stateProdTensorIso (S₁ × S₂) (T₁ × T₂) ≪≫
          tensorIso (stateProdTensorIso S₁ S₂) (stateProdTensorIso T₁ T₂)).symm :=
  Iso.ext <| hom_ext rfl

end Comonoid

end PFunctor
