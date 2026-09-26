/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Lenses between monomials

A lens `A y^ B ⇆ C y^ D` is a forward map `A → C` on positions together with a backward map
`A → D → B` on directions that may consult the source position. Such lenses transport the
inputs and outputs of an interface: they are the context lenses that lift a proof system from
an inner to an outer statement type, and the wrappers that reinterpret a dynamical system's
inputs and outputs. `Lens.ofMonomial` packages the two maps, `monomialMapFst` changes positions
only, and `monomialMapSnd` changes directions only; every monomial lens factors as one of each
(`ofMonomial_eq_comp`).
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor.Lens

variable {A : Type uA₁} {B : Type uB₁} {C : Type uA₂} {D : Type uB₂} {E : Type uA₃} {F : Type uB₃}

/-- The lens between monomials with forward map `proj` on positions and backward map `lift`
on directions, where `lift` may consult the source position. -/
def ofMonomial (proj : A → C) (lift : A → D → B) : Lens (A y^ B) (C y^ D) :=
  proj ⇆ lift

@[simp] theorem ofMonomial_toFunA (proj : A → C) (lift : A → D → B) (a : A) :
    (ofMonomial proj lift).toFunA a = proj a := rfl

@[simp] theorem ofMonomial_toFunB (proj : A → C) (lift : A → D → B) (a : A) (d : D) :
    (ofMonomial proj lift).toFunB a d = lift a d := rfl

/-- Every lens between monomials is `ofMonomial` of its two components. -/
theorem ofMonomial_eta (l : Lens (A y^ B) (C y^ D)) : ofMonomial l.toFunA l.toFunB = l := rfl

@[simp] theorem ofMonomial_id :
    ofMonomial (fun a : A => a) (fun _ (b : B) => b) = Lens.id (A y^ B) := rfl

@[simp] theorem ofMonomial_comp (proj₂ : C → E) (lift₂ : C → F → D) (proj₁ : A → C)
    (lift₁ : A → D → B) :
    ofMonomial proj₂ lift₂ ∘ₗ ofMonomial proj₁ lift₁ =
      ofMonomial (fun a => proj₂ (proj₁ a)) (fun a f => lift₁ a (lift₂ (proj₁ a) f)) :=
  rfl

/-- Reindex the positions of a monomial, keeping its directions. -/
def monomialMapFst (proj : A → C) : Lens (A y^ B) (C y^ B) :=
  ofMonomial proj fun _ b => b

/-- Translate the directions of a monomial, keeping its positions; the translation may consult
the position. -/
def monomialMapSnd (lift : A → D → B) : Lens (A y^ B) (A y^ D) :=
  ofMonomial (fun a => a) lift

@[simp] theorem monomialMapFst_toFunA (proj : A → C) (a : A) :
    (monomialMapFst (B := B) proj).toFunA a = proj a := rfl

@[simp] theorem monomialMapFst_toFunB (proj : A → C) (a : A) (b : B) :
    (monomialMapFst proj).toFunB a b = b := rfl

@[simp] theorem monomialMapSnd_toFunA (lift : A → D → B) (a : A) :
    (monomialMapSnd lift).toFunA a = a := rfl

@[simp] theorem monomialMapSnd_toFunB (lift : A → D → B) (a : A) (d : D) :
    (monomialMapSnd lift).toFunB a d = lift a d := rfl

/-- A monomial lens is a direction translation followed by a position reindexing. -/
theorem ofMonomial_eq_comp (proj : A → C) (lift : A → D → B) :
    ofMonomial proj lift = monomialMapFst proj ∘ₗ monomialMapSnd lift := rfl

end PFunctor.Lens
