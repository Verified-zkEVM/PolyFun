/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Representables, Yoneda, and lenses as natural transformations

A polynomial `P` acts on a type `X` by `P.Obj X = Σ a, (P.B a → X)` (Niu–Spivak Def 2.1,
p. 25). This file records the elementary facts that identify lenses with natural
transformations between these actions (Niu–Spivak §1.1, §2.1, §3.1–§3.7):

* `Obj.equivSigma`, `Obj.punitEquiv` and `Obj.pemptyEquiv`: the action as a sigma type, and its
  values `p(1) ≅ p.A` (Prop 2.6, p. 27) and `p(0) ≅ {a // p.B a = ∅}`.
* `Lens.purePowerMap`: a function `R → S` induces a lens `y^S ⇆ y^R` (Prop 1.4, p. 4), and the
  assignment is functorial (Ex 1.8).
* `Lens.purePowerEquiv`: the Yoneda lemma for polynomials, `Lens (y^S) Q ≃ Q.Obj S`
  (Lemma 1.10, p. 5, and Ex 3.2), natural in `S` and `Q`.
* `Lens.equivPiObj`: a lens `P ⇆ Q` is a choice of an element of `Q.Obj (P.B a)` for every
  position `a` (Prop 3.6, p. 42).
* `ObjHom` and `Lens.objHomEquiv`: lenses `P ⇆ Q` correspond to natural transformations
  `P.Obj ⟹ Q.Obj` (Prop 3.44, p. 58, and Cor 3.47, p. 59), compatibly with identities and
  composition.

The forward maps send a lens to its action `Lens.mapObj`. Every round trip except
`objHomEquiv`'s right inverse holds by `rfl`; that one uses naturality, as it must.

Natural transformations are taken with components at the source's direction universe, the
universe in which the generic element `Obj.mk a id : P.Obj (P.B a)` lives.
-/

@[expose] public section

universe v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor

/-! ## The action of a polynomial -/

namespace Obj

variable (P : PFunctor.{uA, uB})

/-- The action of a polynomial on `X` is the sigma type `Σ a, (P.B a → X)` (Niu–Spivak
Def 2.1). -/
def equivSigma (X : Type v) : P.Obj X ≃ Σ a, (P.B a → X) where
  toFun x := ⟨x.fst, x.snd⟩
  invFun s := Obj.mk s.1 s.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The positions of a polynomial are its value at the singleton, `p(1) ≅ p.A` (Niu–Spivak
Prop 2.6). -/
def punitEquiv : P.Obj PUnit.{v + 1} ≃ P.A where
  toFun x := x.fst
  invFun a := Obj.mk a fun _ => PUnit.unit
  left_inv _ := rfl
  right_inv _ := rfl

/-- The value of a polynomial at the empty set consists of the positions without directions,
`p(0) ≅ {a // p.B a = ∅}`. -/
def pemptyEquiv : P.Obj PEmpty.{v + 1} ≃ {a : P.A // IsEmpty (P.B a)} where
  toFun x := ⟨x.fst, ⟨fun b => (x.snd b).elim⟩⟩
  invFun a := Obj.mk a.1 fun b => (a.2.false b).elim
  left_inv x := Obj.ext rfl (heq_of_eq (funext fun b => (x.snd b).elim))
  right_inv _ := rfl

@[simp] theorem punitEquiv_apply (x : P.Obj PUnit.{v + 1}) : punitEquiv P x = x.fst := rfl

@[simp] theorem punitEquiv_symm_apply (a : P.A) :
    (punitEquiv.{v} P).symm a = Obj.mk a fun _ => PUnit.unit := rfl

end Obj

namespace Lens

/-! ## Representable maps -/

/-- A function `f : R → S` induces the lens `y^S ⇆ y^R` that pulls each direction back
along `f` (Niu–Spivak Prop 1.4). -/
def purePowerMap {R : Type uB₁} {S : Type uB₂} (f : R → S) :
    Lens (y^S : PFunctor.{uA₁, uB₂}) (y^R : PFunctor.{uA₂, uB₁}) :=
  (fun _ => PUnit.unit) ⇆ fun _ => f

@[simp] theorem purePowerMap_id {S : Type uB} :
    purePowerMap (id : S → S) = Lens.id (y^S : PFunctor.{uA, uB}) := rfl

/-- `f ↦ purePowerMap f` is contravariantly functorial (Niu–Spivak Ex 1.8). -/
@[simp] theorem purePowerMap_comp {R : Type uB₁} {S : Type uB₂} {T : Type uB₃}
    (f : R → S) (g : S → T) :
    (purePowerMap f : Lens (y^S : PFunctor.{uA₂, uB₂}) (y^R : PFunctor.{uA₁, uB₁})) ∘ₗ
        (purePowerMap g : Lens (y^T : PFunctor.{uA₃, uB₃}) (y^S : PFunctor.{uA₂, uB₂})) =
      purePowerMap (g ∘ f) := rfl

/-! ## The Yoneda lemma for polynomials -/

/-- **Yoneda for polynomials** (Niu–Spivak Lemma 1.10, Ex 3.2): a lens out of the
representable `y^S` is an element of `Q.Obj S`. -/
def purePowerEquiv {S : Type uB} {Q : PFunctor.{uA₂, uB₂}} :
    Lens (y^S : PFunctor.{uA, uB}) Q ≃ Q.Obj S where
  toFun l := Obj.mk (l.toFunA PUnit.unit) (l.toFunB PUnit.unit)
  invFun x := (fun _ => x.fst) ⇆ fun _ => x.snd
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Yoneda bijection is natural in the target polynomial. -/
@[simp] theorem purePowerEquiv_comp {S : Type uB} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} (g : Lens Q R) (l : Lens (y^S : PFunctor.{uA, uB}) Q) :
    purePowerEquiv (g ∘ₗ l) = g.mapObj (purePowerEquiv l) := rfl

/-- The Yoneda bijection is natural in the representing set. -/
theorem purePowerEquiv_comp_purePowerMap {R : Type uB₁} {S : Type uB}
    {Q : PFunctor.{uA₂, uB₂}} (l : Lens (y^R : PFunctor.{uA₁, uB₁}) Q) (f : R → S) :
    purePowerEquiv (l ∘ₗ (purePowerMap f : Lens (y^S : PFunctor.{uA, uB}) (y^R))) =
      Q.map f (purePowerEquiv l) := rfl

/-! ## Lenses as families of elements -/

/-- A lens `P ⇆ Q` is a choice, for each position `a` of `P`, of an element of `Q.Obj (P.B a)`
(Niu–Spivak Prop 3.6): the image under the lens of the generic element `Obj.mk a id`. -/
def equivPiObj {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens P Q ≃ ((a : P.A) → Q.Obj (P.B a)) where
  toFun l a := Obj.mk (l.toFunA a) (l.toFunB a)
  invFun g := (fun a => (g a).fst) ⇆ fun a => (g a).snd
  left_inv _ := rfl
  right_inv _ := rfl

/-- `equivPiObj l a` is the action of `l` on the generic element at `a`. -/
theorem equivPiObj_apply {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (a : P.A) : equivPiObj l a = l.mapObj (Obj.mk a id) := rfl

/-- The action of a lens commutes with the actions of `P` and `Q` on functions (Niu–Spivak
Prop 3.44). -/
theorem mapObj_map {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    {X Y : Type v} (h : X → Y) (x : P.Obj X) : l.mapObj (P.map h x) = Q.map h (l.mapObj x) :=
  rfl

end Lens

/-! ## Natural transformations between polynomial functors -/

/-- A **natural transformation** `P.Obj ⟹ Q.Obj` between the actions of two polynomials, with
components at the direction universe of `P`. By `Lens.objHomEquiv` these are exactly the
lenses `P ⇆ Q` (Niu–Spivak Prop 3.44, Cor 3.47). -/
@[ext]
structure ObjHom (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The component at a type `X`. -/
  app : ∀ X : Type uB₁, P.Obj X → Q.Obj X
  /-- Naturality in `X`. -/
  naturality : ∀ {X Y : Type uB₁} (h : X → Y) (x : P.Obj X),
    app Y (P.map h x) = Q.map h (app X x)

namespace ObjHom

/-- The identity natural transformation. -/
protected def id (P : PFunctor.{uA, uB}) : ObjHom P P where
  app _ x := x
  naturality _ _ := rfl

/-- Composition of natural transformations; the middle polynomial shares its direction
universe with the source, where the components of the second transformation live. -/
def comp {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (θ : ObjHom Q R) (η : ObjHom P Q) : ObjHom P R where
  app X x := θ.app X (η.app X x)
  naturality h x := by rw [η.naturality, θ.naturality]

@[simp] theorem id_app (P : PFunctor.{uA, uB}) (X : Type uB) (x : P.Obj X) :
    (ObjHom.id P).app X x = x := rfl

@[simp] theorem comp_app {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} (θ : ObjHom Q R) (η : ObjHom P Q) (X : Type uB) (x : P.Obj X) :
    (θ.comp η).app X x = θ.app X (η.app X x) := rfl

/-- The lens determined by a natural transformation: its value on each generic element
`Obj.mk a id` (Niu–Spivak Cor 3.47). -/
def toLens {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (η : ObjHom P Q) : Lens P Q :=
  (fun a => (η.app (P.B a) (Obj.mk a _root_.id)).fst) ⇆
    fun a => (η.app (P.B a) (Obj.mk a _root_.id)).snd

/-- A natural transformation acts as its lens: naturality at `x.snd` moves `x` to the generic
element at `x.fst`. -/
theorem mapObj_toLens {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (η : ObjHom P Q)
    {X : Type uB₁} (x : P.Obj X) : η.toLens.mapObj x = η.app X x := by
  induction x using Obj.rec with
  | mk a f =>
    have h := η.naturality f (Obj.mk a _root_.id)
    simp only [PFunctor.map_eq, Function.comp_id] at h
    rw [h]
    rfl

end ObjHom

namespace Lens

/-- The natural transformation `P.Obj ⟹ Q.Obj` given by the action of a lens. -/
def toObjHom {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) : ObjHom P Q where
  app _ := l.mapObj
  naturality := l.mapObj_map

@[simp] theorem toObjHom_app {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (X : Type uB₁) (x : P.Obj X) : l.toObjHom.app X x = l.mapObj x := rfl

/-- **Lenses are natural transformations** (Niu–Spivak Prop 3.44, Cor 3.47): sending a lens to
its action is a bijection onto the natural transformations `P.Obj ⟹ Q.Obj`. -/
def objHomEquiv {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Lens P Q ≃ ObjHom P Q where
  toFun := toObjHom
  invFun := ObjHom.toLens
  left_inv _ := rfl
  right_inv η := ObjHom.ext (funext fun _ => funext fun x => η.mapObj_toLens x)

@[simp] theorem objHomEquiv_apply {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (l : Lens P Q) : objHomEquiv l = l.toObjHom := rfl

@[simp] theorem objHomEquiv_symm_apply {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (η : ObjHom P Q) : objHomEquiv.symm η = η.toLens := rfl

@[simp] theorem toObjHom_id (P : PFunctor.{uA, uB}) :
    (Lens.id P).toObjHom = ObjHom.id P := rfl

/-- The correspondence between lenses and natural transformations preserves composition. -/
@[simp] theorem toObjHom_comp {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} (g : Lens Q R) (f : Lens P Q) :
    (g ∘ₗ f).toObjHom = g.toObjHom.comp f.toObjHom := rfl

/-- The lens of a composite natural transformation is the composite lens. -/
theorem toLens_comp {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (θ : ObjHom Q R) (η : ObjHom P Q) : (θ.comp η).toLens = θ.toLens ∘ₗ η.toLens := by
  refine objHomEquiv.injective (ObjHom.ext (funext fun X => funext fun x => ?_))
  simp [ObjHom.mapObj_toLens]

end Lens

end PFunctor
