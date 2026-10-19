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
* `Lens.fromPurePowerEquiv`: the Yoneda lemma for polynomials, `Lens (y^S) Q ≃ Q.Obj S`
  (Lemma 1.10, p. 5, and Ex 3.2), natural in `S` and `Q`.
* `Lens.equivPiObj`: a lens `P ⇆ Q` is a choice of an element of `Q.Obj (P.B a)` for every
  position `a` (Prop 3.6, p. 42).
* `Lens.ofNatural`, `Lens.mapObj_ofNatural` and `Lens.existsUnique_mapObj`: every natural
  transformation `P.Obj ⟹ Q.Obj` is the action `Lens.mapObj` of exactly one lens (Prop 3.44,
  p. 58, and Cor 3.47, p. 59). The action of a lens is natural (`Lens.mapObj_map`) and
  functorial (`Lens.mapObj_id`, `Lens.mapObj_comp`).

`Lens` is the carrier of this data: a natural family of maps arriving from elsewhere is
converted once with `Lens.ofNatural`. Every round trip holds by `rfl` except
`mapObj_ofNatural`, which uses naturality, as it must. Natural families are taken with
components at the source's direction universe, the universe in which the generic element
`Obj.mk a id : P.Obj (P.B a)` lives.
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
def fromPurePowerEquiv {S : Type uB} {Q : PFunctor.{uA₂, uB₂}} :
    Lens (y^S : PFunctor.{uA, uB}) Q ≃ Q.Obj S where
  toFun l := Obj.mk (l.toFunA PUnit.unit) (l.toFunB PUnit.unit)
  invFun x := (fun _ => x.fst) ⇆ fun _ => x.snd
  left_inv _ := rfl
  right_inv _ := rfl
@[deprecated (since := "2026-10-19")] alias purePowerEquiv := fromPurePowerEquiv

/-- The Yoneda bijection is natural in the target polynomial. -/
@[simp] theorem fromPurePowerEquiv_comp {S : Type uB} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} (g : Lens Q R) (l : Lens (y^S : PFunctor.{uA, uB}) Q) :
    fromPurePowerEquiv (g ∘ₗ l) = g.mapObj (fromPurePowerEquiv l) := rfl
@[deprecated (since := "2026-10-19")] alias purePowerEquiv_comp := fromPurePowerEquiv_comp

/-- The Yoneda bijection is natural in the representing set. -/
theorem fromPurePowerEquiv_comp_purePowerMap {R : Type uB₁} {S : Type uB}
    {Q : PFunctor.{uA₂, uB₂}} (l : Lens (y^R : PFunctor.{uA₁, uB₁}) Q) (f : R → S) :
    fromPurePowerEquiv (l ∘ₗ (purePowerMap f : Lens (y^S : PFunctor.{uA, uB}) (y^R))) =
      Q.map f (fromPurePowerEquiv l) := rfl
@[deprecated (since := "2026-10-19")]
alias purePowerEquiv_comp_purePowerMap := fromPurePowerEquiv_comp_purePowerMap

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

/-! ## Lenses as natural transformations -/

namespace Lens

/-- The lens read off from a family of maps `η X : P.Obj X → Q.Obj X`: its value on each generic
element `Obj.mk a id`. When `η` is natural, this is the unique lens whose action is `η`
(`mapObj_ofNatural`, `existsUnique_mapObj`; Niu–Spivak Cor 3.47). -/
def ofNatural {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (η : ∀ X : Type uB₁, P.Obj X → Q.Obj X) : Lens P Q :=
  (fun a => (η (P.B a) (Obj.mk a id)).fst) ⇆ fun a => (η (P.B a) (Obj.mk a id)).snd

/-- A lens is recovered from its action. -/
@[simp] theorem ofNatural_mapObj {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (l : Lens P Q) : ofNatural (fun _ => l.mapObj) = l := rfl

/-- A natural family of maps is the action of the lens read off from it: naturality at `x.snd`
moves `x` to the generic element at `x.fst`. -/
theorem mapObj_ofNatural {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (η : ∀ X : Type uB₁, P.Obj X → Q.Obj X)
    (hη : ∀ {X Y : Type uB₁} (h : X → Y) (x : P.Obj X), η Y (P.map h x) = Q.map h (η X x))
    {X : Type uB₁} (x : P.Obj X) : (ofNatural η).mapObj x = η X x := by
  induction x using Obj.rec with
  | mk a f =>
    have h := hη f (Obj.mk a id)
    simp only [PFunctor.map_eq, Function.comp_id] at h
    rw [h]
    rfl

/-- **Lenses are natural transformations** (Niu–Spivak Prop 3.44, Cor 3.47): every natural family
of maps `P.Obj X → Q.Obj X` is the action of exactly one lens `P ⇆ Q`. -/
theorem existsUnique_mapObj {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (η : ∀ X : Type uB₁, P.Obj X → Q.Obj X)
    (hη : ∀ {X Y : Type uB₁} (h : X → Y) (x : P.Obj X), η Y (P.map h x) = Q.map h (η X x)) :
    ∃! l : Lens P Q, ∀ (X : Type uB₁) (x : P.Obj X), l.mapObj x = η X x :=
  ⟨ofNatural η, fun _ x => mapObj_ofNatural η hη x,
    fun _ hl => ext_mapObj _ _ fun _ => (hl _ _).trans (mapObj_ofNatural η hη _).symm⟩

end Lens

end PFunctor
