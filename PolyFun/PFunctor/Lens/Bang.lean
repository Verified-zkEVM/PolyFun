/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Category.Monoidal
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.Data.Multiset.Sum
public import Mathlib.Data.Multiset.Bind

/-!
# The multiset exponential on lenses

The exponential `bang P` of a polynomial functor `P` has the positions of `P` and, at a position
`a`, the finite multisets of directions of `P` at `a` as directions. A lens `bang P ⇆ Q` is a
forward map on positions with a backward map sending a direction of `Q` to a finite multiset of
directions of `P`; this is the shape of a morphism of the Diller–Nahm variant of the Dialectica
category (de Paiva, *The Dialectica categories*, 1991).

On the category of lenses `bang` is a comonad, the of-course modality of linear logic (Girard,
*Linear logic*, Theoret. Comput. Sci. 50, 1987): the counit (dereliction) sends a direction to the
singleton multiset and the comultiplication (digging) sends a multiset of multisets to its sum.
For the parallel product `⊗`, each `bang P` is a commutative comonoid by weakening (the empty
multiset) and contraction (the sum of two multisets), as in Lafont's model of the exponential
(*Logiques, catégories et machines*, thesis, Paris 7, 1988). The functor `bang` sends the
categorical product `*` to the parallel product and the terminal object `1` to the unit `y`; these
are the Seely isomorphisms (Seely, *Linear logic, ∗-autonomous categories and cofree coalgebras*,
Contemp. Math. 92, 1989).

## Main definitions

* `bang` — the exponential;
* `Lens.bangMap`, `Lens.bangCounit`, `Lens.bangComult` — its action on lenses, counit and
  comultiplication;
* `LensCat.bangFunctor`, `LensCat.bangComonad` — the comonad on `LensCat`;
* `Lens.bangWeak`, `Lens.bangContr` — weakening and contraction;
* `Lens.Equiv.seely`, `Lens.Equiv.seelyUnit` — the Seely isomorphisms `bang (P * Q) ≃ₗ bang P ⊗
  bang Q` and `bang 1 ≃ₗ y`.

## Main results

* `Lens.bangMap_id`, `Lens.bangMap_comp`, `Lens.bangCounit_natural`, `Lens.bangComult_natural`,
  `Lens.bangCounit_comult`, `Lens.bangMap_counit_comult`, `Lens.bangComult_coassoc` — the comonad
  laws;
* `Lens.bangContr_weak_left`, `Lens.bangContr_weak_right`, `Lens.bangContr_assoc`,
  `Lens.bangContr_comm` and the instances `ComonObj`, `IsCommComonObj` on `TensorCat.of (bang P)`
  — the commutative comonoid;
* `Lens.Equiv.seely_contr` — contraction is the Seely image of the exponential of the diagonal.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ u

open CategoryTheory

namespace Multiset

variable {α β : Type u}

/-- The sum of a multiset of multisets of multisets is associative. -/
private theorem join_join' (m : Multiset (Multiset (Multiset α))) :
    m.join.join = (m.map Multiset.join).join := by
  induction m using Multiset.induction_on <;>
    simp_all [Multiset.join_cons, Multiset.join_add]

/-- A multiset over a sum is the sum of its left part and its right part. -/
theorem map_filterMap_getLeft_add_getRight (m : Multiset (α ⊕ β)) :
    (m.filterMap Sum.getLeft?).map Sum.inl + (m.filterMap Sum.getRight?).map Sum.inr = m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    cases a <;> simp [Multiset.filterMap_cons, Sum.getLeft?, Sum.getRight?, Multiset.add_cons,
      Multiset.cons_add, ih]

/-- Filtering by the constant `none` gives the empty multiset. -/
private theorem filterMap_const_none (s : Multiset α) :
    s.filterMap (fun _ => (none : Option β)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.filterMap_cons_none, ih]

/-- The left part of a sum of multisets of left and right elements. -/
theorem filterMap_getLeft_map_add (a : Multiset α) (b : Multiset β) :
    (a.map Sum.inl + b.map Sum.inr).filterMap Sum.getLeft? = a := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

/-- The right part of a sum of multisets of left and right elements. -/
theorem filterMap_getRight_map_add (a : Multiset α) (b : Multiset β) :
    (a.map Sum.inl + b.map Sum.inr).filterMap Sum.getRight? = b := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

end Multiset

namespace PFunctor

/-- The multiset exponential: the positions of `P`, and at a position the finite multisets of
directions of `P` at it. -/
abbrev bang (P : PFunctor.{uA, uB}) : PFunctor.{uA, uB} := ⟨P.A, fun a => Multiset (P.B a)⟩

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-! ## The comonad structure -/

/-- The action of the exponential on a lens: the backward map acts on each element of a
multiset. -/
def bangMap (l : Lens P Q) : Lens (bang P) (bang Q) :=
  l.toFunA ⇆ fun a m => m.map (l.toFunB a)

/-- The counit (dereliction): a direction demands itself once. -/
def bangCounit (P : PFunctor.{uA, uB}) : Lens (bang P) P :=
  id ⇆ fun _ d => {d}

/-- The comultiplication (digging): a multiset of multisets demands their sum. -/
def bangComult (P : PFunctor.{uA, uB}) : Lens (bang P) (bang (bang P)) :=
  id ⇆ fun _ m => m.join

/-- The exponential preserves identities. -/
theorem bangMap_id : bangMap (Lens.id P) = Lens.id (bang P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => Multiset.map_id m

/-- The exponential preserves composition. -/
theorem bangMap_comp (m : Lens Q R) (l : Lens P Q) :
    bangMap (m ∘ₗ l) = bangMap m ∘ₗ bangMap l :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun s =>
    (Multiset.map_map (l.toFunB a) (m.toFunB (l.toFunA a)) s).symm

/-- The counit is natural. -/
theorem bangCounit_natural (l : Lens P Q) :
    bangCounit Q ∘ₗ bangMap l = l ∘ₗ bangCounit P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Multiset.map_singleton _ _

/-- The comultiplication is natural. -/
theorem bangComult_natural (l : Lens P Q) :
    bangComult Q ∘ₗ bangMap l = bangMap (bangMap l) ∘ₗ bangComult P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun mm => Multiset.map_join _ mm

/-- Left counit law: the counit at `bang P` after the comultiplication is the identity. -/
theorem bangCounit_comult (P : PFunctor.{uA, uB}) :
    bangCounit (bang P) ∘ₗ bangComult P = Lens.id (bang P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => Multiset.singleton_join m

/-- Right counit law: the exponential of the counit after the comultiplication is the identity. -/
theorem bangMap_counit_comult (P : PFunctor.{uA, uB}) :
    bangMap (bangCounit P) ∘ₗ bangComult P = Lens.id (bang P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m =>
    (Multiset.bind_singleton m fun y => y).trans (Multiset.map_id' m)

/-- Coassociativity of the comultiplication. -/
theorem bangComult_coassoc (P : PFunctor.{uA, uB}) :
    bangComult (bang P) ∘ₗ bangComult P = bangMap (bangComult P) ∘ₗ bangComult P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => Multiset.join_join' m

/-! ## Weakening and contraction -/

/-- Weakening: no direction is demanded. -/
def bangWeak (P : PFunctor.{uA, uB}) : Lens (bang P) y.{uA, uB} :=
  (fun _ => PUnit.unit) ⇆ fun _ _ => 0

/-- Contraction: a position is duplicated, and a pair of multisets demands their sum. -/
def bangContr (P : PFunctor.{uA, uB}) : Lens (bang P) (bang P ⊗ bang P) :=
  (fun a => (a, a)) ⇆ fun _ m => m.1 + m.2

/-- Weakening on the left after contraction is the inverse of the left unitor. -/
theorem bangContr_weak_left (P : PFunctor.{uA, uB}) :
    (bangWeak P ⊗ₗ Lens.id (bang P)) ∘ₗ bangContr P = Lens.Equiv.yTensor.invLens :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => zero_add m.2

/-- Weakening on the right after contraction is the inverse of the right unitor. -/
theorem bangContr_weak_right (P : PFunctor.{uA, uB}) :
    (Lens.id (bang P) ⊗ₗ bangWeak P) ∘ₗ bangContr P = Lens.Equiv.tensorY.invLens :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => add_zero m.1

/-- Contraction is coassociative. -/
theorem bangContr_assoc (P : PFunctor.{uA, uB}) :
    (Lens.id (bang P) ⊗ₗ bangContr P) ∘ₗ bangContr P =
      Lens.Equiv.tensorAssoc.toLens ∘ₗ (bangContr P ⊗ₗ Lens.id (bang P)) ∘ₗ bangContr P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => (add_assoc _ _ _).symm

/-- Contraction is cocommutative. -/
theorem bangContr_comm (P : PFunctor.{uA, uB}) :
    (Lens.Equiv.tensorComm (bang P) (bang P)).toLens ∘ₗ bangContr P = bangContr P :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => add_comm _ _

end Lens

/-! ## The Seely isomorphisms -/

/-- A finite multiset over a sum is a pair of finite multisets. -/
def multisetSumEquiv (α β : Type u) : Multiset (α ⊕ β) ≃ Multiset α × Multiset β where
  toFun m := (m.filterMap Sum.getLeft?, m.filterMap Sum.getRight?)
  invFun st := st.1.disjSum st.2
  left_inv m := Multiset.map_filterMap_getLeft_add_getRight m
  right_inv st :=
    Prod.ext (Multiset.filterMap_getLeft_map_add st.1 st.2)
      (Multiset.filterMap_getRight_map_add st.1 st.2)

namespace Lens.Equiv

/-- The Seely isomorphism: the exponential of a categorical product is the parallel product of
the exponentials (Seely 1989). -/
def seely (P Q : PFunctor.{uA, uB}) : bang (P * Q) ≃ₗ bang P ⊗ bang Q where
  toLens := id ⇆ fun ab st => (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).symm st
  invLens := id ⇆ fun ab m => multisetSumEquiv (P.B ab.1) (Q.B ab.2) m
  left_inv := Lens.ext _ _ (fun _ => rfl) fun ab => funext fun m =>
    (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).symm_apply_apply m
  right_inv := Lens.ext _ _ (fun _ => rfl) fun ab => funext fun st =>
    (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).apply_symm_apply st

/-- The Seely isomorphism at the unit: the exponential of the terminal object is the unit of the
parallel product. -/
def seelyUnit : bang (1 : PFunctor.{uA, uB}) ≃ₗ y.{uA, uB} where
  toLens := (fun _ => PUnit.unit) ⇆ fun _ _ => 0
  invLens := (fun _ => PUnit.unit) ⇆ fun _ _ => PUnit.unit
  left_inv := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ =>
    (Multiset.eq_zero_of_forall_notMem fun x _ => PEmpty.elim x).symm
  right_inv := rfl

/-- Contraction is the Seely image of the exponential of the diagonal. -/
theorem seely_contr (P : PFunctor.{uA, uB}) :
    (seely P P).toLens ∘ₗ Lens.bangMap (Lens.prodPair (Lens.id P) (Lens.id P)) =
      Lens.bangContr P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (m : Multiset (P.B a) × Multiset (P.B a)) => by
    change Multiset.map (Sum.elim id id) (m.1.map Sum.inl + m.2.map Sum.inr) = m.1 + m.2
    simp [Multiset.map_map, Function.comp_def]

end Lens.Equiv

/-! ## The comonad on the category of lenses -/

namespace LensCat

/-- The exponential as an endofunctor of the category of lenses. -/
def bangFunctor : LensCat.{uA, uB} ⥤ LensCat.{uA, uB} where
  obj X := LensCat.of (bang X.toPFunctor)
  map f := Lens.bangMap f
  map_id _ := Lens.bangMap_id
  map_comp f g := Lens.bangMap_comp g f

/-- The exponential as a comonad on the category of lenses. -/
def bangComonad : Comonad LensCat.{uA, uB} where
  toFunctor := bangFunctor
  ε := { app X := Lens.bangCounit X.toPFunctor, naturality _ _ f := Lens.bangCounit_natural f }
  δ := { app X := Lens.bangComult X.toPFunctor, naturality _ _ f := Lens.bangComult_natural f }
  coassoc X := (Lens.bangComult_coassoc X.toPFunctor).symm
  left_counit X := Lens.bangCounit_comult X.toPFunctor
  right_counit X := Lens.bangMap_counit_comult X.toPFunctor

end LensCat

/-! ## The commutative comonoid structure -/

namespace TensorCat

/-- `bang P` is a comonoid for the parallel product, by weakening and contraction. -/
instance instComonObjBang (P : PFunctor.{uA, uB}) : ComonObj (TensorCat.of (bang P)) where
  counit := Lens.bangWeak P
  comul := Lens.bangContr P
  counit_comul := Lens.bangContr_weak_left P
  comul_counit := Lens.bangContr_weak_right P
  comul_assoc := Lens.bangContr_assoc P

/-- The comonoid `bang P` is commutative. -/
instance instIsCommComonObjBang (P : PFunctor.{uA, uB}) :
    IsCommComonObj (TensorCat.of (bang P)) where
  comul_comm := Lens.bangContr_comm P

end TensorCat

end PFunctor
