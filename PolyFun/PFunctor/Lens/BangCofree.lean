/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.Bang
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Ext

/-!
# Comonoids for the parallel product and the cofreeness of `bang`

A comonoid for the parallel product `⊗` in the category of lenses is a family of monoids on the
directions. The comultiplication `Q ⇆ Q ⊗ Q` has the diagonal as forward map, by the counit laws,
so its backward map is a binary operation on the directions at each position; the backward map of
the counit `Q ⇆ y` chooses a direction at each position, and the comonoid laws are the monoid
laws. The comonoid is commutative exactly when every monoid is.

The exponential `bang P` with its counit (dereliction) is the cofree commutative `⊗`-comonoid on
`P`: a lens `f : Q ⇆ P` out of a commutative comonoid `Q` factors uniquely through the counit by a
comonoid morphism `Q ⇆ bang P`, whose backward map sends a multiset of directions of `P` to the
sum of their images under `f`. This is Lafont's characterisation of the exponential of linear
logic as the cofree commutative comonoid (Lafont, *Logiques, catégories et machines*, thesis,
Paris 7, 1988).

## Main definitions

* `TensorCat.comonAdd`, `TensorCat.comonZero` — the operation and unit on the directions of a
  `⊗`-comonoid;
* `TensorCat.comonAddMonoid`, `TensorCat.comonAddCommMonoid` — the monoids they form;
* `TensorCat.comonObjOfAddMonoid` — the `⊗`-comonoid of a family of monoids on the directions;
* `TensorCat.comonObjEquiv` — `⊗`-comonoid structures on `Q` are families of monoids on the
  directions of `Q`;
* `TensorCat.bangLift` — the comonoid morphism into `bang P` induced by a lens into `P`.

## Main results

* `TensorCat.comul_toFunA` — the comultiplication of a `⊗`-comonoid is the diagonal on positions;
* `TensorCat.isCommComonObj_iff` — the comonoid is commutative iff each monoid is commutative;
* `TensorCat.isComonHom_bangMap` — the exponential of a lens is a comonoid morphism;
* `TensorCat.bangCounit_comp_bangLift`, `TensorCat.isComonHom_bangLift`,
  `TensorCat.eq_bangLift`, `TensorCat.bang_cofree` — the cofree commutative comonoid.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂

open CategoryTheory

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}

/-- Equal lenses have equal backward maps, after transport along the equality of their forward
maps. -/
theorem toFunB_congr {l₁ l₂ : Lens P R} (h : l₁ = l₂) (a : P.A) (b : R.B (l₁.toFunA a)) :
    l₁.toFunB a b =
      l₂.toFunB a (cast (congrArg (fun l : Lens P R => R.B (l.toFunA a)) h) b) := by
  subst h
  rfl

/-- A lens whose forward map agrees pointwise with `f` is the lens with forward map `f` and its
own backward map, transported along that agreement. -/
theorem eq_mk_of_toFunA (l : Lens P R) {f : P.A → R.A} (h : ∀ a, l.toFunA a = f a) :
    l = (f ⇆ fun a b => l.toFunB a (cast (congrArg R.B (h a)).symm b)) := by
  obtain ⟨lA, lB⟩ := l
  obtain rfl : lA = f := funext h
  rfl

end Lens

namespace TensorCat

/-! ## A `⊗`-comonoid is a family of monoids on the directions -/

section Comonoid

variable {Q : PFunctor.{uA, uB}} [ComonObj (TensorCat.of Q)]

/-- The forward map of the comultiplication of a `⊗`-comonoid is the diagonal. -/
theorem comul_toFunA (q : Q.A) :
    (ComonObj.comul (X := TensorCat.of Q) : Lens Q (Q ⊗ Q)).toFunA q = (q, q) := by
  have h₁ := congrArg (fun l : Lens Q (y ⊗ Q) => (l.toFunA q).2)
    (ComonObj.counit_comul (TensorCat.of Q))
  have h₂ := congrArg (fun l : Lens Q (Q ⊗ y) => (l.toFunA q).1)
    (ComonObj.comul_counit (TensorCat.of Q))
  exact Prod.ext h₂ h₁

/-- The binary operation on the directions at `q` given by the backward map of the
comultiplication. -/
def comonAdd (q : Q.A) (a b : Q.B q) : Q.B q :=
  (ComonObj.comul (X := TensorCat.of Q) : Lens Q (Q ⊗ Q)).toFunB q
    (cast (congrArg (Q ⊗ Q).B (comul_toFunA q)).symm (a, b))

/-- The direction at `q` given by the backward map of the counit. -/
def comonZero (q : Q.A) : Q.B q :=
  (ComonObj.counit (X := TensorCat.of Q) : Lens Q y).toFunB q PUnit.unit

/-- The comultiplication is the diagonal on positions and `comonAdd` on directions. -/
theorem comul_eq : (ComonObj.comul (X := TensorCat.of Q) : Lens Q (Q ⊗ Q)) =
    ((fun q => (q, q)) ⇆ fun q (b : Q.B q × Q.B q) => comonAdd q b.1 b.2) :=
  Lens.eq_mk_of_toFunA _ comul_toFunA

/-- The counit is the unique map on positions and `comonZero` on directions. -/
theorem counit_eq : (ComonObj.counit (X := TensorCat.of Q) : Lens Q y) =
    ((fun _ => PUnit.unit) ⇆ fun q _ => comonZero q) :=
  rfl

/-- `comonZero` is a left unit for `comonAdd`. -/
theorem comonZero_add (q : Q.A) (b : Q.B q) : comonAdd q (comonZero q) b = b := by
  have h := ComonObj.counit_comul (TensorCat.of Q)
  rw [comul_eq] at h
  exact Lens.toFunB_congr h q (PUnit.unit, b)

/-- `comonZero` is a right unit for `comonAdd`. -/
theorem comonAdd_zero (q : Q.A) (b : Q.B q) : comonAdd q b (comonZero q) = b := by
  have h := ComonObj.comul_counit (TensorCat.of Q)
  rw [comul_eq] at h
  exact Lens.toFunB_congr h q (b, PUnit.unit)

/-- `comonAdd` is associative. -/
theorem comonAdd_assoc (q : Q.A) (a b c : Q.B q) :
    comonAdd q (comonAdd q a b) c = comonAdd q a (comonAdd q b c) := by
  have h := ComonObj.comul_assoc (TensorCat.of Q)
  rw [comul_eq] at h
  exact (Lens.toFunB_congr h q (a, (b, c))).symm

/-- The additive monoid on the directions at `q` of a `⊗`-comonoid. -/
abbrev comonAddMonoid (q : Q.A) : AddMonoid (Q.B q) :=
  letI : Add (Q.B q) := ⟨comonAdd q⟩
  letI : Zero (Q.B q) := ⟨comonZero q⟩
  { add_assoc := comonAdd_assoc q
    zero_add := comonZero_add q
    add_zero := comonAdd_zero q
    nsmul := nsmulRec }

/-- A `⊗`-comonoid is commutative iff `comonAdd` is commutative at every position. -/
theorem isCommComonObj_iff :
    Nonempty (IsCommComonObj (TensorCat.of Q)) ↔
      ∀ q (a b : Q.B q), comonAdd q a b = comonAdd q b a := by
  constructor
  · rintro ⟨hc⟩ q a b
    have h := hc.comul_comm
    rw [comul_eq] at h
    exact Lens.toFunB_congr h q (b, a)
  · intro hc
    refine ⟨⟨?_⟩⟩
    rw [comul_eq]
    exact Lens.ext _ _ (fun _ => rfl) fun q => funext fun b => hc q b.2 b.1

/-- `comonAdd` of a commutative `⊗`-comonoid is commutative. -/
theorem comonAdd_comm [IsCommComonObj (TensorCat.of Q)] (q : Q.A) (a b : Q.B q) :
    comonAdd q a b = comonAdd q b a :=
  isCommComonObj_iff.mp ⟨inferInstance⟩ q a b

/-- The commutative additive monoid on the directions at `q` of a commutative `⊗`-comonoid. -/
abbrev comonAddCommMonoid [IsCommComonObj (TensorCat.of Q)] (q : Q.A) : AddCommMonoid (Q.B q) :=
  { comonAddMonoid q with add_comm := comonAdd_comm q }

end Comonoid

section OfAddMonoid

variable {Q : PFunctor.{uA, uB}}

/-- The `⊗`-comonoid of a family of additive monoids on the directions: the counit chooses the
zero and the comultiplication duplicates a position and adds two directions. -/
abbrev comonObjOfAddMonoid (m : (q : Q.A) → AddMonoid (Q.B q)) : ComonObj (TensorCat.of Q) where
  counit := (fun _ => PUnit.unit) ⇆ fun q _ => (m q).zero
  comul := (fun q => (q, q)) ⇆ fun q b => (m q).add b.1 b.2
  counit_comul := Lens.ext _ _ (fun _ => rfl) fun q => funext fun b => (m q).zero_add b.2
  comul_counit := Lens.ext _ _ (fun _ => rfl) fun q => funext fun b => (m q).add_zero b.1
  comul_assoc := Lens.ext _ _ (fun _ => rfl) fun q => funext fun b =>
    ((m q).add_assoc b.1 b.2.1 b.2.2).symm

/-- Two `⊗`-comonoid structures with the same counit and comultiplication are equal. -/
theorem comonObj_ext {c₁ c₂ : ComonObj (TensorCat.of Q)}
    (h₁ : @ComonObj.counit _ _ _ _ c₁ = @ComonObj.counit _ _ _ _ c₂)
    (h₂ : @ComonObj.comul _ _ _ _ c₁ = @ComonObj.comul _ _ _ _ c₂) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases h₁
  cases h₂
  rfl

/-- `⊗`-comonoid structures on `Q` are families of additive monoid structures on the directions
of `Q`. -/
def comonObjEquiv : ComonObj (TensorCat.of Q) ≃ ((q : Q.A) → AddMonoid (Q.B q)) where
  toFun c := @comonAddMonoid Q c
  invFun m := comonObjOfAddMonoid m
  left_inv c := comonObj_ext (@counit_eq Q c).symm (@comul_eq Q c).symm
  right_inv _ := funext fun _ => AddMonoid.ext (funext fun _ => funext fun _ => rfl)

end OfAddMonoid

/-! ## `bang P` is the cofree commutative `⊗`-comonoid -/

/-- The exponential of a lens is a comonoid morphism. -/
instance isComonHom_bangMap {P R : PFunctor.{uA, uB}} (l : Lens R P) :
    IsComonHom (M := TensorCat.of (bang R)) (N := TensorCat.of (bang P)) (Lens.bangMap l) where
  hom_counit := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => rfl
  hom_comul := Lens.ext _ _ (fun _ => rfl) fun a => funext fun m =>
    Multiset.map_add (l.toFunB a) m.1 m.2

section Cofree

variable {P Q : PFunctor.{uA, uB}} [ComonObj (TensorCat.of Q)] [IsCommComonObj (TensorCat.of Q)]

/-- The lens into `bang P` induced by a lens `f` into `P`: a multiset of directions of `P` demands
the sum, in the commutative monoid of the comonoid `Q`, of the images of its elements under `f`. -/
def bangLift (f : Lens Q P) : Lens Q (bang P) :=
  f.toFunA ⇆ fun q m => letI := comonAddCommMonoid q; (m.map (f.toFunB q)).sum

/-- The induced lens followed by the counit of `bang P` is the given lens. -/
theorem bangCounit_comp_bangLift (f : Lens Q P) : Lens.bangCounit P ∘ₗ bangLift f = f :=
  Lens.ext _ _ (fun _ => rfl) fun q => funext fun d => by
    let _ := comonAddCommMonoid q
    exact Multiset.sum_singleton (f.toFunB q d)

/-- The induced lens is a comonoid morphism. -/
instance isComonHom_bangLift (f : Lens Q P) :
    IsComonHom (M := TensorCat.of Q) (N := TensorCat.of (bang P)) (bangLift f) where
  hom_counit := Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => rfl
  hom_comul := by
    rw [comul_eq (Q := Q)]
    refine Lens.ext _ _ (fun _ => rfl) fun q => funext fun b => ?_
    let _ := comonAddCommMonoid q
    exact (congrArg Multiset.sum (Multiset.map_add (f.toFunB q) b.1 b.2)).trans
      (Multiset.sum_add _ _)

/-- A comonoid morphism into `bang P` is the induced lens of its composite with the counit. -/
theorem eq_bangLift (f : Lens Q P) (g : Lens Q (bang P))
    [IsComonHom (M := TensorCat.of Q) (N := TensorCat.of (bang P)) g]
    (h : Lens.bangCounit P ∘ₗ g = f) : g = bangLift f := by
  subst h
  have h₀ : ∀ q, g.toFunB q 0 = comonZero q := fun q =>
    Lens.toFunB_congr (IsComonHom.hom_counit (M := TensorCat.of Q)
      (N := TensorCat.of (bang P)) g) q PUnit.unit
  have hadd : ∀ q (m₁ m₂ : Multiset (P.B (g.toFunA q))),
      g.toFunB q (m₁ + m₂) = comonAdd q (g.toFunB q m₁) (g.toFunB q m₂) := by
    intro q m₁ m₂
    have h := IsComonHom.hom_comul (M := TensorCat.of Q) (N := TensorCat.of (bang P)) g
    rw [comul_eq (Q := Q)] at h
    exact Lens.toFunB_congr h q (m₁, m₂)
  refine Lens.ext _ _ (fun _ => rfl) fun q => funext fun m => ?_
  let _ := comonAddCommMonoid q
  change g.toFunB q m = (m.map fun d => g.toFunB q {d}).sum
  induction m using Multiset.induction_on with
  | empty => exact h₀ q
  | cons d m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih, ← Multiset.singleton_add]
    exact hadd q {d} m

/-- `bang P` with its counit is the cofree commutative `⊗`-comonoid on `P` (Lafont 1988): every
lens `f : Q ⇆ P` out of a commutative comonoid factors through the counit by a unique comonoid
morphism `Q ⇆ bang P`. -/
theorem bang_cofree (f : Lens Q P) :
    ∃! g : Lens Q (bang P),
      IsComonHom (M := TensorCat.of Q) (N := TensorCat.of (bang P)) g ∧
        Lens.bangCounit P ∘ₗ g = f :=
  ⟨bangLift f, ⟨isComonHom_bangLift f, bangCounit_comp_bangLift f⟩,
    fun g ⟨_, hg⟩ => eq_bangLift f g hg⟩

end Cofree

end TensorCat

end PFunctor
