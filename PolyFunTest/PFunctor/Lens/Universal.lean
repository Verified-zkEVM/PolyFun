/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Universal
public import PolyFun.PFunctor.Lens.Yoneda

/-!
# Examples for universal properties and lenses into special polynomials

Regression tests for `PFunctor/Lens/Universal.lean` on small concrete polynomials, including a
non-existence result that follows from the hom-isomorphisms: there is no lens `C Bool ⇆ y`.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Universal

open _root_.PFunctor

/-- Positions and directions both `Bool`. -/
abbrev qBool : PFunctor.{0, 0} := Bool y^ Bool

/-- A `Bool`-indexed family: `y` and `qBool`. -/
abbrev fam : Bool → PFunctor.{0, 0} := fun b => if b then qBool else y

/-! ## Indexed sums and products -/

/-- A lens out of the indexed sum is determined by its restrictions. -/
example (l : Lens (sigma fam) qBool) : Lens.sigmaEquiv.symm (Lens.sigmaEquiv l) = l := rfl

example (l : ∀ b, Lens (fam b) qBool) (b : Bool) :
    Lens.sigmaExists l ∘ₗ Lens.sigmaInj b = l b := rfl

/-- The projections out of `pi fam` recover a pairing. -/
example (l : ∀ b, Lens qBool (fam b)) : Lens.piEquiv (Lens.piForall l) = l := rfl

example (x : (pi fam).Obj Nat) :
    (Obj.piEquiv fam Nat).symm (Obj.piEquiv fam Nat x) = x := rfl

example (x : (sigma fam).Obj Nat) :
    (Obj.sigmaEquiv fam Nat).symm (Obj.sigmaEquiv fam Nat x) = x := rfl

/-! ## Binary sums and products -/

example : Obj.sumEquiv qBool y Nat (Obj.mk (Sum.inl true : (qBool + y).A) fun _ => 3) =
    Sum.inl (Obj.mk true fun _ => 3) := rfl

/-- The two factors receive labels from different summands of the direction type. -/
example :
    let x : (qBool * y).Obj Nat :=
      Obj.mk (true, PUnit.unit) (Sum.elim (fun b => if b then 7 else 3) (fun _ => 11))
    ((Obj.prodEquiv qBool y Nat x).1.snd false,
      (Obj.prodEquiv qBool y Nat x).1.snd true,
      (Obj.prodEquiv qBool y Nat x).2.snd PUnit.unit) = (3, 7, 11) := rfl

example (f g : Lens qBool qBool) : Lens.prodEquiv (Lens.prodPair f g) = (f, g) := rfl

example (f g : Lens qBool qBool) : Lens.sumEquiv (Lens.sumPair f g) = (f, g) := rfl

/-! ## Special polynomials -/

/-- A lens out of `linear Bool` picks a position for each boolean. -/
example :
    Lens.fromLinearEquiv
      ((fun b : Bool => !b) ⇆ fun _ _ => PUnit.unit : Lens (linear Bool) qBool)
    = fun b => !b := rfl

/-- The section of `qBool` that answers every position with itself. -/
def diag : Lens qBool (y : PFunctor.{0, 0}) := Lens.sectionEquiv.symm fun a => a

example : Lens.sectionEquiv diag true = true := rfl

/-- Sections are pulled back along lenses. -/
example : Lens.sectionEquiv (diag ∘ₗ ((fun b => !b) ⇆ fun _ d => !d : Lens qBool qBool)) =
    fun a => a := by
  funext a
  cases a <;> rfl

/-- A lens into `Bool y^ Bool` is a position map and a `Bool`-indexed family of sections. -/
example : (Lens.toMonomialEquiv (Lens.id qBool)).1 true = true := rfl

/-- Direction types distinguish the two positions. -/
abbrev dep : PFunctor.{0, 0} := ⟨Bool, fun b => if b then Fin 3 else Fin 2⟩

/-- A lens whose position and direction maps both distinguish branches. -/
def observe : Lens dep (Nat y^ Bool) :=
  (fun b => if b then 7 else 4) ⇆
    fun b => match b with
      | true => fun d => if d then (2 : Fin 3) else (1 : Fin 3)
      | false => fun d => if d then (1 : Fin 2) else (0 : Fin 2)

example : ((Lens.toMonomialEquiv observe).1 true,
    (Lens.toMonomialEquiv observe).1 false) = (7, 4) := rfl

example : ((Lens.toMonomialEquiv observe).2 true true,
    (Lens.toMonomialEquiv observe).2 false true) = ((2 : Fin 3), (1 : Fin 3)) := rfl

example : ((Lens.toMonomialEquiv observe).2 true false,
    (Lens.toMonomialEquiv observe).2 false false) = ((1 : Fin 2), (0 : Fin 2)) := rfl

/-- Each direction of this tensor section depends on the other factor's position. -/
def tensorSection : Lens (dep ⊗ qBool) (y : PFunctor.{0, 0}) :=
  (fun _ => PUnit.unit) ⇆ fun ab _ =>
    (match ab.1 with
      | true => if ab.2 then (2 : Fin 3) else (1 : Fin 3)
      | false => if ab.2 then (1 : Fin 2) else (0 : Fin 2),
      ab.1 != ab.2)

example : ((Lens.sectionTensorEquiv tensorSection).1 true true,
    (Lens.sectionTensorEquiv tensorSection).1 false true) = ((2 : Fin 3), (1 : Fin 3)) := rfl

example : ((Lens.sectionTensorEquiv tensorSection).2 true false,
    (Lens.sectionTensorEquiv tensorSection).2 false false) = (true, false) := rfl

/-! ## Naturality through ordinary imports -/

/-- Flip the selected position and observe a nonconstant predicate on its directions. -/
def select : Lens qBool dep :=
  (fun b => !b) ⇆ fun b => match b with
    | true => fun d => d.val == 1
    | false => fun d => d.val == 1

def flip : Lens qBool qBool := (fun b => !b) ⇆ fun _ d => !d

/-- Both forward-selected positions and both backward maps affect the pulled-back section. -/
example :
    ((Lens.sectionTensorEquiv (tensorSection ∘ₗ (select ⊗ₗ flip))).1 false true,
      (Lens.sectionTensorEquiv (tensorSection ∘ₗ (select ⊗ₗ flip))).2 false false) =
        (true, true) := by
  rw [Lens.sectionTensorEquiv_comp]
  rfl

def linearChoice : Lens (linear Bool : PFunctor.{0, 0}) dep :=
  (fun b => !b) ⇆ fun _ _ => PUnit.unit

example :
    let reindex : Lens (linear Bool : PFunctor.{0, 0}) (linear Bool) :=
      Lens.fromLinearEquiv.symm Bool.not
    (Lens.fromLinearEquiv (linearChoice ∘ₗ reindex) false,
      Lens.fromLinearEquiv (linearChoice ∘ₗ reindex) true) = (false, true) := by
  dsimp only
  rw [Lens.fromLinearEquiv_reindex]
  rfl

/-- Choose distinct nullary positions in a polynomial that also has nonnullary positions. -/
def constChoice : Lens (C Bool : PFunctor.{0, 0}) (C Bool + qBool) :=
  (fun b => Sum.inl (!b)) ⇆ fun _ d => d

example :
    let reindex : Lens (C Bool : PFunctor.{0, 0}) (C Bool) :=
      Lens.fromConstEquiv.symm (fun b => Obj.mk (!b) id)
    ((Lens.fromConstEquiv (constChoice ∘ₗ reindex) false).fst,
      (Lens.fromConstEquiv (constChoice ∘ₗ reindex) true).fst) =
        (Sum.inl false, Sum.inl true) := by
  dsimp only
  rw [Lens.fromConstEquiv_reindex]
  rfl

/-- A family of sections constructed directly from the branch-dependent backward map. -/
def powerChoice : Lens dep (y^Bool : PFunctor.{0, 0}) :=
  (fun _ => PUnit.unit) ⇆ observe.toFunB

example :
    let change : Lens (y^Bool : PFunctor.{0, 0}) (y^Bool : PFunctor.{0, 0}) :=
      Lens.toPurePowerEquiv.symm (fun b _ => !b)
    (Lens.toPurePowerEquiv (change ∘ₗ powerChoice) false true,
      Lens.toPurePowerEquiv (change ∘ₗ powerChoice) true false) =
        ((2 : Fin 3), (0 : Fin 2)) := by
  dsimp only
  rw [Lens.toPurePowerEquiv_comp_purePower]
  rfl

example :
    let reindex : Lens (Nat y^ Bool) (Nat y^ Bool) :=
      Lens.toMonomialEquiv.symm (Nat.succ, fun b _ => b)
    ((Lens.toMonomialEquiv (reindex ∘ₗ observe)).1 false,
      (Lens.toMonomialEquiv (reindex ∘ₗ observe)).1 true,
      (Lens.toMonomialEquiv (reindex ∘ₗ observe)).2 true true) =
        (5, 8, (2 : Fin 3)) := by
  dsimp only
  rw [Lens.toMonomialEquiv_reindex]
  rfl

example :
    let change : Lens (Nat y^ Bool) (Nat y^ Bool) :=
      Lens.toMonomialEquiv.symm (id, fun b _ => !b)
    ((Lens.toMonomialEquiv (change ∘ₗ observe)).1 true,
      (Lens.toMonomialEquiv (change ∘ₗ observe)).2 false true,
      (Lens.toMonomialEquiv (change ∘ₗ observe)).2 true false) =
        (7, (2 : Fin 3), (0 : Fin 2)) := by
  dsimp only
  rw [Lens.toMonomialEquiv_comp_exponent]
  rfl

/-- There is no lens `C Bool ⇆ y`: it would send `true` to an element of `y(0)`, which is
empty because `y`'s only position has a direction. -/
example : IsEmpty (Lens (C Bool : PFunctor.{0, 0}) (y : PFunctor.{0, 0})) := by
  refine ⟨fun l => ?_⟩
  obtain ⟨_, h⟩ := Obj.pemptyEquiv (y : PFunctor.{0, 0}) (Lens.fromConstEquiv l true)
  exact h.false PUnit.unit

end PolyFunTest.PFunctor.Universal
