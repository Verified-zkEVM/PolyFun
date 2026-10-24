/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Adjunctions
public import PolyFun.PFunctor.Category.Factorization
public import PolyFun.PFunctor.Lens.MonoEpi
public import PolyFun.PFunctor.Lens.Universal

/-!
# Monomorphisms and epimorphisms of lenses

In `LensCat`:

* A lens is a monomorphism exactly when its position map is injective and every direction
  map is surjective (Niu–Spivak Prop 5.18).
* A lens is an epimorphism exactly when its position map is surjective and every joint fibre
  map `Lens.fiberJoint` is injective (Niu–Spivak Prop 5.21). The condition is on the joint
  map out of a target direction set, not on the individual direction maps.

The sufficient halves are `Lens.cancel_left` and `Lens.cancel_right`, which hold across
universes. The necessary halves test against small polynomials of `LensCat.{uA, uB}`:
* `linear PUnit` detects positions for monomorphisms.
* A pure power `y^X`, with `X` a lifted `Prop`, detects directions for monomorphisms.
* A constant `C X` detects positions for epimorphisms.
* `y + 1` detects joint fibres for epimorphisms. It needs no direction where the two test
  lenses agree.

`LensCat` is balanced: a monomorphism that is also an epimorphism is bijective on positions
and on directions, hence an isomorphism. For cartesian lenses, being a monomorphism reduces to
injectivity of positions (`mono_iff_injective_of_isCartesian`).
-/

@[expose] public section

universe uA uB

open CategoryTheory

namespace PFunctor
namespace LensCat

/-- A lens is a monomorphism exactly when its position map is injective and every direction
map is surjective (Niu–Spivak Prop 5.18, p. 149). -/
theorem mono_iff {P Q : LensCat.{uA, uB}} (l : P ⟶ Q) :
    Mono l ↔
      Function.Injective (Lens.toFunA l) ∧ ∀ a, Function.Surjective (Lens.toFunB l a) := by
  refine ⟨fun hl => ⟨?_, ?_⟩, fun ⟨hA, hB⟩ => ⟨fun _ _ H => Lens.cancel_left l hA hB H⟩⟩
  · intro a a' haa
    let Z : LensCat.{uA, uB} := .of (linear PUnit.{uA + 1})
    let g : Z ⟶ P := Lens.fromLinearEquiv.symm fun _ => a
    let h : Z ⟶ P := Lens.fromLinearEquiv.symm fun _ => a'
    have H : g ≫ l = h ≫ l := Lens.fromLinearEquiv.injective (funext fun _ => haa)
    exact congrFun (congrArg Lens.fromLinearEquiv (hl.right_cancellation g h H)) PUnit.unit
  · intro a e
    let Z : LensCat.{uA, uB} := .of (y^(ULift.{uB} Prop))
    let g : Z ⟶ P :=
      Lens.fromPurePowerEquiv.symm (Obj.mk a fun e => ULift.up (∃ d, Lens.toFunB l a d = e))
    let h : Z ⟶ P := Lens.fromPurePowerEquiv.symm (Obj.mk a fun _ => ULift.up True)
    have H : g ≫ l = h ≫ l := by
      refine Lens.fromPurePowerEquiv.injective ?_
      change Obj.mk _ _ = Obj.mk _ _
      congr 1
      funext d
      exact congrArg ULift.up (propext ⟨fun _ => trivial, fun _ => ⟨d, rfl⟩⟩)
    have hk := eq_of_heq (Obj.mk.inj (congrArg Lens.fromPurePowerEquiv
      (hl.right_cancellation g h H))).2
    have he : (∃ d, Lens.toFunB l a d = e) = True := congrArg ULift.down (congrFun hk e)
    exact he ▸ trivial

/-- The position map of an epimorphism is surjective. -/
theorem surjective_toFunA_of_epi {P Q : LensCat.{uA, uB}} (l : P ⟶ Q) [hl : Epi l] :
    Function.Surjective (Lens.toFunA l) := by
  intro b
  let Z : LensCat.{uA, uB} := .of (C (ULift.{uA} Prop))
  let g : Q ⟶ Z := Lens.toConstEquiv.symm fun b => ULift.up (∃ a, Lens.toFunA l a = b)
  let h : Q ⟶ Z := Lens.toConstEquiv.symm fun _ => ULift.up True
  have H : l ≫ g = l ≫ h := by
    refine Lens.toConstEquiv.injective (funext fun a => ?_)
    exact congrArg ULift.up (propext ⟨fun _ => trivial, fun _ => ⟨a, rfl⟩⟩)
  have hb := congrFun (congrArg Lens.toConstEquiv (hl.left_cancellation g h H)) b
  have he : (∃ a, Lens.toFunA l a = b) = True := congrArg ULift.down hb
  exact he ▸ trivial

/-- The joint fibre maps of an epimorphism are injective. -/
theorem injective_fiberJoint_of_epi {P Q : LensCat.{uA, uB}} (l : P ⟶ Q) [hl : Epi l]
    (b : Q.toPFunctor.A) : Function.Injective (Lens.fiberJoint l b) := by
  classical
  intro d d' hdd
  let Z : LensCat.{uA, uB} := .of (y + 1)
  let pick (e : Q.toPFunctor.B b) : Q ⟶ Z := Lens.equivPiObj.symm fun b' =>
    if hb : b' = b then
      Obj.mk (Sum.inl PUnit.unit) fun _ => cast (congrArg Q.toPFunctor.B hb.symm) e
    else Obj.mk (Sum.inr PUnit.unit) PEmpty.elim
  have H : l ≫ pick d = l ≫ pick d' := by
    refine Lens.equivPiObj.injective (funext fun a => ?_)
    change (y + 1 : PFunctor.{uA, uB}).map (Lens.toFunB l a) (Lens.equivPiObj (pick d) _) =
      (y + 1 : PFunctor.{uA, uB}).map (Lens.toFunB l a) (Lens.equivPiObj (pick d') _)
    simp only [pick, Equiv.apply_symm_apply]
    by_cases ha : Lens.toFunA l a = b
    · subst ha
      simp only [dite_true, cast_eq]
      have := congrFun hdd ⟨a, rfl⟩
      simp only [Lens.fiberJoint, cast_eq] at this
      change Obj.mk _ (fun _ => Lens.toFunB l a d) = Obj.mk _ (fun _ => Lens.toFunB l a d')
      rw [this]
      rfl
    · simp only [ha, dite_false]
  have hpick := congrArg (fun g => Lens.equivPiObj g b) (hl.left_cancellation _ _ H)
  simp only [pick, Equiv.apply_symm_apply, dite_true, cast_eq] at hpick
  exact congrFun (eq_of_heq (Obj.mk.inj hpick).2) PUnit.unit

/-- A lens is an epimorphism exactly when its position map is surjective and every joint fibre
map is injective (Niu–Spivak Prop 5.21, p. 150). -/
theorem epi_iff {P Q : LensCat.{uA, uB}} (l : P ⟶ Q) :
    Epi l ↔ Function.Surjective (Lens.toFunA l) ∧ ∀ b, Function.Injective (Lens.fiberJoint l b) :=
  ⟨fun _ => ⟨surjective_toFunA_of_epi l, injective_fiberJoint_of_epi l⟩,
    fun ⟨hA, hB⟩ => ⟨fun _ _ H => Lens.cancel_right l hA hB H⟩⟩

/-- A cartesian lens is a monomorphism exactly when its position map is injective. -/
theorem mono_iff_injective_of_isCartesian {P Q : LensCat.{uA, uB}} (l : P ⟶ Q)
    (hl : Lens.IsCartesian l) : Mono l ↔ Function.Injective (Lens.toFunA l) := by
  rw [mono_iff]
  exact ⟨And.left, fun h => ⟨h, fun a => (hl a).2⟩⟩

/-- `LensCat` is balanced: a lens that is both a monomorphism and an epimorphism is an
isomorphism. -/
instance : Balanced LensCat.{uA, uB} where
  isIso_of_mono_of_epi l _ _ := by
    obtain ⟨hA, hB⟩ := (mono_iff l).1 inferInstance
    obtain ⟨hA', hB'⟩ := (epi_iff l).1 inferInstance
    exact (isIso_iff_isVertical_and_isCartesian l).2
      ⟨⟨hA, hA'⟩, fun a => ⟨Lens.injective_toFunB_of_fiberJoint l hA hB' a, hB a⟩⟩

end LensCat
end PFunctor
