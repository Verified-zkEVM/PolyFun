/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Yoneda

/-!
# Cancellable lenses

The two sufficient conditions behind Niu–Spivak Props 5.18 and 5.21:

* A lens with injective positions and surjective direction maps cancels on the left
  (`Lens.cancel_left`). It acts injectively on every `P.Obj X`.
* A lens with surjective positions and injective joint fibre maps cancels on the right
  (`Lens.cancel_right`). The joint fibre map `l.fiberJoint b` sends a direction at a target
  position `b` to its images at every source position over `b`.

Both lemmas hold for lenses between polynomials in independent universes. The converses, which
make these conditions characterize the monomorphisms and epimorphisms of `LensCat`, are in
`PolyFun/PFunctor/Category/MonoEpi.lean`.
-/

@[expose] public section

universe v uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- The joint fibre map of a lens at a target position `b` (Niu–Spivak Prop 5.21, p. 150): a
direction at `b` is sent to its image at every source position over `b`. -/
def fiberJoint (l : Lens P Q) (b : Q.A) (d : Q.B b) :
    (a : {a : P.A // l.toFunA a = b}) → P.B a.1 :=
  fun a => l.toFunB a.1 (cast (congrArg Q.B a.2.symm) d)

@[simp] theorem fiberJoint_apply_self (l : Lens P Q) (a : P.A) (d : Q.B (l.toFunA a)) :
    l.fiberJoint (l.toFunA a) d ⟨a, rfl⟩ = l.toFunB a d := rfl

/-- A lens with injective positions and surjective direction maps acts injectively on
objects. -/
theorem mapObj_injective (l : Lens P Q) (hA : Function.Injective l.toFunA)
    (hB : ∀ a, Function.Surjective (l.toFunB a)) {X : Type v} :
    Function.Injective (l.mapObj (α := X)) := by
  intro x y hxy
  cases x using Obj.rec with | mk a k =>
  cases y using Obj.rec with | mk a' k' =>
  obtain ⟨ha, hk⟩ := Obj.mk.inj hxy
  obtain rfl := hA ha
  have : k ∘ l.toFunB a = k' ∘ l.toFunB a := eq_of_heq hk
  rw [(hB a).injective_comp_right this]
  rfl

/-- A lens with injective positions and surjective direction maps cancels on the left
(the sufficient half of Niu–Spivak Prop 5.18). -/
theorem cancel_left (l : Lens P Q) (hA : Function.Injective l.toFunA)
    (hB : ∀ a, Function.Surjective (l.toFunB a)) {R : PFunctor.{uA₃, uB₃}} {g h : Lens R P}
    (H : l ∘ₗ g = l ∘ₗ h) : g = h :=
  equivPiObj.injective <| funext fun r =>
    mapObj_injective l hA hB (congrFun (congrArg equivPiObj H) r)

/-- Two elements of `R.Obj (Q.B b)` are equal if they agree after mapping along every
component of an injective joint fibre map with a nonempty fibre. -/
theorem eq_of_map_fiberJoint {R : PFunctor.{uA₃, uB₃}} (l : Lens P Q) (b : Q.A)
    (hne : Nonempty {a : P.A // l.toFunA a = b}) (hinj : Function.Injective (l.fiberJoint b))
    {x y : R.Obj (Q.B b)}
    (H : ∀ a : {a : P.A // l.toFunA a = b},
      R.map (fun d => l.fiberJoint b d a) x = R.map (fun d => l.fiberJoint b d a) y) :
    x = y := by
  cases x using Obj.rec with | mk r k =>
  cases y using Obj.rec with | mk r' k' =>
  obtain ⟨a₀⟩ := hne
  obtain ⟨hr, -⟩ := Obj.mk.inj (H a₀)
  change r = r' at hr
  subst hr
  have hk : ∀ a, (fun e => l.fiberJoint b (k e) a) = fun e => l.fiberJoint b (k' e) a :=
    fun a => eq_of_heq (Obj.mk.inj (H a)).2
  congr 1
  funext e
  exact hinj (funext fun a => congrFun (hk a) e)

/-- A lens with surjective positions and injective joint fibre maps cancels on the right
(the sufficient half of Niu–Spivak Prop 5.21). -/
theorem cancel_right (l : Lens P Q) (hA : Function.Surjective l.toFunA)
    (hB : ∀ b, Function.Injective (l.fiberJoint b)) {R : PFunctor.{uA₃, uB₃}} {g h : Lens Q R}
    (H : g ∘ₗ l = h ∘ₗ l) : g = h := by
  refine equivPiObj.injective (funext fun b => ?_)
  obtain ⟨a₀, rfl⟩ := hA b
  refine eq_of_map_fiberJoint l _ ⟨⟨a₀, rfl⟩⟩ (hB _) fun ⟨a, ha⟩ => ?_
  generalize l.toFunA a₀ = b at ha ⊢
  subst ha
  exact congrFun (congrArg equivPiObj H) a

/-- With injective positions, an injective joint fibre map makes every direction map
injective: each fibre has exactly one point. -/
theorem injective_toFunB_of_fiberJoint (l : Lens P Q) (hA : Function.Injective l.toFunA)
    (hB : ∀ b, Function.Injective (l.fiberJoint b)) (a : P.A) :
    Function.Injective (l.toFunB a) := by
  intro d d' hdd
  refine hB (l.toFunA a) (funext fun ⟨a', ha'⟩ => ?_)
  obtain rfl := hA ha'
  exact hdd

end Lens
end PFunctor
