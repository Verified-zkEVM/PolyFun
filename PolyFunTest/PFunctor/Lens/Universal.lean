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

example (x : (qBool * y).Obj Nat) :
    (Obj.prodEquiv qBool y Nat).symm (Obj.prodEquiv qBool y Nat x) = x :=
  (Obj.prodEquiv qBool y Nat).symm_apply_apply x

example (f g : Lens qBool qBool) : Lens.prodEquiv (Lens.prodPair f g) = (f, g) := rfl

example (f g : Lens qBool qBool) : Lens.sumEquiv (Lens.sumPair f g) = (f, g) := rfl

/-! ## Special polynomials -/

/-- A lens out of `linear Bool` picks a position for each boolean. -/
example : Lens.linearEquiv (Lens.linearEquiv.symm (fun b : Bool => !b) : Lens (linear Bool) qBool)
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

/-- Sections of `qBool ⊗ qBool` split into two families of sections. -/
example : (Lens.sectionTensorEquiv
    (Lens.sectionTensorEquiv.symm ((fun _ a => a), (fun _ b => !b)) :
      Lens (qBool ⊗ qBool) (y : PFunctor.{0, 0}))).2 true false = true := rfl

/-- There is no lens `C Bool ⇆ y`: it would send `true` to an element of `y(0)`, which is
empty because `y`'s only position has a direction. -/
example : IsEmpty (Lens (C Bool : PFunctor.{0, 0}) (y : PFunctor.{0, 0})) := by
  refine ⟨fun l => ?_⟩
  obtain ⟨_, h⟩ := Obj.pemptyEquiv (y : PFunctor.{0, 0}) (Lens.constEquiv l true)
  exact h.false PUnit.unit

end PolyFunTest.PFunctor.Universal
