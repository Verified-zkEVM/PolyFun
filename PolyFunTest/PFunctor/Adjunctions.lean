/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Adjunctions

/-!
# Examples for the trivial-interface hom-set adjunctions

Regression tests exercising the Spivak–Niu §5.1 hom-isomorphisms
`homFromZero`, `homToOne`, `homFromX`, `homToConst`, and `homToLinear` on the
small concrete polynomial `qBool = Bool y^Bool`.
-/

@[expose] public section

universe u pA pB qA qB rA rB

namespace PFunctor

/-- A small concrete polynomial `Bool y^Bool` for the worked examples:
positions and directions are both `Bool`. -/
def qBool : PFunctor.{0, 0} := Bool X^ Bool

/-! ## The equivalences instantiate at the stated types -/

example {p : PFunctor.{u, u}} : Lens (0 : PFunctor.{u, u}) p ≃ PUnit := homFromZero
example {p : PFunctor.{u, u}} : Lens p (1 : PFunctor.{u, u}) ≃ PUnit := homToOne
example {p : PFunctor.{u, u}} : Lens X.{u, u} p ≃ p.A := homFromX
example {p : PFunctor.{u, u}} {A : Type u} : Lens p (C A) ≃ (p.A → A) := homToConst
example {p : PFunctor.{u, u}} {A : Type u} :
    Lens p (linear A) ≃ ((p.A → A) × ((a : p.A) → p.B a)) := homToLinear

/-! ## `0` is initial and `1` is terminal -/

/-- The unique lens out of `0` is sent to the point. -/
example : homFromZero (p := qBool) Lens.initial = PUnit.unit := rfl
/-- The unique lens into `1` is sent to the point. -/
example : homToOne (p := qBool) Lens.terminal = PUnit.unit := rfl
/-- Every lens out of `0` is `Lens.initial` (the uniqueness content of `homFromZero`). -/
example (l : Lens (0 : PFunctor.{0, 0}) qBool) : l = Lens.initial := by
  ext a <;> exact a.elim
/-- Every lens into `1` is `Lens.terminal` (the uniqueness content of `homToOne`). -/
example (l : Lens qBool (1 : PFunctor.{0, 0})) : l = Lens.terminal := by
  ext a d
  · rfl
  · exact d.elim

/-! ## `homFromX`: a lens `y ⇆ p` is a position -/

/-- The forward map reads off the chosen position. -/
example : homFromX (p := qBool) (Lens.fromX true) = true := rfl

/-- The inverse builds the constant-position lens. -/
example :
    (homFromX (p := qBool)).symm false = Lens.fromX false := rfl

/-- Round-trip through a position is the identity. -/
example (a : qBool.A) : homFromX (p := qBool) ((homFromX (p := qBool)).symm a) = a := rfl

/-! ## `homToConst`: a lens `p ⇆ C A` is a position map -/

/-- The forward map is exactly the position map `toFunA`, checked concretely
on `Bool.toNat`. -/
example :
    homToConst (Lens.toConst Bool.toNat : Lens qBool (C Nat)) = Bool.toNat := rfl

/-- The forward map is exactly the position map `toFunA`, for an arbitrary map. -/
example (f : qBool.A → Nat) :
    homToConst (Lens.toConst f : Lens qBool (C Nat)) = f := rfl

/-- The inverse installs the empty backward map. -/
example (f : Bool → Nat) : ((homToConst (p := qBool) (A := Nat)).symm f).toFunA = f := rfl

/-- Round-trip through a position map is the identity. -/
example (f : qBool.A → Nat) :
    homToConst (p := qBool) ((homToConst (p := qBool) (A := Nat)).symm f) = f := rfl

/-! ## `homToLinear`: a lens `p ⇆ A·y` is a position map plus a section -/

/-- The forward map splits into the position map and the chosen section. -/
example (f : qBool.A → Nat) (s : (a : qBool.A) → qBool.B a) :
    homToLinear (Lens.toLinear f s : Lens qBool (linear Nat)) = (f, s) := rfl

/-- The inverse reassembles the position map and section into a lens. -/
example (f : Bool → Nat) (s : (a : qBool.A) → qBool.B a) :
    ((homToLinear (p := qBool) (A := Nat)).symm (f, s)).toFunA = f := rfl

/-- Round-trip through a `(position map, section)` pair is the identity. -/
example (f : qBool.A → Nat) (s : (a : qBool.A) → qBool.B a) :
    homToLinear (p := qBool) ((homToLinear (p := qBool) (A := Nat)).symm (f, s)) = (f, s) := rfl

/-! ## Tensor gluing -/

/-- Canonical tensor restrictions expose their position and direction
projections to `simp` without unfolding the constructors. -/
example {p : PFunctor.{pA, pB}} (a : p.A) (d : p.B a) :
    (Lens.positionCounit p).toFunA a = a ∧
      (Lens.positionCounit p).toFunB a d = PUnit.unit := by
  simp

example {p : PFunctor.{pA, pB}} {q : PFunctor.{qA, qB}}
    {r : PFunctor.{rA, rB}} (l : Lens (p ⊗ q) r) (pq : p.A × q.A)
    (d : r.B (l.toFunA pq)) :
    (Lens.tensorLeftView l).toFunA pq = l.toFunA pq ∧
      ((Lens.tensorLeftView l).toFunB pq d).1 = (l.toFunB pq d).1 ∧
      ((Lens.tensorRightView l).toFunB pq d).2 = (l.toFunB pq d).2 := by
  simp

/-- A lens out of a tensor is recovered from its two position-only views. -/
example {p q r : PFunctor.{u, u}} (l : Lens (p ⊗ q) r) :
    Lens.tensorGlue (Lens.tensorLeftView l) (Lens.tensorRightView l) rfl = l := by simp

/-- The universal property is stated directly in terms of compatible ordinary
lenses, with no second tensor-view representation. -/
example {p q r : PFunctor.{u, u}} :
    Lens (p ⊗ q) r ≃
      { views : Lens (p ⊗ linear q.A) r × Lens (linear p.A ⊗ q) r //
        views.1.toFunA = views.2.toFunA } :=
  Lens.tensorGlueEquiv

/-- The client-facing β laws hold for arbitrary compatible ordinary lenses,
including a caller-supplied compatibility proof and independent universes. -/
example {p : PFunctor.{pA, pB}} {q : PFunctor.{qA, qB}}
    {r : PFunctor.{rA, rB}}
    (left : Lens (p ⊗ linear q.A) r)
    (right : Lens (linear p.A ⊗ q) r)
    (positions : left.toFunA = right.toFunA) :
    Lens.tensorLeftView (Lens.tensorGlue left right positions) = left ∧
      Lens.tensorRightView (Lens.tensorGlue left right positions) = right := by
  simp

end PFunctor
