/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Factorization

/-!
# Examples for the vertical–cartesian factorization

Regression tests: every lens factors as vertical-then-cartesian recovering the
original, the two legs land in their classes, and a concrete cartesian lens
(`inl`) is displayed vertical exactly when its position map is a bijection.
-/

@[expose] public section

universe u

namespace PFunctor

variable {P Q : PFunctor.{u, u}}

/-- The factorization recovers the original lens. -/
example (l : Lens P Q) : Lens.factorCart l ∘ₗ Lens.factorVert l = l :=
  Lens.factorCart_comp_factorVert l

/-- The vertical leg is vertical. -/
example (l : Lens P Q) : (Lens.factorVert l).IsVertical := Lens.factorVert_isVertical l

/-- The cartesian leg is cartesian. -/
example (l : Lens P Q) : (Lens.factorCart l).IsCartesian := Lens.factorCart_isCartesian l

section Orthogonality

variable {R S : PFunctor.{u, u}}

/-- Every vertical-left/cartesian-right commutative square has a diagonal. -/
example (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Nonempty (Lens.DiagonalFiller v f c g) :=
  Lens.exists_verticalCartesianDiagonal v f c g hv hc comm

/-- Both triangle equations are available directly from the bundled filler. -/
example (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    let d := Lens.verticalCartesianFiller v f c g hv hc comm
    d.diagonal ∘ₗ v = f ∧ c ∘ₗ d.diagonal = g := by
  exact ⟨(Lens.verticalCartesianFiller v f c g hv hc comm).comp_left,
    (Lens.verticalCartesianFiller v f c g hv hc comm).comp_right⟩

/-- The canonical diagonal triangles are simp-normal forms. -/
example (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Lens.verticalCartesianDiagonal v f c g hv hc comm ∘ₗ v = f ∧
      c ∘ₗ Lens.verticalCartesianDiagonal v f c g hv hc comm = g := by
  simp

/-- The diagonal is unique, not merely chosen. -/
example (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v)
    (d : Lens.DiagonalFiller v f c g) :
    d.diagonal = Lens.verticalCartesianDiagonal v f c g hv hc comm :=
  Lens.verticalCartesianDiagonal_unique v f c g hv hc comm d

/-- Equivalently, the bundled filler type is a subsingleton. -/
example (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Subsingleton (Lens.DiagonalFiller v f c g) :=
  Lens.subsingleton_verticalCartesianFillers v f c g hv hc comm

end Orthogonality

/-- `IsVertical` is closed under composition and holds of the identity. -/
example (l₁ l₂ : Lens P P) (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) :
    (l₁ ∘ₗ l₂).IsVertical := h₁.comp h₂

example : (Lens.id P).IsVertical := Lens.IsVertical.id P

/-- `inl : P ⇆ P + Q` is cartesian but not vertical (its position map `Sum.inl`
is injective but not surjective when `Q` has positions). -/
example : (Lens.inl : Lens P (P + Q)).IsCartesian := Lens.IsCartesian.inl

section Closure

variable {R W : PFunctor.{u, u}} {l₁ : Lens P R} {l₂ : Lens Q W}

/-- Verticality is closed under `⊎ₗ`, `×ₗ`, `⊗ₗ` (Spivak–Niu Prop 5.63). -/
example (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ⊎ₗ l₂).IsVertical :=
  h₁.sumMap h₂

example (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ×ₗ l₂).IsVertical :=
  h₁.prodMap h₂

example (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ⊗ₗ l₂).IsVertical :=
  h₁.tensorMap h₂

/-- Cartesianness is closed under `×ₗ`, `⊗ₗ`, and `◃ₗ` (Spivak–Niu Prop 5.63,
6.88). -/
example (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ×ₗ l₂).IsCartesian :=
  h₁.prodMap h₂

example (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ⊗ₗ l₂).IsCartesian :=
  h₁.tensorMap h₂

example (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) : (l₁ ◃ₗ l₂).IsCartesian :=
  h₁.compMap h₂

end Closure

/-- A lens that is both vertical and cartesian is an isomorphism `P ≃ₗ Q`. -/
example (l : Lens P Q) (hv : l.IsVertical) (hc : l.IsCartesian) :
    Nonempty (P ≃ₗ Q) := ⟨Lens.equivOfVerticalCartesian l hv hc⟩

/-- Conversely, the forward lens of every lens equivalence is vertical and
cartesian. -/
example (e : P ≃ₗ Q) : e.toLens.IsVertical ∧ e.toLens.IsCartesian :=
  ⟨e.toLens_isVertical, e.toLens_isCartesian⟩

/-- Both legs of an equivalence lie in both factorization classes. -/
example (e : P ≃ₗ Q) : e.invLens.IsVertical ∧ e.invLens.IsCartesian := by simp

/-- The two predicates exactly characterize the lenses underlying
equivalences. -/
example (l : Lens P Q) :
    (∃ e : P ≃ₗ Q, e.toLens = l) ↔ l.IsVertical ∧ l.IsCartesian :=
  Lens.exists_equiv_toLens_iff l

end PFunctor
