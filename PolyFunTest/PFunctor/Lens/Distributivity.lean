/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Distributivity

/-!
# Examples for the left-distributivity laws of substitution

Regression tests instantiating the substitution-distributivity equivalences at
small concrete polynomials, and the guardrail witnessing that substitution does
*not* right-distribute over products (Spivak–Niu, Ex. 6.56).
-/

@[expose] public section

universe u

namespace PFunctor

/-! ## Instantiating the distributivity equivalences -/

/-- **Prop. 6.47 / (6.48)** (library `sumCompDistrib`) at `(X + 1) ◃ X`. -/
example := Lens.Equiv.sumCompDistrib (P := (X : PFunctor.{0, 0})) (Q := X) (R := 1)

/-- **(6.50)** (library `sigmaCompDistrib`) at a `Bool`-indexed family of `X`s. -/
example := Lens.sigmaCompDistrib (P := (X : PFunctor.{0, 0})) (F := fun _ : Bool => X)

/-- **(6.51)** at a `Bool`-indexed product of `X`s. -/
example := Lens.Equiv.piCompDistrib
  (P := (X : PFunctor.{0, 0})) (F := fun _ : Bool => X)

/-- The indexed-product distributivity equivalence round-trips positions. -/
example (x : ((pi (fun _ : Bool => X.{0, 0})) ◃ X).A) :
    Lens.Equiv.piCompDistrib.invLens.toFunA
      (Lens.Equiv.piCompDistrib.toLens.toFunA x) = x := rfl

/-- **(6.49)** at `X * X ◃ X`. -/
example := Lens.Equiv.prodCompDistrib (P := (X : PFunctor.{0, 0})) (Q := X) (R := X)

/-- **(6.49)** at `(X + 1) * X ◃ 1`. -/
example :=
  Lens.Equiv.prodCompDistrib (P := (X + 1 : PFunctor.{0, 0})) (Q := X) (R := 1)

/-- **Ex. 6.55** at `C Bool * X ◃ X`. -/
example := Lens.Equiv.scalarCompDistrib (A := Bool) (p := (X : PFunctor.{0, 0})) (q := X)

/-! ## The monomial hom-set equivalence -/

/-- A lens out of a monomial round-trips through `A → p(B)`. -/
example {A B : Type} {p : PFunctor.{0, 0}} (l : Lens (monomial A B) p) :
    Lens.homMonomialEquiv.symm (Lens.homMonomialEquiv l) = l := rfl

/-- A function `A → p(B)` round-trips through the lens. -/
example {A B : Type} {p : PFunctor.{0, 0}} (g : A → p.Obj B) :
    Lens.homMonomialEquiv (Lens.homMonomialEquiv.symm g) = g := rfl

/-- The identity lens on `Bool y^ Unit` becomes `a ↦ ⟨a, id⟩`. -/
example :
    Lens.homMonomialEquiv (Lens.id (monomial Bool Unit))
      = (fun a => ⟨a, id⟩ : Bool → (monomial Bool Unit).Obj Unit) := rfl

/-! ## Ex. 6.56: substitution does not right-distribute over products

With `p = X + 1`, `q = 1`, `r = 0`, the polynomial `p ◃ (q * r)` has a single
position while `(p ◃ q) * (p ◃ r)` has two, so the two sides cannot be
equivalent — substitution only distributes over products on the *left*. -/

/-- The left-hand `p ◃ (q * r)` has at most one position. -/
theorem right_distrib_lhs_subsingleton :
    Subsingleton (((X + 1 : PFunctor.{0, 0}) ◃ ((1 : PFunctor.{0, 0}) * 0)).A) := by
  constructor
  rintro ⟨a, f⟩ ⟨a', f'⟩
  have hE : IsEmpty (((1 : PFunctor.{0, 0}) * 0).A) :=
    inferInstanceAs (IsEmpty (PUnit × PEmpty))
  match a, f with
  | Sum.inl _, f => exact (hE.false (f PUnit.unit)).elim
  | Sum.inr _, f =>
    match a', f' with
    | Sum.inl _, f' => exact (hE.false (f' PUnit.unit)).elim
    | Sum.inr _, f' =>
      have : f = f' := funext (fun e => e.elim)
      subst this; rfl

/-- The right-hand `(p ◃ q) * (p ◃ r)` has at least two positions. -/
theorem right_distrib_rhs_nontrivial :
    Nontrivial ((((X + 1 : PFunctor.{0, 0}) ◃ 1) * ((X + 1 : PFunctor.{0, 0}) ◃ 0)).A) := by
  refine ⟨⟨⟨Sum.inl PUnit.unit, fun _ => PUnit.unit⟩, ⟨Sum.inr PUnit.unit, PEmpty.elim⟩⟩,
          ⟨⟨Sum.inr PUnit.unit, PEmpty.elim⟩, ⟨Sum.inr PUnit.unit, PEmpty.elim⟩⟩, ?_⟩
  intro h
  have h2 : (Sum.inl PUnit.unit : PUnit ⊕ PUnit) = Sum.inr PUnit.unit :=
    congrArg (fun z => z.1.1) h
  exact absurd h2 (by decide)

/-- Consequently there is no bijection between the two position types, so no
lens-equivalence right-distributes substitution over the product. -/
example :
    IsEmpty ((((X + 1 : PFunctor.{0, 0}) ◃ ((1 : PFunctor.{0, 0}) * 0)).A) ≃
      ((((X + 1 : PFunctor.{0, 0}) ◃ 1) * ((X + 1 : PFunctor.{0, 0}) ◃ 0)).A)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, y, hxy⟩ := right_distrib_rhs_nontrivial.exists_pair_ne
  exact hxy (e.symm.injective
    (@Subsingleton.elim _ right_distrib_lhs_subsingleton (e.symm x) (e.symm y)))

end PFunctor
