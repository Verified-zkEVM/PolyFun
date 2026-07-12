/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Hom-set adjunctions for trivial-interface polynomial functors

This file records the "trivial interface" hom-set equivalences of Spivak–Niu
*Polynomial Functors: A General Theory of Interaction* (Cambridge University
Press, 2025), §5.1. Each computes the set of lenses out of, or into, one of the
distinguished polynomial functors `0`, `1`, `X = y`, a constant `C A`, or a
linear `linear A` by a concrete data type. These are the hom-isomorphisms
witnessing the adjoint quadruple `linear ⊣ (−)(1) ⊣ C ⊣ (−)(0)` together with
the sections/principal-monomial refinements.

* `homFromZero` — `0` is initial in `Poly`: the lens `0 ⇆ p` is unique,
  `Lens 0 p ≃ PUnit`. (A special case of `Poly(I, q) ≅ Set(I, q(0))` from
  Spivak–Niu Thm 5.4 at `I = 0`.)
* `homToOne` — `1` is terminal in `Poly`: the lens `p ⇆ 1` is unique,
  `Lens p 1 ≃ PUnit`. (The `I = PUnit` case of `Poly(q, I) ≅ Set(q(1), I)`
  from Thm 5.4.)
* `homFromX` — a lens `y ⇆ p` is a position of `p`, `Lens X p ≃ p.A`. This is
  the counit of `linear ⊣ (−)(1)`, i.e. `Poly(y, q) ≅ q(1)` (Thm 5.4).
* `homToConst` — a lens `p ⇆ C A` is a map of positions `p.A → A`,
  `Lens p (C A) ≃ (p.A → A)`, i.e. `Poly(q, I) ≅ Set(q(1), I)` (Thm 5.4;
  the `C ⊣ (−)(0)` / `(−)(1) ⊣ C` unit).
* `homToLinear` — a lens `p ⇆ A·y` is a map of positions together with a
  section, `Lens p (linear A) ≃ (p.A → A) × ((a : p.A) → p.B a)`. This is the
  principal-monomial hom-iso `Poly(p, Iy^A) ≅ Set(p(1), I) × Set(A, Γ(p))` of
  Spivak–Niu Cor 5.15 specialised to `A_exp = PUnit`, where the second factor
  `(a : p.A) → p.B a` is the set of sections `Γ(p) = Poly(p, y)` (Prop 5.12).

## Design notes

The equivalences are stated as bare `Equiv`s between `Lens` types and concrete
types, matching the observation of the reading notes (§5.1) that none of these
hom-isos needs category-theory packaging to be useful.

These hom-isomorphisms are reference API: book-completeness formalizations of
the §5.1 trivial-interface adjunctions, staged for downstream (VCV-io)
consumers and exercised in `PolyFunTest/PFunctor/Adjunctions.lean`.

Both directions of `homFromX` and `homToLinear` hold definitionally
(`PUnit`/`Prod` eta), so their inverse laws are `rfl`. The three equivalences
touching an empty direction type (`homFromZero`, `homToOne`, `homToConst`)
need a `funext` into the empty type for one inverse law.

## Future work

The `⊗`-gluing constructors of Spivak–Niu Prop 5.49 / Cor 5.50 are not
formalised here. The parallel product of lenses `PFunctor.Lens.tensorMap` and
the tensor–hom adjunction `PFunctor.Lens.curryEquiv`
(in `PolyFun.PFunctor.InternalHom`, Ex 4.78 / Prop 4.85) already supply the
compositional `⊗` interface, so the residual gluing lemmas are deferred to a
follow-on rather than stated in a possibly-mismatched form.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂

namespace PFunctor

variable {p : PFunctor.{uA, uB}}

/-- **`0` is initial** (Spivak–Niu Thm 5.4, special case). The only lens out of
the zero polynomial functor is `Lens.initial`, so the hom-set is a singleton. -/
def homFromZero : Lens (0 : PFunctor.{uA₁, uB₁}) p ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Lens.initial
  left_inv _ := Lens.ext _ _ (fun a => a.elim) (fun a => a.elim)
  right_inv _ := rfl

/-- **`1` is terminal** (Spivak–Niu Thm 5.4, `I = PUnit` case of
`Poly(q, I) ≅ Set(q(1), I)`). The only lens into the unit polynomial functor is
`Lens.terminal`, so the hom-set is a singleton. -/
def homToOne : Lens p (1 : PFunctor.{uA₁, uB₁}) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Lens.terminal
  left_inv l := by
    refine Lens.ext _ _ (fun a => rfl) (fun a => ?_)
    funext d
    exact d.elim
  right_inv _ := rfl

/-- **Representability of `y`** (Spivak–Niu Thm 5.4, `Poly(y, q) ≅ q(1)`). A
lens `X ⇆ p` picks a single position of `p` via `toFunA PUnit.unit`, and its
`toFunB` is forced (every direction of `X` is `PUnit.unit`). -/
def homFromX : Lens X.{uA₁, uB₁} p ≃ p.A where
  toFun l := l.toFunA PUnit.unit
  invFun a := (fun _ => a) ⇆ (fun _ _ => PUnit.unit)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Constants are right adjoint on positions** (Spivak–Niu Thm 5.4,
`Poly(q, I) ≅ Set(q(1), I)`). A lens `p ⇆ C A` is exactly a function on
positions `p.A → A`; its backward map is forced since `C A` has no directions. -/
def homToConst {A : Type uA₂} : Lens p (C A : PFunctor.{uA₂, uB₁}) ≃ (p.A → A) where
  toFun l := l.toFunA
  invFun f := f ⇆ (fun _ => PEmpty.elim)
  left_inv l := by
    refine Lens.ext _ _ (fun a => rfl) (fun a => ?_)
    funext d
    exact d.elim
  right_inv _ := rfl

/-- **Principal monomial hom-iso** (Spivak–Niu Cor 5.15, at exponent `PUnit`).
A lens `p ⇆ A·y` is a function on positions `p.A → A` together with a section
`(a : p.A) → p.B a` of `p` (an element `Γ(p) = Poly(p, y)`), because the single
direction of `linear A` at each position is pulled back to a chosen direction
of `p`. -/
def homToLinear {A : Type uA₂} :
    Lens p (linear A : PFunctor.{uA₂, uB₁}) ≃ ((p.A → A) × ((a : p.A) → p.B a)) where
  toFun l := (l.toFunA, fun a => l.toFunB a PUnit.unit)
  invFun fg := fg.1 ⇆ (fun a _ => fg.2 a)
  left_inv _ := rfl
  right_inv _ := rfl

end PFunctor
