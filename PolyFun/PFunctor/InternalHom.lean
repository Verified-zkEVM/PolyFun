/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic
import Batteries.Tactic.Lint

/-!
# The internal hom of the tensor product

Following Spivak–Niu, *Polynomial Functors: A General Theory of Interaction*
(§4.5, Ex 4.78), the tensor (parallel / Dirichlet) product `⊗` on `PFunctor` is
closed: for each `q` the functor `- ⊗ q` has a right adjoint `ihom q -`, the
**internal hom** `[q, r]`. Its positions are exactly the lenses `q ⇆ r`, and a
direction at a lens `f` is a `q`-position together with an `r`-direction over its
image:

* `(ihom q r).A := Lens q r`;
* `(ihom q r).B f := Σ j : q.A, r.B (f.toFunA j)`.

The counit is the evaluation lens `eval : ihom q r ⊗ q ⇆ r`, and the adjunction
is witnessed by the `curry` / `uncurry` bijection

`Lens (p ⊗ q) r ≃ Lens p (ihom q r)`  (`curryEquiv`).

This is the object VCVio's `WireK`/`ProbResponder` wiring hand-rolls: wiring a
challenger against a responder is exactly closing over `eval`. Two special cases
tie the hom back to existing structure: `[y, r] ≅ r` (`ihomX`, the tensor-unit
law) and `(ihom q X).A = Lens q X = enclose q` — the positions of `[q, y]` are
the handlers (sections) of `q`.

Note this is a *different* object from `PFunctor.exp` (`P ^ Q`, Spivak–Niu §5.3),
which is the cartesian exponential right-adjoint to the categorical product,
not to `⊗`.
-/

@[expose] public section

universe uA uB

namespace PFunctor

/-- The **internal hom** `[q, r]` of the tensor product (Spivak–Niu Ex 4.78):
positions are the lenses `q ⇆ r`, and a direction at a lens `f` is a `q`-position
`j` paired with an `r`-direction over `f.toFunA j`. -/
def ihom (q r : PFunctor.{uA, uB}) : PFunctor.{max uA uB, max uA uB} where
  A := Lens q r
  B f := Σ j : q.A, r.B (f.toFunA j)

@[inherit_doc] scoped[PFunctor] infixr:60 " ⊸ " => ihom

namespace Lens

variable {p q r : PFunctor.{uA, uB}}

/-- The evaluation (counit) lens `eval : ihom q r ⊗ q ⇆ r`: at a position
`(f, j)` it exposes `f.toFunA j`, and pulls a direction `d : r.B (f.toFunA j)`
back to the pair `(⟨j, d⟩, f.toFunB j d)`. -/
def eval (q r : PFunctor.{uA, uB}) : Lens (ihom q r ⊗ q) r :=
  (fun fj => fj.1.toFunA fj.2) ⇆
    (fun fj d => (⟨fj.2, d⟩, fj.1.toFunB fj.2 d))

/-- Currying: a lens `p ⊗ q ⇆ r` transposes to a lens `p ⇆ ihom q r`. This is
the forward direction of the tensor–hom adjunction. -/
def curry (φ : Lens (p ⊗ q) r) : Lens p (ihom q r) :=
  (fun i => (fun j => φ.toFunA (i, j)) ⇆ (fun j d => (φ.toFunB (i, j) d).2)) ⇆
    (fun i => fun ⟨j, d⟩ => (φ.toFunB (i, j) d).1)

/-- Uncurrying: a lens `p ⇆ ihom q r` transposes to a lens `p ⊗ q ⇆ r`. Inverse
to `curry`. -/
def uncurry (ψ : Lens p (ihom q r)) : Lens (p ⊗ q) r :=
  (fun ij => (ψ.toFunA ij.1).toFunA ij.2) ⇆
    (fun ij d => (ψ.toFunB ij.1 ⟨ij.2, d⟩, (ψ.toFunA ij.1).toFunB ij.2 d))

/-- The tensor–hom adjunction as an equivalence of hom-sets:
`Lens (p ⊗ q) r ≃ Lens p (ihom q r)`. -/
def curryEquiv : Lens (p ⊗ q) r ≃ Lens p (ihom q r) where
  toFun := curry
  invFun := uncurry
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem uncurry_curry (φ : Lens (p ⊗ q) r) : uncurry (curry φ) = φ := rfl

@[simp] theorem curry_uncurry (ψ : Lens p (ihom q r)) : curry (uncurry ψ) = ψ := rfl

/-- Naturality of `eval` against a curried lens: evaluating a curried `φ` in
parallel with the identity on `q` recovers `φ`. -/
@[simp] theorem eval_comp_curry (φ : Lens (p ⊗ q) r) :
    eval q r ∘ₗ (curry φ ⊗ₗ Lens.id q) = φ := rfl

end Lens

/-! ## Special cases tying the hom to existing structure -/

/-- The tensor-unit law `[y, r] ≅ r`: a lens `y ⇆ r` is a position of `r`, and a
direction of `[y, r]` at that lens is a direction of `r`. -/
def ihomX (r : PFunctor.{uA, uB}) : ihom X r ≃ₗ r where
  toLens := (fun f => f.toFunA PUnit.unit) ⇆ (fun _f d => ⟨PUnit.unit, d⟩)
  invLens := (fun a => (fun _ => a) ⇆ (fun _ _ => PUnit.unit)) ⇆ (fun _ d => d.2)
  left_inv := rfl
  right_inv := rfl

/-- The positions of `[q, y]` are the sections (handlers) of `q`, i.e. the
lenses `q ⇆ y = enclose q`. -/
theorem ihom_X_A (q : PFunctor.{uA, uB}) :
    (ihom q X.{uA, uB}).A = Lens q X.{uA, uB} := rfl

/-! ## The internal hom of a coproduct

The internal hom turns a coproduct in its first argument into a categorical
product: `[q₁ + q₂, r] ≅ [q₁, r] × [q₂, r]`. On positions this is the universal
property of the coproduct, `Lens (q₁ + q₂) r ≃ Lens q₁ r × Lens q₂ r`; on
directions the sigma `Σ j : q₁.A ⊕ q₂.A, r.B (f.toFunA j)` splits as the
*coproduct* of the two direction sigmas (`Equiv.sumSigmaDistrib`), which matches
the directions of the categorical product `*` (positions multiply, directions
add). The target is therefore the categorical product `*`, not the tensor `⊗`:
the tensor combines directions multiplicatively and does not match the
coproduct-shaped fibers here. -/

/-- The positions of `[q₁ + q₂, r]` split as a product: a lens `q₁ + q₂ ⇆ r` is
exactly a pair of lenses `(q₁ ⇆ r, q₂ ⇆ r)`, by the universal property of the
coproduct. This is the position component of `ihomSum`, and equally identifies
the positions of the categorical-product form `ihom q₁ r * ihom q₂ r`. -/
def ihomSumAEquiv (q₁ q₂ r : PFunctor.{uA, uB}) :
    (ihom (q₁ + q₂) r).A ≃ (ihom q₁ r).A × (ihom q₂ r).A where
  toFun f := (f ∘ₗ Lens.inl, f ∘ₗ Lens.inr)
  invFun p := Lens.sumPair p.1 p.2
  left_inv f := Lens.comp_inl_inr f
  right_inv p := by
    obtain ⟨a, b⟩ := p
    simp only [Lens.sumPair_comp_inl, Lens.sumPair_comp_inr]

/-- The position bijection together with the fiber splitting, packaged as a
`PFunctor.Equiv`: over a lens `f : q₁ + q₂ ⇆ r` the sigma of `r`-directions over
`(q₁ + q₂).A` splits as the coproduct of the sigmas over `q₁.A` and `q₂.A`. -/
def ihomSumPEquiv (q₁ q₂ r : PFunctor.{uA, uB}) :
    ihom (q₁ + q₂) r ≃ₚ (ihom q₁ r * ihom q₂ r) where
  equivA := ihomSumAEquiv q₁ q₂ r
  equivB f := _root_.Equiv.sumSigmaDistrib (fun j => r.B (f.toFunA j))

/-- The internal hom sends a coproduct in its first argument to a categorical
product: `[q₁ + q₂, r] ≅ [q₁, r] × [q₂, r]`. This is the contravariant image of
the coproduct's universal property under the tensor–hom adjunction. -/
def ihomSum (q₁ q₂ r : PFunctor.{uA, uB}) :
    ihom (q₁ + q₂) r ≃ₗ (ihom q₁ r * ihom q₂ r) :=
  PFunctor.Equiv.toLensEquiv (ihomSumPEquiv q₁ q₂ r)

end PFunctor
