/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Cartesian exponential transposes for `Poly`

This file constructs the evaluation lens and one direction of the cartesian
exponential transpose, following Spivak–Niu
*Polynomial Functors* (Theorem 5.31, Example 5.32).

The exponential object used here is the `PFunctor.exp` of `PFunctor.Basic`,
namely `exp r q = ∏_{a : q.A} r ◃ (X + C (q.B a))`. This is the **cartesian**
exponential: it is the right adjoint to the categorical product functor
`- * q`, so lenses `p * q ⇆ r` correspond to lenses `p ⇆ exp r q`.

Do not confuse this with the `⊗`-internal hom (right adjoint to the tensor /
Dirichlet product `⊗`), which lives in `PolyFun/PFunctor/InternalHom.lean` as
`PFunctor.ihom`; the two closures answer different universal properties. The
cartesian transposes live in `PFunctor.CartesianClosed`, while the tensor
transposes live in `PFunctor.Lens`.

## Main definitions and results

- `CartesianClosed.eval : Lens (exp r q * q) r` — the evaluation / counit lens.
- `CartesianClosed.curry : Lens (p * q) r → Lens p (exp r q)` — the adjunction
  transpose (Theorem 5.31, forward direction).
- `CartesianClosed.uncurry : Lens p (exp r q) → Lens (p * q) r` — the inverse
  transpose, `eval ∘ₗ (g ×ₗ id)`.
- `CartesianClosed.uncurry_curry : uncurry (curry l) = l` — one round-trip of
  the transpose bijection, fully proven.
- `CartesianClosed.curry_uncurry_toFunA : (curry (uncurry g)).toFunA = g.toFunA`
  — the position component of the other round-trip, fully proven.

## Status / gap

The forward round-trip `uncurry (curry l) = l` is complete, as is the
position-level half of the reverse round-trip. The full direction-level reverse
identity `curry (uncurry g) = g` — and hence the packaged bijection
`curryEquiv : Lens (p * q) r ≃ Lens p (exp r q)` of Theorem 5.31 — is **not**
included here. It reduces (after `curry_uncurry_toFunA`) to a heterogeneous
equality of the two `toFunB` maps whose domains are only *propositionally* equal
(the exponential's branch data differs by a `PUnit`-collapse that is not
definitional), requiring dependent cast / `HEq` bookkeeping over the composition
`◃` that is deferred. All declarations below are `sorry`-free.

All three of `p`, `q`, `r` live in a single universe `PFunctor.{uA, uB}`, since
`exp` requires its two arguments in a common universe and the adjunction is
stated within the one category `Poly.{uA, uB}`.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

namespace CartesianClosed

/-- The evaluation lens `exp r q * q ⇆ r`, the counit of the cartesian
exponential adjunction (Spivak–Niu Example 5.32).

On positions, a pair `(f, a)` of an exponential position `f : (exp r q).A` and
an input position `a : q.A` maps to the `r`-position `(f a).1` that the strategy
`f` chooses at input `a`. On directions, each `r`-direction `d` at that position
is routed by the exponential's branch data `(f a).2 d : PUnit ⊕ q.B a`: a `PUnit`
branch feeds the direction back to the exponential factor, while a `q.B a` branch
feeds it to the input factor. -/
def eval {q r : PFunctor.{uA, uB}} : Lens (exp r q * q) r where
  toFunA := fun fqa => (fqa.1 fqa.2).1
  toFunB := fun fqa d =>
    match hh : (fqa.1 fqa.2).2 d with
    | Sum.inl _ => Sum.inl ⟨fqa.2, d, hh ▸ PUnit.unit⟩
    | Sum.inr qb => Sum.inr qb

/-- Transpose of a lens `p * q ⇆ r` to a lens `p ⇆ exp r q` (the forward
direction of the cartesian exponential adjunction, Spivak–Niu Theorem 5.31).

At each input position `a : q.A`, the component lens sends `pa : p.A` to the
`r`-position `l.toFunA (pa, a)`, with branch data recording, for each
`r`-direction, whether `l` sent it to the `p`-factor (`PUnit`, kept internal) or
the `q`-factor (`q.B a`). The backward map reads a `p`-direction back off `l`. -/
def curry {p q r : PFunctor.{uA, uB}}
    (l : Lens (p * q) r) : Lens p (exp r q) :=
  Lens.piForall (fun a =>
    { toFunA := fun pa => ⟨l.toFunA (pa, a),
        fun d => Sum.map (fun _ => PUnit.unit) id (l.toFunB (pa, a) d)⟩
      toFunB := fun pa dx =>
        match hh : l.toFunB (pa, a) dx.1 with
        | Sum.inl pb => pb
        | Sum.inr _ =>
            (cast (congrArg
              (fun s => (X + C (q.B a)).B (Sum.map (fun _ => PUnit.unit) id s)) hh)
              dx.2 : PEmpty).elim })

/-- Transpose of a lens `p ⇆ exp r q` back to a lens `p * q ⇆ r` (the backward
direction of the cartesian exponential adjunction), obtained by pairing with
`q` and post-composing with evaluation. -/
def uncurry {p q r : PFunctor.{uA, uB}}
    (g : Lens p (exp r q)) : Lens (p * q) r :=
  eval ∘ₗ (g ×ₗ Lens.id q)

@[simp, grind =]
theorem uncurry_curry {p q r : PFunctor.{uA, uB}} (l : Lens (p * q) r) :
    uncurry (curry l) = l := by
  apply Lens.ext
  case h₁ => intro a; rfl
  case h₂ =>
    intro a
    obtain ⟨pa, qa⟩ := a
    funext d
    dsimp only [uncurry, eval, curry, Lens.comp, Lens.prodMap, Lens.piForall, Lens.id,
      Function.comp_apply, id_eq] at d ⊢
    split <;> rename_i heq
    · simp only [Sum.elim_inl, Function.comp_apply]
      split <;> rename_i heq2
      · exact heq2.symm
      · rw [heq2] at heq; simp at heq
    · simp only [Sum.elim_inr, Function.comp_apply, id_eq]
      cases hs : l.toFunB (pa, qa) d with
      | inl pb => rw [hs] at heq; simp at heq
      | inr qb' => rw [hs] at heq; simp_all

/-- Position-level reverse round-trip: `curry (uncurry g)` and `g` agree on
positions. This is the position component of the adjunction unit-counit identity
`curry ∘ uncurry = id`; see the module docstring for the status of the full
direction-level identity. -/
@[simp]
theorem curry_uncurry_toFunA {p q r : PFunctor.{uA, uB}} (g : Lens p (exp r q)) :
    (curry (uncurry g)).toFunA = g.toFunA := by
  funext pa a
  dsimp only [curry, uncurry, eval, Lens.comp, Lens.prodMap, Lens.piForall, Lens.id,
    Function.comp_apply, id_eq]
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext d
  dsimp only
  split <;> rename_i heq
  · conv_rhs => rw [heq]
    rfl
  · conv_rhs => rw [heq]
    rfl

end CartesianClosed

end PFunctor
