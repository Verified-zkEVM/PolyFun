/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import all PolyFun.PFunctor.Lens.Basic
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
- `CartesianClosed.curry_uncurry : curry (uncurry g) = g` — the reverse
  round-trip.
- `CartesianClosed.curryEquiv` — the resulting equivalence of lens types.

These transposes are reference API: a book-completeness formalization of the
§5.3 cartesian exponential (Thm 5.31), exercised in
`PolyFunTest/PFunctor/CartesianClosed.lean` and staged for a downstream
consumer. The `curry` / `eval` / `uncurry` used elsewhere in PolyFun (e.g.
`Game.lean`) are instead the `⊗`-internal-hom ones in `InternalHom.lean`.

All three of `p`, `q`, `r` live in a single universe `PFunctor.{uA, uB}`, since
`exp` requires its two arguments in a common universe and the adjunction is
stated within the one category `Poly.{uA, uB}`.
-/

@[expose] public section

universe u v w uA uB

namespace PFunctor

namespace CartesianClosed

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the exponential-adjunction equations below rewrite through the cartesian
product and exponential constructions there. `implicit_reducible` (unlike
`reducible`) keeps them opaque to simp and typeclass resolution, and needs
no `allowUnsafeReducibility`. -/
attribute [local implicit_reducible] PFunctor.monomial PFunctor.X PFunctor.prod
  PFunctor.instHMulPFunctor PFunctor.instMulPFunctor PFunctor.pi PFunctor.exp PFunctor.comp

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
def curry {p q r : PFunctor.{uA, uB}} (l : Lens (p * q) r) : Lens p (exp r q) :=
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
def uncurry {p q r : PFunctor.{uA, uB}} (g : Lens p (exp r q)) : Lens (p * q) r :=
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
      Function.comp, Function.comp_apply, id_eq] at d ⊢
    split <;> rename_i heq
    · simp only [Sum.elim_inl, Function.comp]
      split <;> rename_i heq2
      · exact heq2.symm
      · rw [heq2] at heq; simp at heq
    · simp only [Sum.elim_inr, Function.comp, id_eq]
      cases hs : l.toFunB (pa, qa) d with
      | inl pb => rw [hs] at heq; simp at heq
      | inr qb' => rw [hs] at heq; simp_all; rfl

/-- Position-level reverse round-trip: `curry (uncurry g)` and `g` agree on
positions. This is the position component of the adjunction unit-counit identity
`curry ∘ uncurry = id`, used below to prove the full lens identity. -/
theorem curry_uncurry_toFunA {p q r : PFunctor.{uA, uB}} (g : Lens p (exp r q)) :
    (curry (uncurry g)).toFunA = g.toFunA := by
  funext pa a
  dsimp only [curry, uncurry, eval, Lens.comp, Lens.prodMap, Lens.piForall, Lens.id,
    Function.comp, Function.comp_apply, id_eq]
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext d
  dsimp only
  split <;> rename_i heq <;> (conv_rhs => rw [heq]) <;> rfl

/-! The reverse round-trip needs two small transport facts. Keeping them
private makes the proof explicit without exposing implementation-specific casts
as part of the cartesian-closed API. -/

private lemma transported_dependent_apply {ι : Type u} {γ : Type v} (F : ι → Type w) {a b : ι}
    (h : a = b) (f : F a → γ) (x : F a) (y : F b) (hy : cast (congrArg F h) x = y) :
    Eq.rec (motive := fun b (_ : a = b) => F b → γ) f h y = f x := by
  have hyx : y ≍ x := (heq_of_eq hy.symm).trans (cast_heq (congrArg F h) x)
  apply congr_heq ?_ hyx
  convert eqRec_heq (φ := fun b => F b → γ) h f using 1

private lemma cast_exp_direction_of_inl {q r : PFunctor.{uA, uB}} {f f' : (exp r q).A} (h : f = f')
    {i : q.A} {d : r.B (f i).1} {d' : r.B (f' i).1} {bd : (X + C (q.B i)).B ((f i).2 d)}
    {bd' : (X + C (q.B i)).B ((f' i).2 d')} (hd : d ≍ d') (hb : (f i).2 d = Sum.inl PUnit.unit) :
    cast (congrArg (exp r q).B h) ⟨i, d, bd⟩ = ⟨i, d', bd'⟩ := by
  apply eq_of_heq
  refine (cast_heq (congrArg (exp r q).B h) ⟨i, d, bd⟩).trans ?_
  cases h
  have hdd : d = d' := eq_of_heq hd
  subst d'
  apply heq_of_eq
  let e : (X + C (q.B i)).B ((f i).2 d) ≃ PUnit :=
    _root_.Equiv.cast (congrArg (X + C (q.B i)).B hb)
  have hbd : bd = bd' := e.injective (Subsingleton.elim _ _)
  exact congrArg (fun z => (⟨i, ⟨d, z⟩⟩ : (exp r q).B f)) hbd

private theorem Lens.ext_heq {p q : PFunctor} (l₁ l₂ : Lens p q)
    (hA : l₁.toFunA = l₂.toFunA) (hB : l₁.toFunB ≍ l₂.toFunB) : l₁ = l₂ := by
  cases l₁ with
  | mk a₁ b₁ =>
    cases l₂ with
    | mk a₂ b₂ =>
      dsimp only [Lens.toFunA, Lens.toFunB] at hA hB
      cases hA
      cases eq_of_heq hB
      rfl

private lemma exp_direction_components {q r : PFunctor} {f f' : (exp r q).A}
    (h : f = f') {x : (exp r q).B f} {y : (exp r q).B f'} (hy : x ≍ y) :
    x.1 = y.1 ∧ x.2.1 ≍ y.2.1 := by
  cases h
  have hxy : x = y := eq_of_heq hy
  subst y
  exact ⟨rfl, HEq.rfl⟩

/-- Reverse round-trip of the cartesian exponential transpose: currying an
uncurried lens recovers the original lens. -/
@[simp, grind =]
theorem curry_uncurry {p q r : PFunctor.{uA, uB}} (g : Lens p (exp r q)) :
    curry (uncurry g) = g := by
  -- Lean 4.33: the original transport through `transported_dependent_apply`
  -- leaves a final goal that is no longer type-correct at implicit
  -- transparency, defeating `grind`; the round-trip is instead established
  -- componentwise through heterogeneous extensionality.
  apply Lens.ext_heq
  · exact curry_uncurry_toFunA g
  · apply Function.hfunext rfl
    intro pa pa' hpa
    cases hpa
    apply Function.hfunext (congrArg (exp r q).B (congrFun (curry_uncurry_toFunA g) pa))
    intro yNew yOld hy
    obtain ⟨iNew, dNew, bdNew⟩ := yNew
    obtain ⟨iOld, dOld, bdOld⟩ := yOld
    have hcomponents := exp_direction_components
      (congrFun (curry_uncurry_toFunA g) pa) hy
    have hi : iNew = iOld := hcomponents.1
    subst iOld
    have hd : dNew ≍ dOld := hcomponents.2
    have hpos := congrFun (congrFun (curry_uncurry_toFunA g) pa) iNew
    have hbranches := congr_arg_heq Sigma.snd hpos
    have hbranch : ((curry (uncurry g)).toFunA pa iNew).2 dNew =
        (g.toFunA pa iNew).2 dOld := congr_heq hbranches hd
    have hdEq : dNew = dOld := eq_of_heq hd
    subst dNew
    cases hs : (uncurry g).toFunB (pa, iNew) dOld with
    | inl pb =>
      simp only [curry, Lens.piForall]
      split <;> rename_i value hh
      · have hpb : value = pb := Sum.inl.inj (hh.symm.trans hs)
        dsimp only [uncurry, eval, Lens.comp, Lens.prodMap, Lens.id,
          Function.comp, Function.comp_apply, id_eq] at hs
        split at hs <;> rename_i heval
        · simp only [Sum.elim_inl] at hs
          have hp := Sum.inl.inj hs
          apply heq_of_eq
          rw [hpb, ← hp]
          apply congrArg (g.toFunB pa)
          let xRoute : (exp r q).B (g.toFunA pa) :=
            ⟨iNew, dOld, heval ▸ PUnit.unit⟩
          let xOld : (exp r q).B (g.toFunA pa) := ⟨iNew, dOld, bdOld⟩
          change xRoute = xOld
          dsimp only [xRoute, xOld]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          refine Sigma.ext rfl ?_
          let e : (X + C (q.B iNew)).B ((g.toFunA pa iNew).2 dOld) ≃ PUnit :=
            _root_.Equiv.cast (congrArg (X + C (q.B iNew)).B heval)
          exact heq_of_eq (e.injective (Subsingleton.elim _ _))
        · simp only [Sum.elim_inr] at hs
          contradiction
      · cases hh.symm.trans hs
    | inr qi =>
      have hnew : ((curry (uncurry g)).toFunA pa iNew).2 dOld = Sum.inr qi := by
        change Sum.map (fun _ => PUnit.unit) id
          ((uncurry g).toFunB (pa, iNew) dOld) = Sum.inr qi
        rw [hs]
        rfl
      have hempty : PEmpty := cast
        (congrArg (X + C (q.B iNew)).B hnew) bdNew
      exact hempty.elim

/-- The cartesian exponential adjunction as an equivalence of lens types. -/
def curryEquiv {p q r : PFunctor.{uA, uB}} : Lens (p * q) r ≃ Lens p (exp r q) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end CartesianClosed

end PFunctor
