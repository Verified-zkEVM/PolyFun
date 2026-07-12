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
- `CartesianClosed.curry_uncurry : curry (uncurry g) = g` — the reverse
  round-trip.
- `CartesianClosed.curryEquiv` — the resulting equivalence of lens types.

All three of `p`, `q`, `r` live in a single universe `PFunctor.{uA, uB}`, since
`exp` requires its two arguments in a common universe and the adjunction is
stated within the one category `Poly.{uA, uB}`.
-/

@[expose] public section

universe u v w uA uB

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
`curry ∘ uncurry = id`, used below to prove the full lens identity. -/
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

/-! The reverse round-trip needs two small transport facts. Keeping them
private makes the proof explicit without exposing implementation-specific casts
as part of the cartesian-closed API. -/

private lemma transported_dependent_apply {ι : Type u} {γ : Type v} (F : ι → Type w)
    {a b : ι} (h : a = b) (f : F a → γ) (x : F a) (y : F b)
    (hy : cast (congrArg F h) x = y) :
    Eq.rec (motive := fun b (_ : a = b) => F b → γ) f h y = f x := by
  have hyx : y ≍ x := (heq_of_eq hy.symm).trans (cast_heq (congrArg F h) x)
  apply congr_heq ?_ hyx
  convert eqRec_heq (φ := fun b => F b → γ) h f using 1

private lemma cast_exp_direction_of_inl {q r : PFunctor.{uA, uB}}
    {f f' : (exp r q).A} (h : f = f') {i : q.A}
    {d : r.B (f i).1} {d' : r.B (f' i).1}
    {bd : (X + C (q.B i)).B ((f i).2 d)}
    {bd' : (X + C (q.B i)).B ((f' i).2 d')}
    (hd : d ≍ d') (hb : (f i).2 d = Sum.inl PUnit.unit) :
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

/-- Reverse round-trip of the cartesian exponential transpose: currying an
uncurried lens recovers the original lens. -/
@[simp, grind =]
theorem curry_uncurry {p q r : PFunctor.{uA, uB}} (g : Lens p (exp r q)) :
    curry (uncurry g) = g := by
  let hA : ∀ pa, (curry (uncurry g)).toFunA pa = g.toFunA pa :=
    fun pa => congrFun (curry_uncurry_toFunA g) pa
  apply Lens.ext _ _ hA
  intro pa
  funext yNew
  obtain ⟨i, d, bdNew⟩ := yNew
  have hpos := congrFun (congrFun (curry_uncurry_toFunA g) pa) i
  have hbranches :
      ((curry (uncurry g)).toFunA pa i).2 ≍ (g.toFunA pa i).2 :=
    congr_arg_heq Sigma.snd hpos
  have hbranch :
      ((curry (uncurry g)).toFunA pa i).2 d = (g.toFunA pa i).2 d :=
    congr_heq hbranches (HEq.refl d)
  cases hb : (g.toFunA pa i).2 d with
  | inl u =>
    have hbOld : (g.toFunA pa i).2 d = Sum.inl PUnit.unit := by
      exact hb.trans (congrArg Sum.inl (Subsingleton.elim u PUnit.unit))
    let bdOld : (X + C (q.B i)).B ((g.toFunA pa i).2 d) :=
      cast (congrArg (X + C (q.B i)).B hbOld.symm) PUnit.unit
    let xOld : (exp r q).B (g.toFunA pa) := ⟨i, d, bdOld⟩
    have hy : cast (congrArg (exp r q).B (hA pa).symm) xOld = ⟨i, d, bdNew⟩ :=
      cast_exp_direction_of_inl (hA pa).symm (HEq.refl d) hbOld
    rw [transported_dependent_apply (exp r q).B (hA pa).symm (g.toFunB pa)
      xOld ⟨i, d, bdNew⟩ hy]
    dsimp only [curry, uncurry, eval, Lens.comp, Lens.prodMap, Lens.piForall, Lens.id,
      Function.comp_apply, id_eq]
    grind
  | inr qi =>
    have hempty : PEmpty :=
      cast (congrArg (X + C (q.B i)).B (hbranch.trans hb)) bdNew
    exact hempty.elim

/-- The cartesian exponential adjunction as an equivalence of lens types. -/
def curryEquiv {p q r : PFunctor.{uA, uB}} :
    Lens (p * q) r ≃ Lens p (exp r q) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end CartesianClosed

end PFunctor
