/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler
public import PolyFun.PFunctor.Lens.Basic

/-!
# `grind` smoke tests for the polynomial core

The `@[grind =]` equations of the handler fold's naturality, of handler retargeting, and of the
lens constructors let `grind` close goals that chain several of them, with no manual `simp` set.
Each example below is discharged by `grind` alone, and each of those equations is needed by at
least one example, so the file fails as soon as one of them stops being indexed.

The W-type presentation of free programs (`toWWithReturn_pure`, `ofWWithReturn_return`,
`ofWWithReturn_query`) stays `simp`-only. Each of those equations mentions `WType.mk` over
`P + C α`, on the left-hand side or the right, and with `grind =` each fails even on its own
statement, including `toWWithReturn_pure` stated with `FreeM.pure`: the implicit polynomial
argument of `WType.mk` is the unreduced sum in the lemma and its reduced `Sum` / `Sum.rec`
fields in a goal, and `grind` never merges the instantiated equation with the goal's term.
-/

@[expose] public section

namespace PolyFunTest.GrindSmoke

open PFunctor PFunctor.FreeM PFunctor.Lens

section Free

universe uP uB uM uN uO

variable {P : PFunctor.{uP, uB}}

variable {m : Type uB → Type uM} {n : Type uB → Type uN} {o : Type uB → Type uO}
  [Monad m] [Monad n] [Monad o]

/-- Naturality composes: two monad morphisms push through the fold as one post-composition. -/
example (s : Handler m P) (φ : m →ᵐ n) (ψ : n →ᵐ o) {α : Type uB} (x : FreeM P α) :
    ψ (φ (FreeM.liftM s x)) = FreeM.liftM (fun a => ψ (φ (s a))) x := by
  grind

/-- Naturality over a retargeted handler: the retargeting is unfolded at every position. -/
example (s : Handler m P) (φ : m →ᵐ n) (ψ : n →ᵐ o) {α : Type uB} (x : FreeM P α) :
    ψ (FreeM.liftM (Handler.mapTarget (fun c => φ c) s) x) =
      FreeM.liftM (fun a => ψ (φ (s a))) x := by
  grind

/-- Retargeting by the identity leaves the fold unchanged. -/
example (s : Handler m P) {α : Type uB} (x : FreeM P α) :
    FreeM.liftM (Handler.mapTarget (fun computation => computation) s) x = FreeM.liftM s x := by
  grind

end Free

section Handler

universe uQA uQ uM uN uO

variable {m : Type uQ → Type uM} {n : Type uQ → Type uN} {o : Type uQ → Type uO}
  {q : PFunctor.{uQA, uQ}}

/-- Retargeting twice applies both maps at every position. -/
example (second : ∀ {α : Type uQ}, n α → o α) (first : ∀ {α : Type uQ}, m α → n α)
    (handler : Handler m q) (position : q.A) :
    Handler.mapTarget second (Handler.mapTarget first handler) position =
      second (first (handler position)) := by
  grind

/-- Retargeting by the identity, twice, is the identity. -/
example (handler : Handler m q) :
    Handler.mapTarget (fun computation => computation)
      (Handler.mapTarget (fun computation => computation) handler) = handler := by
  grind

end Handler

section Lens

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uCA uCB uY₁ uY₂

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A constant lens after a `y`-sourced lens reads the position map at the chosen position. -/
example {A : Type uCA} (f : P.A → A) (a : P.A) (u : PUnit) :
    (toConst f : Lens P (C A : PFunctor.{uCA, uCB})).toFunA
      ((fromY a : Lens y.{uY₁, uY₂} P).toFunA u) = f a := by
  grind

/-- A `y`-sourced lens answers every direction with the unit direction of `y`. -/
example (a : P.A) (u : PUnit) (d : P.B a) :
    (fromY a : Lens y.{uY₁, uY₂} P).toFunB u d = PUnit.unit := by
  grind

/-- Linear and constant lenses built from the same position map agree on positions. -/
example {A : Type uCA} (f : P.A → A) (choose : (a : P.A) → P.B a) (a : P.A) :
    (toLinear f choose : Lens P (linear A : PFunctor.{uCA, uCB})).toFunA a =
      (toConst f : Lens P (C A : PFunctor.{uCA, uCB})).toFunA a := by
  grind

/-- Linear lenses choose the recorded direction at every position. -/
example {A : Type uCA} (f : P.A → A) (choose : (a : P.A) → P.B a) (a : P.A) (u : PUnit) :
    (toLinear f choose : Lens P (linear A : PFunctor.{uCA, uCB})).toFunB a u = choose a := by
  grind

/-- Reassociating a tensor position and reading it back. -/
example (p : P.A) (q : Q.A) (r : R.A) :
    (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunA ((p, q), r) =
      (p, (q, r)) := by
  grind

/-- Reassociating a tensor direction back to the original nesting. -/
example (p : P.A) (q : Q.A) (r : R.A) (dp : P.B p) (dq : Q.B q) (dr : R.B r) :
    (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunB ((p, q), r)
      (dp, (dq, dr)) = ((dp, dq), dr) := by
  grind

end Lens

end PolyFunTest.GrindSmoke
