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
Each example below is discharged by `grind` alone, so the file fails as soon as one of those
equations stops being indexed.

The W-type presentation of free programs (`toWWithReturn_pure`, `ofWWithReturn_return`,
`ofWWithReturn_query`) stays `simp`-only: `grind` indexes the implicit `P + C α` argument of
`WType.mk` syntactically, and elaboration produces it both as the unreduced sum and as its
reduced `Sum`/`Sum.rec` fields, so those equations would match only one of the two spellings.
-/

@[expose] public section

namespace PolyFunTest.GrindSmoke

open PFunctor PFunctor.FreeM PFunctor.Lens

universe u v w uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

section Free

variable {P : PFunctor.{uA, uB}}

variable {m : Type uB → Type v} {n : Type uB → Type w} {o : Type uB → Type u}
  [Monad m] [Monad n] [Monad o]

/-- Naturality composes: two monad morphisms push through the fold as one post-composition. -/
example (s : Handler m P) (φ : m →ᵐ n) (ψ : n →ᵐ o) {α : Type uB} (x : FreeM P α) :
    ψ (φ (FreeM.liftM s x)) = FreeM.liftM (fun a => ψ (φ (s a))) x := by
  grind

/-- Naturality is stable under a retargeted handler: retargeting is unfolded at each position. -/
example (s : Handler m P) (φ : m →ᵐ n) (ψ : n →ᵐ o) {α : Type uB} (x : FreeM P α) :
    ψ (FreeM.liftM (Handler.mapTarget (fun c => φ c) s) x) =
      FreeM.liftM (fun a => ψ (Handler.mapTarget (fun c => φ c) s a)) x := by
  grind

end Free

section Handler

variable {m : Type u → Type v} {n : Type u → Type w} {o : Type u → Type uA}
  {q : PFunctor.{uB, u}}

/-- Retargeting twice applies both maps at every position. -/
example (second : ∀ {α : Type u}, n α → o α) (first : ∀ {α : Type u}, m α → n α)
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

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A constant lens after a `y`-sourced lens reads the position map at the chosen position. -/
example {A : Type uA} (f : P.A → A) (a : P.A) (u : PUnit) :
    (toConst f : Lens P (C A : PFunctor.{uA, uB})).toFunA
      ((fromY a : Lens y.{uA₂, uB₂} P).toFunA u) = f a := by
  grind

/-- Linear lenses choose the recorded direction at every position. -/
example {A : Type uA} (f : P.A → A) (choose : (a : P.A) → P.B a) (a : P.A) (u : PUnit) :
    (toLinear f choose : Lens P (linear A : PFunctor.{uA, uB})).toFunB a u = choose a := by
  grind

/-- Reassociating a tensor position and reading it back. -/
example (p : P.A) (q : Q.A) (r : R.A) :
    (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens.toFunA ((p, q), r) =
      (p, (q, r)) := by
  grind

end Lens

end PolyFunTest.GrindSmoke
