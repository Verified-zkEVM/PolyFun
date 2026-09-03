/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.EmulatesQuotient
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Quotient-theory examples

Regression checks for quotient open theories. A theory whose laws hold modulo
a congruence has a strictly lawful quotient; a strict theory satisfies every
law modulo any congruence; the free syntax model is the quotient of raw syntax
by its congruence, so raw syntax inherits the whole `Emulates` composition
suite at the observation pulled back from equality of classes.
-/

@[expose] public section

universe u

namespace Interaction.UC.QuotientExamples

open OpenTheory OpenSyntax

/-- A strict theory satisfies every law modulo the discrete congruence, and the
quotient by it is again strict. -/
example (T : OpenTheory.{u}) [HasPlugWireFactor T] :
    HasPlugWireFactorMod (Congruence.eq T) :=
  inferInstance

example (T : OpenTheory.{u}) [HasPlugWireFactor T] :
    HasPlugWireFactor (T.quotient (Congruence.eq T)) :=
  inferInstance

example (T : OpenTheory.{u}) [HasPlugFactorization T] :
    HasPlugFactorization (T.quotient (Congruence.eq T)) :=
  inferInstance

/-- The free syntax model is the quotient of raw syntax, and raw syntax
satisfies the laws modulo its congruence. -/
example (Atom : PortBoundary → Type u) :
    Expr.theory Atom = (Raw.theory Atom).quotient (Raw.congruence Atom) :=
  rfl

example (Atom : PortBoundary → Type u) : HasPlugWireFactorMod (Raw.congruence Atom) :=
  inferInstance

example (Atom : PortBoundary → Type u) : HasPlugWireFactor (Expr.theory Atom) :=
  inferInstance

/-- Raw syntax is not lawful, but emulation over raw syntax at the observation
pulled back from equality of classes has the full composition suite: the
quotient satisfies plug factorization, so the pulled-back observation respects
it. -/
example (Atom : PortBoundary → Type u) {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : Raw Atom Δ₁} {real₂ ideal₂ : Raw Atom Δ₂}
    (h₁ : Emulates (T := Raw.theory Atom) real₁ ideal₁
      ((Observation.eq (Expr.theory Atom)).comap (Raw.congruence Atom)))
    (h₂ : Emulates (T := Raw.theory Atom) real₂ ideal₂
      ((Observation.eq (Expr.theory Atom)).comap (Raw.congruence Atom))) :
    Emulates (T := Raw.theory Atom) (Raw.par real₁ real₂) (Raw.par ideal₁ ideal₂)
      ((Observation.eq (Expr.theory Atom)).comap (Raw.congruence Atom)) :=
  Emulates.par_compose h₁ h₂

/-- Emulation of classes is emulation of representatives; at the free model
the pulled-back observation is `Raw.Equiv` on closed raw terms. -/
example (Atom : PortBoundary → Type u) {Δ : PortBoundary} {real ideal : Raw Atom Δ} :
    Emulates (T := Expr.theory Atom) (Expr.mk real) (Expr.mk ideal)
        (Observation.eq (Expr.theory Atom)) ↔
      Emulates (T := Raw.theory Atom) real ideal
        (Observation.ofCongruence (Raw.congruence Atom)) :=
  (Emulates.ofCongruence_iff (Raw.congruence Atom)).symm

example (Atom : PortBoundary → Type u) (c₁ c₂ : Raw Atom PortBoundary.empty) :
    (Observation.ofCongruence (Raw.congruence Atom)).rel c₁ c₂ ↔ Raw.Equiv c₁ c₂ :=
  Iff.rfl

/-- An `E`-invariant observation descends to the quotient and pulls back to
itself. -/
example (T : OpenTheory.{u}) (E : Congruence T) (Obs : Observation T)
    (hInv : ∀ {c₁ c₂ : T.Closed}, E.rel c₁ c₂ → Obs.rel c₁ c₂) (c₁ c₂ : T.Closed) :
    ((Obs.descend E hInv).comap E).rel c₁ c₂ ↔ Obs.rel c₁ c₂ :=
  Observation.comap_descend_rel E Obs hInv

end Interaction.UC.QuotientExamples
