/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenTheory.Family
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Plug factorization is enough for the composition suite

`OpenTheory.HasPlugFactorization` records only the five equalities the UC
composition theorems consume. These checks pin that boundary: the free model
reaches the class through its strict `HasPlugWireFactor` instance, a family of
such theories reaches it pointwise, and the whole `Emulates` suite elaborates
from the class alone, with no unit, identity wire, or snake law in scope.
-/

public section

universe u

namespace Interaction.UC.PlugFactorizationExamples

open OpenSyntax

variable {Atom : PortBoundary → Type u}

/-- The free model has plug factorization through strict compact closure. -/
example : OpenTheory.HasPlugFactorization (Expr.theory Atom) := inferInstance

/-- Families of factoring theories factor pointwise. -/
example : OpenTheory.HasPlugFactorization (OpenTheory.pi fun _ : Nat => Expr.theory Atom) :=
  inferInstance

section FromFactorizationAlone

variable {T : OpenTheory.{u}} [OpenTheory.HasPlugFactorization T]

/-- Every observation respects factorization from the class alone. -/
example (Obs : Observation T) : Obs.RespectsFactorization := inferInstance

/-- The parallel composition theorem needs nothing beyond plug factorization. -/
example {Δ₁ Δ₂ : PortBoundary} (Obs : Observation T)
    {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.par real₁ real₂) (T.par ideal₁ ideal₂) Obs :=
  Emulates.par_compose h₁ h₂

/-- The wired composition theorem needs nothing beyond plug factorization. -/
example {Δ₁ Γ Δ₂ : PortBoundary} (Obs : Observation T)
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) Obs :=
  Emulates.wire_compose h₁ h₂

/-- The closed composition theorem needs nothing beyond plug factorization. -/
example {Δ : PortBoundary} (Obs : Observation T) {real ideal : T.Obj Δ}
    {K_real K_ideal : T.Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal Obs) (hEnv : Emulates K_real K_ideal Obs) :
    Obs.rel (T.close real K_real) (T.close ideal K_ideal) :=
  Emulates.plug_compose hProt hEnv

end FromFactorizationAlone

end Interaction.UC.PlugFactorizationExamples
