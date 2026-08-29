/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Sampler-equivalence examples

Regression checks for the sampler-aware equivalence: the equivalence laws
apply, and the forgetting map lands in activation equivalence.  The `top`
relation family shows the equivalence degenerates gracefully when sampler
effects are forgotten.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.SamplerEquivExamples

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m]
  {Party : Type u} {Δ : PortBoundary}

/-- The equivalence laws chain at any relation family. -/
example {R : MonadRelFamily m} {p₁ p₂ p₃ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h₁₂ : OpenProcessSamplerEquiv R p₁ p₂)
    (h₂₃ : OpenProcessSamplerEquiv R p₂ p₃) :
    OpenProcessSamplerEquiv R p₃ p₁ :=
  (h₁₂.trans h₂₃).symm

/-- Sampler equivalence refines activation equivalence, at any relation
family. -/
example {R : MonadRelFamily m} {p₁ p₂ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h : OpenProcessSamplerEquiv R p₁ p₂) :
    OpenProcessActivationEquiv p₁ p₂ :=
  h.toActivationEquiv

end Interaction.UC.SamplerEquivExamples
