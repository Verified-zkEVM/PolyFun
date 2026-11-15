/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedDomains
public import Examples.Tutorials.ScopedVectors
import PolyFun.IPFunctor.Scoped.Certificate

/-! # Ordinary-import checks for certified meanings of binding syntax -/

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature Control.Semantics

/-- The fundamental lemma as a relator, the premise of `CertifiedMeaning.ofLiftFun`. -/
example {S : Type} {σ : ScopedSignature S} {V W : S → Type}
    [∀ a, OmegaCompletePartialOrder (V a)] {R : ∀ a, V a → W a → Prop}
    {alg : DomainInterpretation σ V} {alg' : Interpretation σ W}
    (h : DomainInterpretation.Related R alg alg') {Γ : List S} {a : S} (t : σ.Term Γ a) :
    Relator.LiftFun (Env.LiftRel R) (R a) ⇑(t.denoteDomain alg) (t.denote alg') :=
  Term.liftFun_denoteDomain h t

/-- A certified term means its continuous meaning at the environment of its one input. -/
example {S : Type} {σ : ScopedSignature S} {V W : S → Type}
    [∀ a, OmegaCompletePartialOrder (V a)] {R : ∀ a, V a → W a → Prop}
    {alg : DomainInterpretation σ V} {alg' : Interpretation σ W}
    (h : DomainInterpretation.Related R alg alg') {a b : S} (t : σ.Term [a] b) {A B : Type}
    {input : A ↪ V a} {output : B ↪ V b} {nativeIn : A → W a} {nativeOut : B → W b}
    (represents : ∀ x, R a (input x) (nativeIn x))
    (determines : ∀ y v, R b v (nativeOut y) → v = output y) (implementation : A → B)
    (total : ∀ x, t.denote alg' (Env.single (nativeIn x)) = nativeOut (implementation x))
    (d : V a) :
    (t.certifiedMeaning h represents determines implementation total).meaning d =
      t.denoteDomain alg (Env.single d) := rfl

namespace PolyFunTest.ModuleAPI.Certificate

section ScopedDomains

open Examples.ScopedDomains

/-- `addTwo` returns the encoding of `n + 2` at the encoding of every `n`. -/
example (n : ℕ) :
    addTwoCertified.meaning (natEmbedding n) = natEmbedding (n + 2) :=
  addTwoCertified.correct n

/-- The decoded certificate's implementation is the native function. -/
example : addTwoDecoded.implementation = (· + 2) := rfl

/-- At every native input, the decoded lazy meaning returns a value. -/
example (n : ℕ) :
    decodeNat (addTwo.denoteDomain algebra (Env.single (number n))) =
      DomainResult.value (n + 2) :=
  decodeNat_addTwo n

/-- `pred` corresponds to `(· - 1)` on positive inputs, and diverges at zero. -/
example (n : ℕ) (hn : 0 < n) :
    pred.denoteDomain algebra (Env.single (number n)) = number (n - 1) ∧
      pred.denoteDomain algebra (Env.single (number 0)) = ⊥ :=
  ⟨pred_correspondsOn n hn, pred_zero⟩

end ScopedDomains

section ScopedVectors

open Examples.ScopedVectors Examples.ScopedVectors.TyTerm

/-- The evaluator certifies the lazy meaning of every term with one data input. -/
example {A B : TySig.Term [] .type} (t : Tm [] [mono A] (mono B))
    (hA : (A.denote tyAlg Env.empty).shape.Data) (hB : (B.denote tyAlg Env.empty).shape.Data)
    (x : (A.denote tyAlg Env.empty).shape.native) :
    (certifiedEvaluator t Env.empty hA hB).meaning (hA.embedding x) =
      hB.embedding ((certifiedEvaluator t Env.empty hA hB).implementation x) :=
  (certifiedEvaluator t Env.empty hA hB).correct x

/-- The certified implementation of `(λ x. x) x` is the identity. -/
example (n : ℕ) : (certifiedEvaluator applyIdentity Env.empty .nat .nat).implementation n = n :=
  certifiedEvaluator_applyIdentity n

end ScopedVectors

end PolyFunTest.ModuleAPI.Certificate
