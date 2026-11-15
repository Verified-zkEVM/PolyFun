/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedDomains
import PolyFun.IPFunctor.Scoped.DomainInterpretation

/-! # Ordinary-import checks for continuous interpretations of binding signatures -/

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

/-- Relations over one context extend through a block of fresh bindings. -/
example {S : Type} {V W : S → Type} {R : ∀ a, V a → W a → Prop} {Γ Ξ : List S}
    {ξ : Env V Ξ} {ψ : Env W Ξ} {η : Env V Γ} {ζ : Env W Γ} (hx : Env.LiftRel R ξ ψ)
    (he : Env.LiftRel R η ζ) : Env.LiftRel R (Env.append ξ η) (Env.append ψ ζ) :=
  hx.append he

/-- An abstraction's value unfolds to `bindOne`, and applied to a value it reads that value. -/
example {S : Type} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)] {a : S} {E : Type}
    [OmegaCompletePartialOrder E] (f : Env V [a] →𝒄 E) (x : V a) :
    Env.abstraction f = Env.bindOne f ∧ Env.abstraction f x = f (Env.single x) :=
  ⟨rfl, rfl⟩

/-- A continuous meaning reads a variable from its environment. -/
example {S : Type} {σ : ScopedSignature S} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)]
    (alg : DomainInterpretation σ V) {Γ : List S} {a : S} (x : ScopedVar Γ a) (η : Env V Γ) :
    (Term.var (σ := σ) x).denoteDomain alg η = η a x := by simp

/-- Continuous meanings compose with substitution, for every continuous algebra. -/
example {S : Type} {σ : ScopedSignature S} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)]
    (alg : DomainInterpretation σ V) {Γ Δ : List S} {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (η : Env V Δ) :
    (t.subst θ).denoteDomain alg η =
      t.denoteDomain alg (Term.substitutionEnvDomain alg θ η) :=
  Term.denoteDomain_subst alg t θ η

/-- The fundamental lemma, at a relation indexed by one sort. -/
example {S : Type} {σ : ScopedSignature S} {V W : S → Type}
    [∀ a, OmegaCompletePartialOrder (V a)] {R : ∀ a, V a → W a → Prop}
    {alg : DomainInterpretation σ V} {alg' : Interpretation σ W}
    (h : DomainInterpretation.Related R alg alg') {Γ : List S} {a : S} (t : σ.Term Γ a)
    {η : Env V Γ} {ζ : Env W Γ} (hη : Env.LiftRel R η ζ) :
    R a (t.denoteDomain alg η) (t.denote alg' ζ) :=
  Term.denoteDomain_related h t hη

/-- Whenever the evaluator returns a value, the lazy meaning represents it. -/
example {a : Examples.ScopedDomains.Ty} (t : Examples.ScopedDomains.Expr [] a) (x : a.native)
    (h : t.denote Examples.ScopedDomains.evaluator Env.empty = some x) :
    Examples.ScopedDomains.Represents a (Examples.ScopedDomains.meaning t) x :=
  Examples.ScopedDomains.meaning_represents t x h

/-- An unused divergent argument is never demanded. -/
example : Examples.ScopedDomains.meaning (.app (.lam .zero) Examples.ScopedDomains.diverge) =
    Examples.ScopedDomains.number 0 :=
  Examples.ScopedDomains.meaning_const
