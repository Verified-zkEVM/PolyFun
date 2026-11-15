/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Semantics.Correspondence
public import PolyFun.IPFunctor.Scoped.DomainInterpretation
public import PolyFun.IPFunctor.Scoped.StackedInterpretation

/-!
# Certified meanings from fundamental lemmas

A continuous meaning related to an ordinary evaluator by a fundamental lemma is certified against
a native implementation by two more facts. The representation relates each encoded input to a
native representative and lets a representative determine its encoded output. Totality says that
the evaluator returns the representative of the implementation's result.

* `Term.liftFun_denoteDomain` and `Stacked.Model.liftFun_denoteDomain` state the fundamental
  lemmas as `Relator.LiftFun`, the premise of `Control.Semantics.CertifiedMeaning.ofLiftFun`.
* `Term.certifiedMeaning` certifies a term with one free variable, which is its input, and
  `Term.correspondsOn_denoteDomain` gives the correspondence when the evaluator is total only on
  admissible inputs. `Stacked.Model.certifiedMeaning` certifies a term of a stacked family at a
  type assignment.

An input variable needs no function sorts, so first-order languages are covered. A language with
functions certifies a closed function term through `ofLiftFun` and its relation at function sorts.

The encodings and native representatives are bound after the term, so the term and the relation
fix their carriers before a representative such as `some` is elaborated. Throughout, `V` is the
family of semantic carriers and `W` the family of native ones; `d` is a semantic value and `w` a
native one.
-/

public section

open OmegaCompletePartialOrder Control.Semantics

universe u v w x y d e e' z z' uA uB

namespace IPFunctor.ScopedSignature

/-! ## Binding signatures -/

section Signature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {V : S → Type z} {W : S → Type z'}
  [∀ a, OmegaCompletePartialOrder (V a)] {R : ∀ a, V a → W a → Prop}
  {alg : DomainInterpretation σ V} {alg' : Interpretation σ W} {a b : S}

/-- The fundamental lemma as a relator: related environments give related meanings. -/
theorem Term.liftFun_denoteDomain (h : DomainInterpretation.Related R alg alg') {Γ : List S}
    (t : σ.Term Γ a) :
    Relator.LiftFun (Env.LiftRel R) (R a) ⇑(t.denoteDomain alg) (t.denote alg') :=
  fun _ _ hη => Term.denoteDomain_related h t hη

/-- The meaning of a term with one free variable, read as a function of that variable, is
certified against `implementation`. The input's encoding is related to its native
representative, a representative determines the encoded output, and the evaluator returns the
representative of `implementation x` at every input `x`. -/
@[expose] noncomputable def Term.certifiedMeaning (h : DomainInterpretation.Related R alg alg')
    (t : σ.Term [a] b) {A : Type uA} {B : Type uB} {input : A ↪ V a} {output : B ↪ V b}
    {nativeIn : A → W a} {nativeOut : B → W b} (represents : ∀ x, R a (input x) (nativeIn x))
    (determines : ∀ y d, R b d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, t.denote alg' (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    CertifiedMeaning input output :=
  CertifiedMeaning.ofLiftFun (fun d => t.denoteDomain alg (Env.single d)) implementation
    (eval := fun w => t.denote alg' (Env.single w))
    (fun _ _ hdw => Term.denoteDomain_related h t ((Env.liftRel_empty R).cons hdw))
    represents determines total

theorem Term.certifiedMeaning_meaning (h : DomainInterpretation.Related R alg alg')
    (t : σ.Term [a] b) {A : Type uA} {B : Type uB} {input : A ↪ V a} {output : B ↪ V b}
    {nativeIn : A → W a} {nativeOut : B → W b} (represents : ∀ x, R a (input x) (nativeIn x))
    (determines : ∀ y d, R b d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, t.denote alg' (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    (t.certifiedMeaning h represents determines implementation total).meaning =
      fun d => t.denoteDomain alg (Env.single d) := rfl

theorem Term.certifiedMeaning_implementation (h : DomainInterpretation.Related R alg alg')
    (t : σ.Term [a] b) {A : Type uA} {B : Type uB} {input : A ↪ V a} {output : B ↪ V b}
    {nativeIn : A → W a} {nativeOut : B → W b} (represents : ∀ x, R a (input x) (nativeIn x))
    (determines : ∀ y d, R b d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, t.denote alg' (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    (t.certifiedMeaning h represents determines implementation total).implementation =
      implementation := rfl

/-- The correspondence on admissible inputs, for an evaluator that returns the implementation's
representative only there. Outside `valid`, the meaning may diverge or fail. -/
theorem Term.correspondsOn_denoteDomain (h : DomainInterpretation.Related R alg alg')
    (t : σ.Term [a] b) {A : Type uA} {B : Type uB} {input : A ↪ V a} {output : B ↪ V b}
    {nativeIn : A → W a} {nativeOut : B → W b} {valid : A → Prop} {implementation : A → B}
    (represents : ∀ x, valid x → R a (input x) (nativeIn x))
    (determines : ∀ y d, R b d (nativeOut y) → d = output y)
    (total : ∀ x, valid x →
      t.denote alg' (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    CorrespondsOn input output valid (fun d => t.denoteDomain alg (Env.single d))
      implementation :=
  CorrespondsOn.of_liftFun (eval := fun w => t.denote alg' (Env.single w))
    (fun _ _ hdw => Term.denoteDomain_related h t ((Env.liftRel_empty R).cons hdw))
    represents determines total

end Signature

/-! ## Two-level binding families -/

section Stacked

variable {K : Type u} {τ : ScopedSignature.{u, v, w} K} {k₀ : K} {H : Heads.{u, x, y} K}
  {S : Stacked τ k₀ H} {M : Stacked.Model.{u, v, w, x, y, d} S}
  {V : M.Den k₀ → Type e} [∀ δ, OmegaCompletePartialOrder (V δ)] {W : M.Den k₀ → Type e'}
  {R : ∀ δ, V δ → W δ → Prop} {I : M.DomainInterp V} {I' : M.Interp W}

namespace Stacked.Model

/-- The fundamental lemma at a type assignment, as a relator. -/
theorem liftFun_denoteDomain (hI : DomainInterp.Related R I I') {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) (ρ : Env M.Den Θ) :
    Relator.LiftFun (Env.LiftRel fun s : τ.Term Θ k₀ => R (s.denote M.tyAlg ρ)) (R _)
      ⇑(M.denoteDomain V I t ρ) (M.denote W I' t ρ) :=
  fun _ _ hη => denoteDomain_related hI t ρ hη

variable {Θ : List K} {s s' : τ.Term Θ k₀}

/-- The meaning of a term with one free value variable, at the type assignment `ρ`, is certified
against `implementation`, under the premises of `Term.certifiedMeaning`. -/
@[expose] noncomputable def certifiedMeaning (hI : DomainInterp.Related R I I')
    (t : S.toFamily.Term Θ [s] s') (ρ : Env M.Den Θ) {A : Type uA} {B : Type uB}
    {input : A ↪ V (s.denote M.tyAlg ρ)} {output : B ↪ V (s'.denote M.tyAlg ρ)}
    {nativeIn : A → W (s.denote M.tyAlg ρ)} {nativeOut : B → W (s'.denote M.tyAlg ρ)}
    (represents : ∀ x, R _ (input x) (nativeIn x))
    (determines : ∀ y d, R _ d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, M.denote W I' t ρ (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    CertifiedMeaning input output :=
  CertifiedMeaning.ofLiftFun (fun d => M.denoteDomain V I t ρ (Env.single d)) implementation
    (eval := fun w => M.denote W I' t ρ (Env.single w))
    (fun _ _ hdw => denoteDomain_related hI t ρ ((Env.liftRel_empty _).cons hdw))
    represents determines total

theorem certifiedMeaning_meaning (hI : DomainInterp.Related R I I')
    (t : S.toFamily.Term Θ [s] s') (ρ : Env M.Den Θ) {A : Type uA} {B : Type uB}
    {input : A ↪ V (s.denote M.tyAlg ρ)} {output : B ↪ V (s'.denote M.tyAlg ρ)}
    {nativeIn : A → W (s.denote M.tyAlg ρ)} {nativeOut : B → W (s'.denote M.tyAlg ρ)}
    (represents : ∀ x, R _ (input x) (nativeIn x))
    (determines : ∀ y d, R _ d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, M.denote W I' t ρ (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    (certifiedMeaning hI t ρ represents determines implementation total).meaning =
      fun d => M.denoteDomain V I t ρ (Env.single d) := rfl

theorem certifiedMeaning_implementation (hI : DomainInterp.Related R I I')
    (t : S.toFamily.Term Θ [s] s') (ρ : Env M.Den Θ) {A : Type uA} {B : Type uB}
    {input : A ↪ V (s.denote M.tyAlg ρ)} {output : B ↪ V (s'.denote M.tyAlg ρ)}
    {nativeIn : A → W (s.denote M.tyAlg ρ)} {nativeOut : B → W (s'.denote M.tyAlg ρ)}
    (represents : ∀ x, R _ (input x) (nativeIn x))
    (determines : ∀ y d, R _ d (nativeOut y) → d = output y) (implementation : A → B)
    (total : ∀ x, M.denote W I' t ρ (Env.single (nativeIn x)) = nativeOut (implementation x)) :
    (certifiedMeaning hI t ρ represents determines implementation total).implementation =
      implementation := rfl

end Stacked.Model

end Stacked

end IPFunctor.ScopedSignature
