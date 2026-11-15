/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain
public import PolyFun.IPFunctor.Scoped.EnvRelation
public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Continuous interpretations of binding signatures

A continuous algebra receives each constructor argument as a continuous function of only the
variables that argument binds. It never sees the surrounding environment, so every such algebra
is natural in the context: renaming and substitution have uniform semantic laws, and a
constructor may take a least fixed point of an argument. The value family is unbundled: each
`V a` is an omega-complete partial order.

Two interpretations that send related arguments to related results give related meanings for
every term (`Term.denoteDomain_related`). The relation is any family `R : ∀ a, V a → W a →
Prop`, and environments are related by `Env.LiftRel R`. The second interpretation is an
ordinary `Interpretation`, for example a total evaluator on a fragment, so one
constructor-local check relates a lazy semantics to its native counterpart.
-/

public section

open OmegaCompletePartialOrder

universe u v w z z'

namespace IPFunctor.ScopedSignature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {V : S → Type z}
  [∀ a, OmegaCompletePartialOrder (V a)] {Γ Δ : List S}

/-- An algebra receiving each argument as a continuous function of its bound variables. -/
abbrev DomainInterpretation (σ : ScopedSignature.{u, v, w} S) (V : S → Type z)
    [∀ a, OmegaCompletePartialOrder (V a)] :=
  ∀ {a} (op : σ.Op a), ((p : σ.Arg op) → Env V (σ.binders op p) →𝒄 V (σ.sort op p)) →𝒄 V a

namespace DomainInterpretation

/-- An argument's meaning as a function of its own bindings, in a fixed ambient environment. -/
@[expose] noncomputable def under {Ξ : List S} {b : S} (f : Env V (Ξ ++ Γ) →𝒄 V b) :
    Env V Γ →𝒄 (Env V Ξ →𝒄 V b) :=
  ContinuousHom.swapArgs (ContinuousHom.curry (f.comp Env.appendContinuous))

@[simp] theorem under_apply {Ξ : List S} {b : S} (f : Env V (Ξ ++ Γ) →𝒄 V b) (η : Env V Γ)
    (ξ : Env V Ξ) : under f η ξ = f (Env.append ξ η) := rfl

end DomainInterpretation

open DomainInterpretation

namespace Term

/-- The continuous meaning of a term, as a function of its environment. -/
@[expose] noncomputable def denoteDomain (alg : DomainInterpretation σ V) {a : S}
    (t : σ.Term Γ a) : Env V Γ →𝒄 V a :=
  t.fold (D := fun j : Judgment S => Env V j.1 →𝒄 V j.2)
    (fun _ x => .ofFun (fun η => η _ x))
    (fun _ op next => (alg op).comp (.ofFun (fun η p => under (next p) η)))

@[simp] theorem denoteDomain_var (alg : DomainInterpretation σ V) {a : S}
    (x : ScopedVar Γ a) (η : Env V Γ) : (var (σ := σ) x).denoteDomain alg η = η a x := rfl

@[simp] theorem denoteDomain_node (alg : DomainInterpretation σ V) {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) (η : Env V Γ) :
    (node op args).denoteDomain alg η =
      alg op (fun p => under ((args p).denoteDomain alg) η) := rfl

/-- Renaming syntax reads its environment along the renaming. -/
theorem denoteDomain_rename (alg : DomainInterpretation σ V) {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (η : Env V Δ) :
    (t.rename ρ).denoteDomain alg η = t.denoteDomain alg (Env.rename ρ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [rename_node, denoteDomain_node]
    congr 1
    funext p
    ext ξ
    simp only [under_apply, ih p, Env.rename_append]

/-- Interpret every substitution image in the same environment. -/
@[expose] noncomputable def substitutionEnvDomain (alg : DomainInterpretation σ V)
    (θ : σ.Substitution Γ Δ) (η : Env V Δ) : Env V Γ :=
  fun _ x => (θ _ x).denoteDomain alg η

theorem substitutionEnvDomain_liftMany (alg : DomainInterpretation σ V)
    (θ : σ.Substitution Γ Δ) (Ξ : List S) (ξ : Env V Ξ) (η : Env V Δ) :
    substitutionEnvDomain alg (Substitution.liftMany θ Ξ) (Env.append ξ η) =
      Env.append ξ (substitutionEnvDomain alg θ η) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    funext a x
    cases x with
    | zero => rfl
    | succ x =>
      change ((Substitution.liftMany θ Ξ a x).rename fun _ => ScopedVar.succ).denoteDomain alg _ =
        _
      rw [denoteDomain_rename]
      exact congrFun (congrFun (ih (fun b v => ξ b (.succ v))) a) x

/-- Substitution composes meanings; each language supplies only its constructor algebra. -/
theorem denoteDomain_subst (alg : DomainInterpretation σ V) {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (η : Env V Δ) :
    (t.subst θ).denoteDomain alg η = t.denoteDomain alg (substitutionEnvDomain alg θ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [subst_node, denoteDomain_node]
    congr 1
    funext p
    ext ξ
    simp only [under_apply, ih p, substitutionEnvDomain_liftMany]

/-- Entering a binder extends the environment with the argument's meaning. -/
theorem denoteDomain_substOne (alg : DomainInterpretation σ V) {a b : S}
    (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) (η : Env V Γ) :
    (body.substOne value).denoteDomain alg η =
      body.denoteDomain alg (Env.cons (value.denoteDomain alg η) η) := by
  rw [substOne, denoteDomain_subst]
  congr 1
  funext c x
  cases x <;> rfl

end Term

/-! ## Related interpretations -/

section Related

variable {W : S → Type z'}

/-- A continuous algebra simulated by an ordinary one: related arguments give related results
at every constructor. -/
@[expose] def DomainInterpretation.Related (R : ∀ a, V a → W a → Prop)
    (alg : DomainInterpretation σ V) (alg' : Interpretation σ W) : Prop :=
  ∀ {a} (op : σ.Op a)
    (k : (p : σ.Arg op) → Env V (σ.binders op p) →𝒄 V (σ.sort op p))
    (k' : (p : σ.Arg op) → Env W (σ.binders op p) → W (σ.sort op p)),
    (∀ p ξ ξ', Env.LiftRel R ξ ξ' → R _ (k p ξ) (k' p ξ')) → R a (alg op k) (alg' op k')

/-- The fundamental lemma: constructor-local relatedness gives related meanings in related
environments. -/
theorem Term.denoteDomain_related {R : ∀ a, V a → W a → Prop}
    {alg : DomainInterpretation σ V} {alg' : Interpretation σ W}
    (h : DomainInterpretation.Related R alg alg') {a : S} (t : σ.Term Γ a)
    {η : Env V Γ} {ζ : Env W Γ} (hη : Env.LiftRel R η ζ) :
    R a (t.denoteDomain alg η) (t.denote alg' ζ) := by
  induction t using Term.inductionOn with
  | hvar Γ a x => exact hη a x
  | hnode Γ a op args ih =>
    exact h op _ _ fun p ξ ξ' hξ => ih p (hξ.append hη)

end Related

end IPFunctor.ScopedSignature
