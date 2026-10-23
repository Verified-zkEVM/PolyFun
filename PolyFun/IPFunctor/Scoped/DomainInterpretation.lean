/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain
public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Continuous interpretations of binding signatures

A continuous algebra receives each constructor argument as a continuous function of
only the variables that argument binds. It never sees the surrounding environment,
so every such algebra is natural in the context: renaming and substitution have
uniform semantic laws, and a constructor may take a least fixed point of an argument.

Two interpretations that send related arguments to related results give related
meanings for every term (`Term.denoteDomain_related`). The second interpretation is
an ordinary `Interpretation`, for example a total evaluator on a fragment, so one
constructor-local check relates a lazy semantics to its native counterpart.
-/

public section

open OmegaCompletePartialOrder

universe u v w z z'

namespace IPFunctor.ScopedSignature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {D : S → PointedDomain.{z}}
  {Γ Δ : List S}

/-- An algebra receiving each argument as a continuous function of its bound variables. -/
abbrev DomainInterpretation (σ : ScopedSignature.{u, v, w} S) (D : S → PointedDomain.{z}) :=
  ∀ {a} (op : σ.Op a),
    ((p : σ.Arg op) → ScopedDomain.Env D (σ.binders op p) →𝒄 D (σ.sort op p)) →𝒄 D a

namespace DomainInterpretation

/-- An argument's meaning as a function of its own bindings, in a fixed ambient environment. -/
@[expose] noncomputable def under {Ξ : List S} {b : S}
    (f : ScopedDomain.Env D (Ξ ++ Γ) →𝒄 D b) :
    ScopedDomain.Env D Γ →𝒄 (ScopedDomain.Env D Ξ →𝒄 D b) :=
  ContinuousHom.swapArgs (ContinuousHom.curry (f.comp (ScopedDomain.Env.appendContinuous D)))

@[simp] theorem under_apply {Ξ : List S} {b : S} (f : ScopedDomain.Env D (Ξ ++ Γ) →𝒄 D b)
    (η : ScopedDomain.Env D Γ) (ξ : ScopedDomain.Env D Ξ) :
    under f η ξ = f (ScopedDomain.Env.append D ξ η) := rfl

end DomainInterpretation

open DomainInterpretation

namespace Term

/-- The continuous meaning of a term, as a function of its environment. -/
@[expose] noncomputable def denoteDomain (alg : DomainInterpretation σ D) {a : S}
    (t : σ.Term Γ a) : ScopedDomain.Env D Γ →𝒄 D a :=
  t.fold (D := fun j : Judgment S => ScopedDomain.Env D j.1 →𝒄 D j.2)
    (fun _ x => .ofFun (fun η => η _ x))
    (fun _ op next => (alg op).comp (.ofFun (fun η p => under (next p) η) (by
      apply ωScottContinuous.of_apply₂
      intro p
      exact (under (next p)).ωScottContinuous)))

@[simp] theorem denoteDomain_var (alg : DomainInterpretation σ D) {a : S}
    (x : ScopedVar Γ a) (η : ScopedDomain.Env D Γ) :
    (var (σ := σ) x).denoteDomain alg η = η a x := rfl

@[simp] theorem denoteDomain_node (alg : DomainInterpretation σ D) {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p))
    (η : ScopedDomain.Env D Γ) :
    (node op args).denoteDomain alg η =
      alg op (fun p => under ((args p).denoteDomain alg) η) := rfl

/-- Renaming syntax reads its environment along the renaming. -/
theorem denoteDomain_rename (alg : DomainInterpretation σ D) {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (η : ScopedDomain.Env D Δ) :
    (t.rename ρ).denoteDomain alg η =
      t.denoteDomain alg (ScopedDomain.Env.rename D ρ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [rename_node, denoteDomain_node]
    congr 1
    funext p
    ext ξ
    simp only [under_apply, ih p, ScopedDomain.Env.rename_append]

/-- Interpret every substitution image in the same environment. -/
@[expose] noncomputable def substitutionEnvDomain (alg : DomainInterpretation σ D)
    (θ : σ.Substitution Γ Δ) (η : ScopedDomain.Env D Δ) : ScopedDomain.Env D Γ :=
  fun _ x => (θ x).denoteDomain alg η

theorem substitutionEnvDomain_liftMany (alg : DomainInterpretation σ D)
    (θ : σ.Substitution Γ Δ) (Ξ : List S) (ξ : ScopedDomain.Env D Ξ)
    (η : ScopedDomain.Env D Δ) :
    substitutionEnvDomain alg (Substitution.liftMany θ Ξ) (ScopedDomain.Env.append D ξ η) =
      ScopedDomain.Env.append D ξ (substitutionEnvDomain alg θ η) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    funext a x
    cases x with
    | zero => rfl
    | succ x =>
      change ((Substitution.liftMany θ Ξ x).rename ScopedVar.succ).denoteDomain alg _ = _
      rw [denoteDomain_rename]
      exact congrFun (congrFun (ih (fun b v => ξ b (.succ v))) a) x

/-- Substitution composes meanings; each language supplies only its constructor algebra. -/
theorem denoteDomain_subst (alg : DomainInterpretation σ D) {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (η : ScopedDomain.Env D Δ) :
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
theorem denoteDomain_substOne (alg : DomainInterpretation σ D) {a b : S}
    (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) (η : ScopedDomain.Env D Γ) :
    (body.substOne value).denoteDomain alg η =
      body.denoteDomain alg (ScopedDomain.Env.cons D (value.denoteDomain alg η) η) := by
  rw [substOne, denoteDomain_subst]
  congr 1
  funext c x
  cases x <;> rfl

end Term

/-! ## Related interpretations -/

section Related

variable {V : S → Type z'}

/-- A continuous and an ordinary environment related at every binding position. -/
@[expose] def EnvRelated (R : ∀ a, D a → V a → Prop) (η : ScopedDomain.Env D Γ)
    (ζ : Env V Γ) : Prop :=
  ∀ a (x : ScopedVar Γ a), R a (η a x) (ζ x)

/-- Related blocks of fresh bindings extend related environments. -/
theorem EnvRelated.append {R : ∀ a, D a → V a → Prop} {Ξ : List S}
    {ξ : ScopedDomain.Env D Ξ} {ξ' : Env V Ξ} {η : ScopedDomain.Env D Γ} {ζ : Env V Γ}
    (hξ : EnvRelated R ξ ξ') (hη : EnvRelated R η ζ) :
    EnvRelated R (ScopedDomain.Env.append D ξ η) (Env.append ξ' ζ) := by
  induction Ξ with
  | nil => exact hη
  | cons b Ξ ih =>
    intro a x
    cases x with
    | zero => exact hξ b .zero
    | succ x => exact ih (fun c y => hξ c (.succ y)) a x

/-- A continuous algebra simulated by an ordinary one: related arguments give related
results at every constructor. -/
@[expose] def DomainInterpretation.Related (R : ∀ a, D a → V a → Prop)
    (alg : DomainInterpretation σ D) (alg' : Interpretation σ V) : Prop :=
  ∀ {a} (op : σ.Op a)
    (k : (p : σ.Arg op) → ScopedDomain.Env D (σ.binders op p) →𝒄 D (σ.sort op p))
    (k' : (p : σ.Arg op) → Env V (σ.binders op p) → V (σ.sort op p)),
    (∀ p ξ ξ', EnvRelated R ξ ξ' → R _ (k p ξ) (k' p ξ')) → R a (alg op k) (alg' op k')

/-- The fundamental lemma: constructor-local relatedness gives related meanings. -/
theorem Term.denoteDomain_related {R : ∀ a, D a → V a → Prop}
    {alg : DomainInterpretation σ D} {alg' : Interpretation σ V}
    (h : DomainInterpretation.Related R alg alg') {a : S} (t : σ.Term Γ a)
    {η : ScopedDomain.Env D Γ} {ζ : Env V Γ} (hη : EnvRelated R η ζ) :
    R a (t.denoteDomain alg η) (t.denote alg' ζ) := by
  induction t using Term.inductionOn with
  | hvar Γ a x => exact hη a x
  | hnode Γ a op args ih =>
    exact h op _ _ (fun p ξ ξ' hξ => ih p (EnvRelated.append hξ hη))

end Related

end IPFunctor.ScopedSignature
