/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Substitution

/-!
# Environments and interpretations of binding signatures

An argument meaning is a function of its newly bound variables. Constructor
interpretations receive these functions without evaluating their bodies.
Renaming and substitution have uniform semantic laws for every such algebra.
-/

public section

universe u v w z

namespace IPFunctor.ScopedSignature

variable {S : Type u} {V : S → Type z} {Γ Δ : List S}

/-- A value for every variable in a typed context. -/
abbrev Env (V : S → Type z) (Γ : List S) := ∀ {a}, ScopedVar Γ a → V a

namespace Env

/-- The unique environment of an empty context. -/
@[expose] def empty : Env V [] := fun {_} x => nomatch x

/-- Extend an environment by its nearest variable. -/
@[expose] def cons {a : S} (x : V a) (ρ : Env V Γ) : Env V (a :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

/-- Combine values for new binders with the surrounding environment. -/
@[expose] def append : {Ξ : List S} → Env V Ξ → Env V Γ → Env V (Ξ ++ Γ)
  | [], _, ρ => ρ
  | _ :: _, η, ρ => cons (η .zero) (append (fun x => η (.succ x)) ρ)

/-- Read an environment through a variable renaming. -/
@[expose] def pull (ρ : Renaming Γ Δ) (η : Env V Δ) : Env V Γ := fun x => η (ρ x)

/-- Extending a scope and pulling back an environment commute. -/
theorem pull_append (ρ : Renaming Γ Δ) (Ξ : List S) (η : Env V Ξ) (ξ : Env V Δ) :
    (pull (Renaming.liftMany ρ Ξ) (append η ξ) : Env V (Ξ ++ Γ)) =
      (append η (pull ρ ξ) : Env V (Ξ ++ Γ)) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    funext a x
    cases x with
    | zero => rfl
    | succ x =>
      exact congrFun (congrFun (ih (fun x => η (.succ x))) a) x

end Env

/-- An algebra receiving each argument as a function of its bound variables. -/
abbrev Interpretation (σ : ScopedSignature.{u, v, w} S) (V : S → Type z) :=
  ∀ {a} (op : σ.Op a), ((p : σ.Arg op) → Env V (σ.binders op p) → V (σ.sort op p)) → V a

namespace Term

variable {σ : ScopedSignature.{u, v, w} S}

/-- Fold a typed term into an environment-indexed meaning. -/
@[expose] def denote (alg : Interpretation σ V) {a : S} (t : σ.Term Γ a)
    (ρ : Env V Γ) : V a :=
  t.fold (D := fun j : Judgment S => Env V j.1 → V j.2)
    (fun _ x ρ => ρ x)
    (fun _ op next ρ => alg op (fun p η => next p (Env.append η ρ))) ρ

@[simp] theorem denote_var (alg : Interpretation σ V) {a : S}
    (x : ScopedVar Γ a) (ρ : Env V Γ) : (var (σ := σ) x).denote alg ρ = ρ x := rfl

@[simp] theorem denote_node (alg : Interpretation σ V) {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p))
    (ρ : Env V Γ) :
    (node op args).denote alg ρ = alg op (fun p η => (args p).denote alg (Env.append η ρ)) :=
  rfl

/-- Renaming syntax pulls back its semantic environment. -/
theorem denote_rename (alg : Interpretation σ V) {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (η : Env V Δ) :
    (t.rename ρ).denote alg η = t.denote alg (Env.pull ρ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [rename_node, denote_node]
    congr 1
    funext p ξ
    rw [ih p, Env.pull_append]

/-- Interpret every substitution image in the same environment. -/
@[expose] def substitutionEnv (alg : Interpretation σ V) (θ : σ.Substitution Γ Δ)
    (η : Env V Δ) : Env V Γ := fun x => (θ x).denote alg η

theorem substitutionEnv_liftMany (alg : Interpretation σ V) (θ : σ.Substitution Γ Δ)
    (Ξ : List S) (ξ : Env V Ξ) (η : Env V Δ) :
    (substitutionEnv alg (Substitution.liftMany θ Ξ) (Env.append ξ η) : Env V (Ξ ++ Γ)) =
      (Env.append ξ (substitutionEnv alg θ η) : Env V (Ξ ++ Γ)) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    funext a x
    cases x with
    | zero => rfl
    | succ x =>
      change ((Substitution.liftMany θ Ξ x).rename ScopedVar.succ).denote alg _ = _
      rw [denote_rename]
      exact congrFun (congrFun (ih (fun x => ξ (.succ x))) a) x

/-- Substitution composes meanings; each language supplies only its constructor algebra. -/
theorem denote_subst (alg : Interpretation σ V) {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (η : Env V Δ) :
    (t.subst θ).denote alg η = t.denote alg (substitutionEnv alg θ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [subst_node, denote_node]
    congr 1
    funext p ξ
    rw [ih p, substitutionEnv_liftMany]

/-- Entering a binder extends the semantic environment with the argument's meaning. -/
theorem denote_substOne (alg : Interpretation σ V) {a b : S}
    (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) (η : Env V Γ) :
    (body.substOne value).denote alg η =
      body.denote alg (Env.cons (value.denote alg η) η) := by
  rw [substOne, denote_subst]
  congr 1
  funext a x
  cases x <;> rfl

end Term
end IPFunctor.ScopedSignature
