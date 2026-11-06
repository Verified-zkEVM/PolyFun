/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Renaming

/-! # Capture-avoiding substitution and composition -/

public section

universe u v w

namespace IPFunctor.ScopedSignature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {Γ Δ Θ : List S}

namespace Substitution

@[simp] theorem liftMany_var (Ξ : List S) {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (σ := σ) (fun x => Term.var x) Ξ x = Term.var x := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x =>
      change Term.weaken (liftMany (fun x => Term.var x) Ξ x) b = _
      rw [ih]
      rfl

theorem lift_rename (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) (b : S)
    {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => (θ x).rename ρ) b x = (lift θ b x).rename (Renaming.lift ρ b) := by
  cases x with
  | zero => rfl
  | succ x => simp only [lift, Term.weaken, Term.rename_rename, Renaming.lift]

theorem liftMany_rename (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => (θ x).rename ρ) Ξ x =
      (liftMany θ Ξ x).rename (Renaming.liftMany ρ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    change lift (liftMany (fun x => (θ x).rename ρ) Ξ) b x = _
    have h : (fun {a} (x : ScopedVar (Ξ ++ Γ) a) =>
        liftMany (fun x => (θ x).rename ρ) Ξ x) =
        (fun {a} x => (liftMany θ Ξ x).rename (Renaming.liftMany ρ Ξ)) := by
      funext a x
      exact ih x
    rw [h, lift_rename]
    rfl

theorem liftMany_renaming (ρ : Renaming Γ Δ) (θ : σ.Substitution Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => θ (ρ x)) Ξ x =
      liftMany θ Ξ (Renaming.liftMany ρ Ξ x) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x =>
      change Term.weaken (liftMany (fun x => θ (ρ x)) Ξ x) b = _
      rw [ih]
      rfl

end Substitution

namespace Term

/-- Substituting each variable by itself preserves syntax. -/
@[simp] theorem subst_id {a : S} (t : σ.Term Γ a) : t.subst (fun x => var x) = t := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    rw [subst_node]
    congr 1
    funext p
    have h : (fun {a} (x : ScopedVar (σ.binders op p ++ Γ) a) =>
        Substitution.liftMany (fun x => var (σ := σ) x) (σ.binders op p) x) =
        (fun {a} x => var x) := by
      funext a x
      exact Substitution.liftMany_var _ x
    simp only [h]
    exact ih p

/-- Renaming after substitution renames all of the substitution images. -/
theorem rename_subst {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) :
    (t.subst θ).rename ρ = t.subst (fun x => (θ x).rename ρ) := by
  induction t using Term.inductionOn generalizing Δ Θ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [subst_node, rename_node]
    congr 1
    funext p
    rw [ih p]
    congr 1
    funext a x
    exact (Substitution.liftMany_rename θ ρ _ x).symm

/-- Substitution after renaming composes the variable assignments. -/
theorem subst_rename {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (θ : σ.Substitution Δ Θ) :
    (t.rename ρ).subst θ = t.subst (fun x => θ (ρ x)) := by
  induction t using Term.inductionOn generalizing Δ Θ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [subst_node, rename_node]
    congr 1
    funext p
    rw [ih p]
    congr 1
    funext a x
    exact (Substitution.liftMany_renaming ρ θ _ x).symm

end Term

namespace Substitution

theorem lift_comp (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) (b : S)
    {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => (θ x).subst τ) b x = (lift θ b x).subst (lift τ b) := by
  cases x with
  | zero => rfl
  | succ x => simp only [lift, Term.weaken, Term.rename_subst, Term.subst_rename]

theorem liftMany_comp (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => (θ x).subst τ) Ξ x =
      (liftMany θ Ξ x).subst (liftMany τ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    change lift (liftMany (fun x => (θ x).subst τ) Ξ) b x = _
    have h : (fun {a} (x : ScopedVar (Ξ ++ Γ) a) =>
        liftMany (fun x => (θ x).subst τ) Ξ x) =
        (fun {a} x => (liftMany θ Ξ x).subst (liftMany τ Ξ)) := by
      funext a x
      exact ih x
    rw [h, lift_comp]
    rfl

/-- Extend a substitution by an image for its newest variable. -/
@[expose] def cons {a : S} (θ : σ.Substitution Γ Δ) (value : σ.Term Δ a) :
    σ.Substitution (a :: Γ) Δ
  | _, .zero => value
  | _, .succ x => θ x

end Substitution

namespace Term

/-- Successive capture-avoiding substitutions compose. -/
theorem subst_subst {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) :
    (t.subst θ).subst τ = t.subst (fun x => (θ x).subst τ) := by
  induction t using Term.inductionOn generalizing Δ Θ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [subst_node]
    congr 1
    funext p
    rw [ih p]
    congr 1
    funext a x
    exact (Substitution.liftMany_comp θ τ _ x).symm

/-- Substitute the innermost variable, retaining the surrounding context. -/
@[expose] def substOne {a b : S} (body : σ.Term (a :: Γ) b) (value : σ.Term Γ a) :
    σ.Term Γ b := body.subst (Substitution.cons (fun x => var x) value)

/-- Closing a body commutes with entering its newest binder. -/
theorem substOne_subst_lift {a b : S} (body : σ.Term (a :: Γ) b)
    (θ : σ.Substitution Γ Δ) (value : σ.Term Δ a) :
    (body.subst (Substitution.lift θ a)).substOne value =
      body.subst (Substitution.cons θ value) := by
  rw [substOne, subst_subst]
  congr 1
  funext b x
  cases x with
  | zero => rfl
  | succ x =>
    simp only [Substitution.lift, weaken, subst_rename, Substitution.cons]
    exact subst_id (θ x)

end Term
end IPFunctor.ScopedSignature
