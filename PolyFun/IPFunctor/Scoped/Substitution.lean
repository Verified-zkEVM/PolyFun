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
    liftMany (σ := σ) (fun _ x => Term.var x) Ξ a x = Term.var x := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x =>
      change Term.weaken (liftMany (fun _ x => Term.var x) Ξ a x) b = _
      rw [ih]
      rfl

/-- A lifted substitution weakens the image of each older variable. -/
theorem rename_succ_lift (θ : σ.Substitution Γ Δ) (b : S) :
    Env.rename (fun _ => ScopedVar.succ) (lift θ b) = fun a x => (θ a x).weaken b :=
  rfl

theorem lift_rename (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) (b : S)
    {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun a x => (θ a x).rename ρ) b a x = (lift θ b a x).rename (Renaming.lift ρ b) := by
  cases x with
  | zero => rfl
  | succ x => simp only [lift, Term.weaken, Term.rename_rename, Renaming.rename_succ_lift]

theorem liftMany_rename (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun a x => (θ a x).rename ρ) Ξ a x =
      (liftMany θ Ξ a x).rename (Renaming.liftMany ρ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    change lift (liftMany (fun a x => (θ a x).rename ρ) Ξ) b a x = _
    have h : (liftMany (fun a x => (θ a x).rename ρ) Ξ : σ.Substitution (Ξ ++ Γ) _) =
        fun a x => (liftMany θ Ξ a x).rename (Renaming.liftMany ρ Ξ) := by
      funext a x
      exact ih x
    rw [h, lift_rename]
    rfl

theorem liftMany_renaming (ρ : Renaming Γ Δ) (θ : σ.Substitution Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (Env.rename ρ θ) Ξ a x =
      liftMany θ Ξ a (Renaming.liftMany ρ Ξ a x) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x =>
      change Term.weaken (liftMany (Env.rename ρ θ) Ξ a x) b = _
      rw [ih]
      rfl

end Substitution

namespace Term

/-- Substituting each variable by itself preserves syntax. -/
@[simp] theorem subst_id {a : S} (t : σ.Term Γ a) : t.subst (fun _ x => var x) = t := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    rw [subst_node]
    congr 1
    funext p
    have h : (Substitution.liftMany (fun _ x => var (σ := σ) x) (σ.binders op p) :
        σ.Substitution (σ.binders op p ++ Γ) _) = fun _ x => var x := by
      funext a x
      exact Substitution.liftMany_var _ x
    simp only [h]
    exact ih p

/-- Renaming after substitution renames all of the substitution images. -/
theorem rename_subst {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (ρ : Renaming Δ Θ) :
    (t.subst θ).rename ρ = t.subst (fun a x => (θ a x).rename ρ) := by
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
    (t.rename ρ).subst θ = t.subst (Env.rename ρ θ) := by
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
    lift (fun a x => (θ a x).subst τ) b a x = (lift θ b a x).subst (lift τ b) := by
  cases x with
  | zero => rfl
  | succ x =>
    simp only [lift, Term.weaken, Term.rename_subst, Term.subst_rename, rename_succ_lift]

theorem liftMany_comp (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun a x => (θ a x).subst τ) Ξ a x =
      (liftMany θ Ξ a x).subst (liftMany τ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
    change lift (liftMany (fun a x => (θ a x).subst τ) Ξ) b a x = _
    have h : (liftMany (fun a x => (θ a x).subst τ) Ξ : σ.Substitution (Ξ ++ Γ) _) =
        fun a x => (liftMany θ Ξ a x).subst (liftMany τ Ξ) := by
      funext a x
      exact ih x
    rw [h, lift_comp]
    rfl

/-- Extend a substitution by an image for its newest variable. -/
@[deprecated Env.cons +typeChanged (since := "2026-11-07")]
abbrev cons {a : S} (θ : σ.Substitution Γ Δ) (value : σ.Term Δ a) :
    σ.Substitution (a :: Γ) Δ :=
  Env.cons value θ

end Substitution

namespace Term

/-- Successive capture-avoiding substitutions compose. -/
theorem subst_subst {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) :
    (t.subst θ).subst τ = t.subst (fun a x => (θ a x).subst τ) := by
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
    σ.Term Γ b := body.subst (Env.cons value fun _ x => var x)

/-- Closing a body commutes with entering its newest binder. -/
theorem substOne_subst_lift {a b : S} (body : σ.Term (a :: Γ) b)
    (θ : σ.Substitution Γ Δ) (value : σ.Term Δ a) :
    (body.subst (Substitution.lift θ a)).substOne value =
      body.subst (Env.cons value θ) := by
  rw [substOne, subst_subst]
  congr 1
  funext b x
  cases x with
  | zero => rfl
  | succ x =>
    simp only [Substitution.lift, weaken, subst_rename]
    exact subst_id (θ _ x)

end Term

/-! ## Composition and weakening below a block of fresh variables -/

namespace Substitution

/-- Substitute by `θ`, then by `θ'`. -/
@[expose] def comp (θ' : σ.Substitution Δ Θ) (θ : σ.Substitution Γ Δ) : σ.Substitution Γ Θ :=
  fun _ x => (θ _ x).subst θ'

@[simp] theorem comp_apply (θ' : σ.Substitution Δ Θ) (θ : σ.Substitution Γ Δ) {a : S}
    (x : ScopedVar Γ a) : θ'.comp θ a x = (θ a x).subst θ' := rfl

/-- Weakening below a block of fresh variables, as a substitution. -/
@[expose] def weakenMany (Ξ : List S) : σ.Substitution Γ (Ξ ++ Γ) :=
  fun _ x => Term.var (x.weakenMany Ξ)

/-- A substitution lifted past a block sends a weakened variable to its weakened image. -/
theorem liftMany_weakenMany (θ : σ.Substitution Γ Δ) (Ξ : List S) {a : S}
    (x : ScopedVar Γ a) :
    liftMany θ Ξ a (x.weakenMany Ξ) = (θ a x).subst (weakenMany Ξ) := by
  induction Ξ with
  | nil => exact (Term.subst_id _).symm
  | cons b Ξ ih =>
    change Term.weaken (liftMany θ Ξ a (x.weakenMany Ξ)) b = _
    rw [ih, Term.weaken, Term.rename_subst]
    rfl

end Substitution

namespace Term

/-- Substituting by a composite substitutes twice. -/
theorem subst_comp {a : S} (t : σ.Term Γ a) (θ : σ.Substitution Γ Δ)
    (θ' : σ.Substitution Δ Θ) : t.subst (θ'.comp θ) = (t.subst θ).subst θ' :=
  (subst_subst t θ θ').symm

/-- Weakening below one fresh variable by substitution is the renaming `Term.weaken`. -/
theorem subst_weakenMany_singleton (b : S) {a : S} (t : σ.Term Γ a) :
    t.subst (Substitution.weakenMany [b]) = t.weaken b := by
  conv_rhs => rw [← subst_id t]
  rw [weaken, rename_subst]
  rfl

/-- Substitution commutes with weakening below a block of fresh variables. -/
theorem subst_weakenMany_liftMany (θ : σ.Substitution Γ Δ) (Ξ : List S) {a : S}
    (t : σ.Term Γ a) :
    (t.subst (Substitution.weakenMany Ξ)).subst (Substitution.liftMany θ Ξ) =
      (t.subst θ).subst (Substitution.weakenMany Ξ) := by
  rw [subst_subst, subst_subst]
  congr 1
  funext b x
  exact Substitution.liftMany_weakenMany θ Ξ x

end Term
end IPFunctor.ScopedSignature
