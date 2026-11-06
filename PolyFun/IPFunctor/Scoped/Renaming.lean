/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic

/-! # Renaming laws for typed polynomial syntax -/

public section

universe u v w

namespace IPFunctor.ScopedSignature

variable {S : Type u} {Γ Δ Θ : List S}

namespace Renaming

@[simp] theorem lift_id (b : S) {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => x) b x = x := by cases x <;> rfl

@[simp] theorem liftMany_id (Ξ : List S) {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => x) Ξ x = x := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x => exact congrArg ScopedVar.succ (ih x)

theorem lift_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) (b : S)
    {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => τ (ρ x)) b x = lift τ b (lift ρ b x) := by cases x <;> rfl

theorem liftMany_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => τ (ρ x)) Ξ x = liftMany τ Ξ (liftMany ρ Ξ x) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x => exact congrArg ScopedVar.succ (ih x)

end Renaming

namespace Term

variable {σ : ScopedSignature.{u, v, w} S}

/-- Renaming by the identity does not change syntax. -/
@[simp] theorem rename_id {Γ : List S} {a : S} (t : σ.Term Γ a) :
    t.rename (fun x => x) = t := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    rw [rename_node]
    congr 1
    funext p
    have h : (fun {a} (x : ScopedVar (σ.binders op p ++ Γ) a) =>
        Renaming.liftMany (fun x => x) (σ.binders op p) x) = (fun {a} x => x) := by
      funext a x
      exact Renaming.liftMany_id _ x
    simp only [h]
    exact ih p

/-- Successive renamings compose, including under arbitrary binder lists. -/
theorem rename_rename {Γ Δ Θ : List S} {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    (t.rename ρ).rename τ = t.rename (fun x => τ (ρ x)) := by
  induction t using Term.inductionOn generalizing Δ Θ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [rename_node]
    congr 1
    funext p
    rw [ih p]
    congr 1
    funext a x
    exact (Renaming.liftMany_comp ρ τ _ x).symm

end Term
end IPFunctor.ScopedSignature
