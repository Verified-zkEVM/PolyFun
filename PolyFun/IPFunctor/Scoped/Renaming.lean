/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic

/-!
# Renaming laws for typed polynomial syntax

`Env.rename ρ η` reads the environment `η` through the renaming `ρ`. Renamings and
substitutions are environments, so the same operation composes a renaming with either:
`Env.rename ρ τ` applies `ρ` and then `τ`.
-/

public section

universe u v w z

namespace IPFunctor.ScopedSignature

variable {S : Type u} {Γ Δ Θ : List S}

namespace Env

variable {V : S → Type z}

/-- Read an environment through a renaming of its binding positions. -/
@[expose] def rename (ρ : Renaming Γ Δ) (η : Env V Δ) : Env V Γ := fun a x => η a (ρ a x)

@[simp] theorem rename_apply (ρ : Renaming Γ Δ) (η : Env V Δ) {a : S} (x : ScopedVar Γ a) :
    rename ρ η a x = η a (ρ a x) := rfl

@[simp] theorem rename_id (η : Env V Γ) : rename (fun _ x => x) η = η := rfl

/-- Reading through two renamings reads through their composite. -/
theorem rename_rename (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) (η : Env V Θ) :
    rename ρ (rename τ η) = rename (rename ρ τ) η := rfl

/-- Protecting a fresh variable preserves its value. -/
theorem rename_cons (ρ : Renaming Γ Δ) {a : S} (x : V a) (η : Env V Δ) :
    rename (ρ.lift a) (cons x η) = cons x (rename ρ η) := by
  funext b v
  cases v <;> rfl

/-- The fresh block is unchanged when the ambient environment is renamed. -/
theorem rename_append (ρ : Renaming Γ Δ) {Ξ : List S} (ξ : Env V Ξ) (η : Env V Δ) :
    rename (ρ.liftMany Ξ) (append ξ η) = append ξ (rename ρ η) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change rename (Renaming.lift (ρ.liftMany Ξ) a) (cons _ _) = _
      rw [rename_cons, ih]
      rfl

end Env

namespace Renaming

@[simp] theorem lift_id (b : S) {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (fun _ x => x) b a x = x := by cases x <;> rfl

@[simp] theorem liftMany_id (Ξ : List S) {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun _ x => x) Ξ a x = x := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    cases x with
    | zero => rfl
    | succ x => exact congrArg ScopedVar.succ (ih x)

/-- Weakening and then lifting a renaming is renaming and then weakening. -/
theorem rename_succ_lift (ρ : Renaming Γ Δ) (b : S) :
    Env.rename (fun _ => ScopedVar.succ) (lift ρ b) = Env.rename ρ fun _ => ScopedVar.succ :=
  rfl

theorem lift_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) (b : S)
    {a : S} (x : ScopedVar (b :: Γ) a) :
    lift (Env.rename ρ τ) b a x = lift τ b a (lift ρ b a x) := by cases x <;> rfl

theorem liftMany_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) (Ξ : List S)
    {a : S} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (Env.rename ρ τ) Ξ a x = liftMany τ Ξ a (liftMany ρ Ξ a x) := by
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
    t.rename (fun _ x => x) = t := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    rw [rename_node]
    congr 1
    funext p
    have h : (Renaming.liftMany (fun _ x => x) (σ.binders op p) :
        Renaming (σ.binders op p ++ Γ) _) = fun _ x => x := by
      funext a x
      exact Renaming.liftMany_id _ x
    rw [h]
    exact ih p

/-- Successive renamings compose, including under arbitrary binder lists. -/
theorem rename_rename {Γ Δ Θ : List S} {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    (t.rename ρ).rename τ = t.rename (Env.rename ρ τ) := by
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
