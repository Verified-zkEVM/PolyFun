/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Family

/-!
# Substitution under changing parameter contexts

A language supplies the action of its parameter-context changes on terms.
Value substitution then transports old images and protects every newly bound
variable. The operation and its laws do not depend on the language's kinds or types.
-/

public section

universe u v w z

namespace IPFunctor.ScopedFamily

variable {W : Type u} {S : W → Type v} (σ : ScopedFamily.{u, v, w, z} W S)

/-- Action on syntax of the parameter-context change at each constructor argument. -/
abbrev ReindexAction := ∀ {w : W} {a : S w} (op : σ.Op w a) (p : σ.Arg op)
  {Γ : List (S w)} {b : S w}, σ.Term w Γ b →
    σ.Term (σ.world op p) (Γ.map (σ.reindex op p)) (σ.reindex op p b)

/-- A simultaneous substitution at one parameter context. -/
abbrev Substitution {w : W} (Γ Δ : List (S w)) :=
  ∀ {a}, ScopedVar Γ a → σ.Term w Δ a

namespace Substitution

variable {σ} {w : W} {Γ Δ : List (S w)}

/-- Protect one fresh variable and weaken the older substitution images. -/
@[expose] def lift (θ : σ.Substitution Γ Δ) (b : S w) :
    σ.Substitution (b :: Γ) (b :: Δ)
  | _, .zero => .pure .zero
  | _, .succ x => (θ x).rename ScopedVar.succ

/-- Protect all variables bound in a constructor argument. -/
@[expose] def liftMany (θ : σ.Substitution Γ Δ) :
    (Ξ : List (S w)) → σ.Substitution (Ξ ++ Γ) (Ξ ++ Δ)
  | [] => θ
  | b :: Ξ => lift (liftMany θ Ξ) b

/-- Move substitution images to a new parameter context without merging positions. -/
@[expose] def reindex (A : σ.ReindexAction) (θ : σ.Substitution Γ Δ)
    {a : S w} (op : σ.Op w a) (p : σ.Arg op) :
    σ.Substitution (Γ.map (σ.reindex op p)) (Δ.map (σ.reindex op p)) :=
  ScopedVar.mapLookup (σ.reindex op p) (fun x => A op p (θ x))

@[simp] theorem reindex_map (A : σ.ReindexAction) (θ : σ.Substitution Γ Δ)
    {a b : S w} (op : σ.Op w a) (p : σ.Arg op) (x : ScopedVar Γ b) :
    θ.reindex A op p (x.map (σ.reindex op p)) = A op p (θ x) :=
  ScopedVar.mapLookup_map _ _ x

@[simp] theorem liftMany_var (Ξ : List (S w)) {a : S w} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (σ := σ) (fun x => Term.var x) Ξ x = Term.var x := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
      cases x with
      | zero => rfl
      | succ x =>
          change (liftMany (fun x => Term.var x) Ξ x).rename ScopedVar.succ = _
          rw [ih]
          rfl

/-- Precomposing substitution images with a renaming commutes with binder lifting. -/
theorem liftMany_rename {Θ : List (S w)} (ρ : ScopedSignature.Renaming Γ Δ)
    (θ : σ.Substitution Δ Θ) (Ξ : List (S w)) {a : S w} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany θ Ξ (ρ.liftMany Ξ x) = liftMany (fun x => θ (ρ x)) Ξ x := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
      cases x with
      | zero => rfl
      | succ x =>
          change (liftMany θ Ξ (ρ.liftMany Ξ x)).rename ScopedVar.succ =
            (liftMany (fun x => θ (ρ x)) Ξ x).rename ScopedVar.succ
          rw [ih]

/-- Reindexing substitution images retains the composition of binding positions. -/
theorem reindex_rename (A : σ.ReindexAction) {Θ : List (S w)}
    (ρ : ScopedSignature.Renaming Γ Δ) (θ : σ.Substitution Δ Θ)
    {a : S w} (op : σ.Op w a) (p : σ.Arg op) :
    (reindex A (fun x => θ (ρ x)) op p : σ.Substitution _ _) =
      fun {_} x => reindex A θ op p (ScopedSignature.Renaming.map (σ.reindex op p) ρ x) := by
  funext b x
  induction x using ScopedVar.map_inductionOn (σ.reindex op p) with
  | h b x => rw [reindex_map, ScopedSignature.Renaming.map_apply, reindex_map]

end Substitution

/-- A parameter action preserves variable leaves at their original positions. -/
@[expose] def ReindexAction.PreservesVars (A : σ.ReindexAction) : Prop :=
  ∀ {w : W} {a : S w} (op : σ.Op w a) (p : σ.Arg op)
    {Γ : List (S w)} {b : S w} (x : ScopedVar Γ b),
    A op p (Term.var x) = Term.var (x.map (σ.reindex op p))

namespace Term

variable {σ}

/-- Substitute value variables, reindexing images before entering fresh binders. -/
@[expose] def subst (A : σ.ReindexAction) {w : W} {Γ Δ : List (S w)} {a : S w}
    (θ : σ.Substitution Γ Δ) (t : σ.Term w Γ a) : σ.Term w Δ a :=
  t.fold (D := fun j => ∀ Δ : List (S j.1), σ.Substitution j.2.1 Δ → σ.Term j.1 Δ j.2.2)
    (fun _ x _ θ => θ x)
    (fun _ op next _ θ => .liftBind op (fun p => next p _
      (Substitution.liftMany (θ.reindex A op p) (σ.binders op p)))) Δ θ

@[simp] theorem subst_var (A : σ.ReindexAction) {w : W} {Γ Δ : List (S w)} {a : S w}
    (θ : σ.Substitution Γ Δ) (x : ScopedVar Γ a) : (var x).subst A θ = θ x := rfl

@[simp] theorem subst_node (A : σ.ReindexAction) {w : W} {Γ Δ : List (S w)} {a : S w}
    (θ : σ.Substitution Γ Δ) (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) :
    (node op args).subst A θ = node op (fun p => (args p).subst A
      (Substitution.liftMany (θ.reindex A op p) (σ.binders op p))) := rfl

/-- Substituting variables by themselves is identity for every lawful parameter action. -/
@[simp] theorem subst_id (A : σ.ReindexAction) (hA : A.PreservesVars σ)
    {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    t.subst A (fun x => var x) = t := by
  induction t using Term.inductionOn with
  | hvar w Γ a x => rfl
  | hnode w Γ a op args ih =>
      rw [subst_node]
      congr 1
      funext p
      have hr : (Substitution.reindex A
          ((fun {_} x => Term.var x) : σ.Substitution Γ Γ) op p : σ.Substitution _ _) =
          (fun {_} x => Term.var x) := by
        funext b x
        induction x using ScopedVar.map_inductionOn (σ.reindex op p) with
        | h b x => rw [Substitution.reindex_map, hA]
      have hl : (Substitution.liftMany (σ := σ)
          (Γ := Γ.map (σ.reindex op p)) (fun x => Term.var x) (σ.binders op p) :
          σ.Substitution _ _) = fun {_} x => Term.var x := by
        funext b x
        exact Substitution.liftMany_var _ x
      rw [hr, hl]
      exact ih p

/-- Substitution after value renaming equals precomposition of its images.
The law holds for every parameter action, including noninjective sort changes. -/
theorem subst_rename (A : σ.ReindexAction) {w : W} {Γ Δ Θ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (θ : σ.Substitution Δ Θ) (t : σ.Term w Γ a) :
    (t.rename ρ).subst A θ = t.subst A (fun x => θ (ρ x)) := by
  induction t using Term.inductionOn with
  | hvar => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node, subst_node]
      congr 1
      funext p
      rw [ih p]
      congr 1
      rw [Substitution.reindex_rename A ρ θ op p]
      funext b x
      exact Substitution.liftMany_rename _ _ _ x

end Term
end IPFunctor.ScopedFamily
