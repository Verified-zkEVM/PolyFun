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
  induction Ξ generalizing a with
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
  induction Ξ generalizing a with
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

/-- Parameter transport commutes with changing value-variable positions. -/
@[expose] def ReindexAction.PreservesRenaming (A : σ.ReindexAction) : Prop :=
  ∀ {w : W} {a : S w} (op : σ.Op w a) (p : σ.Arg op)
    {Γ Δ : List (S w)} {b : S w} (ρ : ScopedSignature.Renaming Γ Δ)
    (t : σ.Term w Γ b),
    A op p (t.rename ρ) = (A op p t).rename (ScopedSignature.Renaming.map
      (σ.reindex op p) ρ)

namespace Substitution

variable {σ} {w : W} {Γ Δ Θ : List (S w)}

/-- Renaming substitution images commutes with protecting one binder. -/
theorem lift_postrename (θ : σ.Substitution Γ Δ) (ρ : ScopedSignature.Renaming Δ Θ)
    (b : S w) {a : S w} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => (θ x).rename ρ) b x =
      (lift θ b x).rename (ScopedSignature.Renaming.lift ρ b) := by
  cases x with
  | zero => rfl
  | succ x => simp only [lift, Term.rename_rename, ScopedSignature.Renaming.lift]

/-- Renaming substitution images commutes with protecting a block of binders. -/
theorem liftMany_postrename (θ : σ.Substitution Γ Δ)
    (ρ : ScopedSignature.Renaming Δ Θ) (Ξ : List (S w))
    {a : S w} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => (θ x).rename ρ) Ξ x =
      (liftMany θ Ξ x).rename (ScopedSignature.Renaming.liftMany ρ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
      change lift (liftMany (fun x => (θ x).rename ρ) Ξ) b x = _
      have h : (liftMany (fun x => (θ x).rename ρ) Ξ : σ.Substitution _ _) =
          fun {_} x => (liftMany θ Ξ x).rename (ScopedSignature.Renaming.liftMany ρ Ξ) := by
        funext a x
        exact ih x
      rw [h, lift_postrename]
      rfl

/-- Reindexing and renaming substitution images commute under a compatible action. -/
theorem reindex_postrename (A : σ.ReindexAction) (hA : A.PreservesRenaming σ)
    (θ : σ.Substitution Γ Δ) (ρ : ScopedSignature.Renaming Δ Θ)
    {a : S w} (op : σ.Op w a) (p : σ.Arg op) :
    (reindex A (fun x => (θ x).rename ρ) op p : σ.Substitution _ _) =
      fun {_} x => (reindex A θ op p x).rename
        (ScopedSignature.Renaming.map (σ.reindex op p) ρ) := by
  funext b x
  induction x using ScopedVar.map_inductionOn (σ.reindex op p) with
  | h b x => rw [reindex_map, reindex_map, hA]

end Substitution

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

/-- Renaming a substituted term renames each substitution image. -/
theorem rename_subst (A : σ.ReindexAction) (hA : A.PreservesRenaming σ)
    {w : W} {Γ Δ Θ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (θ : σ.Substitution Γ Δ) (ρ : ScopedSignature.Renaming Δ Θ) :
    (t.subst A θ).rename ρ = t.subst A (fun x => (θ x).rename ρ) := by
  induction t using Term.inductionOn with
  | hvar => rfl
  | hnode w Γ a op args ih =>
      simp only [subst_node, rename_node]
      congr 1
      funext p
      rw [ih p, Substitution.reindex_postrename A hA]
      congr 1
      funext b x
      exact (Substitution.liftMany_postrename _ _ _ x).symm

end Term

/-- Parameter transport commutes with simultaneous value substitution. -/
@[expose] def ReindexAction.PreservesSubstitution (A : σ.ReindexAction) : Prop :=
  ∀ {w : W} {a : S w} (op : σ.Op w a) (p : σ.Arg op)
    {Γ Δ : List (S w)} {b : S w} (θ : σ.Substitution Γ Δ) (t : σ.Term w Γ b),
    A op p (t.subst A θ) = (A op p t).subst A (θ.reindex A op p)

/-- The compatibility needed for the usual capture-avoiding substitution algebra.
These laws are explicit assumptions on the language's parameter action. -/
structure ReindexAction.Lawful (A : σ.ReindexAction) : Prop where
  /-- Variables retain their binding positions. -/
  vars : A.PreservesVars σ
  /-- Value renaming commutes with parameter transport. -/
  rename : A.PreservesRenaming σ
  /-- Value substitution commutes with parameter transport. -/
  subst : A.PreservesSubstitution σ

namespace Substitution

variable {σ} {w : W} {Γ Δ Θ : List (S w)}

theorem lift_comp (A : σ.ReindexAction) (hA : A.PreservesRenaming σ)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) (b : S w)
    {a : S w} (x : ScopedVar (b :: Γ) a) :
    lift (fun x => (θ x).subst A τ) b x = (lift θ b x).subst A (lift τ b) := by
  cases x with
  | zero => rfl
  | succ x =>
      simp only [lift, Term.rename_subst A hA, Term.subst_rename]

theorem liftMany_comp (A : σ.ReindexAction) (hA : A.PreservesRenaming σ)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) (Ξ : List (S w))
    {a : S w} (x : ScopedVar (Ξ ++ Γ) a) :
    liftMany (fun x => (θ x).subst A τ) Ξ x =
      (liftMany θ Ξ x).subst A (liftMany τ Ξ) := by
  induction Ξ generalizing a with
  | nil => rfl
  | cons b Ξ ih =>
      change lift (liftMany (fun x => (θ x).subst A τ) Ξ) b x = _
      have h : (liftMany (fun x => (θ x).subst A τ) Ξ : σ.Substitution _ _) =
          fun {_} x => (liftMany θ Ξ x).subst A (liftMany τ Ξ) := by
        funext a x
        exact ih x
      rw [h, lift_comp A hA]
      rfl

theorem reindex_comp (A : σ.ReindexAction) (hA : A.PreservesSubstitution σ)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ)
    {a : S w} (op : σ.Op w a) (p : σ.Arg op) :
    (reindex A (fun x => (θ x).subst A τ) op p : σ.Substitution _ _) =
      fun {_} x => (reindex A θ op p x).subst A (reindex A τ op p) := by
  funext b x
  induction x using ScopedVar.map_inductionOn (σ.reindex op p) with
  | h b x => rw [reindex_map, reindex_map, hA]

/-- Extend a substitution by an image for the nearest binding position. -/
@[expose] def cons {a : S w} (θ : σ.Substitution Γ Δ) (value : σ.Term w Δ a) :
    σ.Substitution (a :: Γ) Δ
  | _, .zero => value
  | _, .succ x => θ x

end Substitution

namespace Term

variable {σ}

/-- Successive substitutions compose for a lawful parameter action. -/
theorem subst_subst (A : σ.ReindexAction) (hA : A.Lawful σ)
    {w : W} {Γ Δ Θ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (θ : σ.Substitution Γ Δ) (τ : σ.Substitution Δ Θ) :
    (t.subst A θ).subst A τ = t.subst A (fun x => (θ x).subst A τ) := by
  induction t using Term.inductionOn with
  | hvar => rfl
  | hnode w Γ a op args ih =>
      simp only [subst_node]
      congr 1
      funext p
      rw [ih p, Substitution.reindex_comp A hA.subst]
      congr 1
      funext b x
      exact (Substitution.liftMany_comp A hA.rename _ _ _ x).symm

/-- Substitute the nearest variable and retain the surrounding context. -/
@[expose] def substOne (A : σ.ReindexAction) {w : W} {Γ : List (S w)} {a b : S w}
    (body : σ.Term w (a :: Γ) b) (value : σ.Term w Γ a) : σ.Term w Γ b :=
  body.subst A (Substitution.cons (fun x => var x) value)

/-- Closing a body commutes with entering its nearest binder. -/
theorem substOne_subst_lift (A : σ.ReindexAction) (hA : A.Lawful σ)
    {w : W} {Γ Δ : List (S w)} {a b : S w} (body : σ.Term w (a :: Γ) b)
    (θ : σ.Substitution Γ Δ) (value : σ.Term w Δ a) :
    (body.subst A (Substitution.lift θ a)).substOne A value =
      body.subst A (Substitution.cons θ value) := by
  rw [substOne, subst_subst A hA]
  congr 1
  funext b x
  cases x with
  | zero => rfl
  | succ x =>
      simp only [Substitution.lift, subst_rename, Substitution.cons]
      exact subst_id A hA.vars (θ x)

end Term
end IPFunctor.ScopedFamily
