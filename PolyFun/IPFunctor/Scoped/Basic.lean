/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Fold

/-!
# Typed binding signatures and polynomial syntax

A constructor specifies a result sort and, for each argument, the sorts it
binds and the argument's result sort. Its trees use `IFreeM`: variables are
leaves, and constructor children carry their extended typing judgments.
Renaming and substitution lift under each argument's binders.
-/

public section

universe u v w

namespace IPFunctor

/-- A typed de Bruijn variable in a list of sorts. -/
inductive ScopedVar {S : Type u} : List S → S → Type u where
  | zero {Γ : List S} {a : S} : ScopedVar (a :: Γ) a
  | succ {Γ : List S} {a b : S} : ScopedVar Γ a → ScopedVar (b :: Γ) a

/-- The numerical de Bruijn index; sorts and scope membership remain in the type. -/
@[expose] def ScopedVar.index {S : Type u} {Γ : List S} {a : S} : ScopedVar Γ a → Nat
  | .zero => 0
  | .succ x => x.index + 1

/-- Change the sorts of all variables while retaining their binding positions. -/
@[expose] def ScopedVar.map {S : Type u} {T : Type v} (f : S → T) :
    {Γ : List S} → {a : S} → ScopedVar Γ a → ScopedVar (Γ.map f) (f a)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (x.map f)

@[simp] theorem ScopedVar.index_map {S : Type u} {T : Type v} (f : S → T)
    {Γ : List S} {a : S} (x : ScopedVar Γ a) : (x.map f).index = x.index := by
  induction x with
  | zero => rfl
  | succ x ih => exact congrArg (· + 1) ih

/-- A variable's numerical position determines its sort and typed occurrence. -/
theorem ScopedVar.sigma_eq_of_index_eq {S : Type u} {Γ : List S} {a b : S}
    (x : ScopedVar Γ a) (y : ScopedVar Γ b) (h : x.index = y.index) :
    (⟨a, x⟩ : (s : S) × ScopedVar Γ s) = ⟨b, y⟩ := by
  induction x generalizing b with
  | zero =>
    cases y with
    | zero => rfl
    | succ y => simp only [index] at h; omega
  | succ x ih =>
    cases y with
    | zero => simp only [index] at h; omega
    | succ y =>
      have he := ih y (Nat.add_right_cancel h)
      cases he
      rfl

/-- Constructor shapes with explicit binding information for every argument. -/
structure ScopedSignature (S : Type u) where
  /-- Constructors producing the given sort. -/
  Op : S → Type v
  /-- Argument positions of a constructor. -/
  Arg : {a : S} → Op a → Type w
  /-- Variables bound in the selected argument, nearest first. -/
  binders : {a : S} → (op : Op a) → Arg op → List S
  /-- Result sort of the selected argument. -/
  sort : {a : S} → (op : Op a) → Arg op → S

namespace ScopedSignature

variable {S : Type u}

/-- Scope and result sort, indexing the polynomial syntax. -/
abbrev Judgment (S : Type u) := List S × S

/-- The indexed polynomial associated with a binding signature. -/
@[expose, reducible] def polynomial (σ : ScopedSignature.{u, v, w} S) :
    Endo (Judgment S) where
  A j := σ.Op j.2
  B _ op := σ.Arg op
  src j op p := (σ.binders op p ++ j.1, σ.sort op p)

/-- Typed syntax, with variables at the leaves of the indexed free tree. -/
abbrev Term (σ : ScopedSignature.{u, v, w} S) (Γ : List S) (a : S) :=
  IFreeM σ.polynomial (fun j => ScopedVar j.1 j.2) (Γ, a)

/-- A sort-preserving map between variable contexts. -/
abbrev Renaming (Γ Δ : List S) := ∀ {a}, ScopedVar Γ a → ScopedVar Δ a

namespace Renaming

/-- Lift a renaming past one freshly bound variable. -/
@[expose] def lift {Γ Δ : List S} (ρ : Renaming Γ Δ) (a : S) :
    Renaming (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

/-- Lift a renaming under a list of binders. -/
@[expose] def liftMany {Γ Δ : List S} (ρ : Renaming Γ Δ) :
    (Ξ : List S) → Renaming (Ξ ++ Γ) (Ξ ++ Δ)
  | [] => ρ
  | a :: Ξ => lift (liftMany ρ Ξ) a

@[simp] theorem liftMany_nil {Γ Δ : List S} (ρ : Renaming Γ Δ)
    {a : S} (x : ScopedVar Γ a) : ρ.liftMany [] x = ρ x := rfl

@[simp] theorem liftMany_cons {Γ Δ : List S} (ρ : Renaming Γ Δ)
    (b : S) (Ξ : List S) {a : S} (x : ScopedVar (b :: Ξ ++ Γ) a) :
    ρ.liftMany (b :: Ξ) x = lift (liftMany ρ Ξ) b x := rfl

end Renaming

namespace Term

variable {σ : ScopedSignature.{u, v, w} S} {Γ Δ Θ : List S} {a : S}

/-- A variable occurrence. -/
@[expose, match_pattern] def var (x : ScopedVar Γ a) : σ.Term Γ a := .pure x

/-- A constructor with typed arguments in their extended contexts. -/
@[expose, match_pattern] def node (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    σ.Term Γ a := .liftBind op args

/-- Structural induction with each child's extended context explicit. -/
@[elab_as_elim] protected theorem inductionOn
    {C : ∀ (Γ : List S) (a : S), σ.Term Γ a → Prop}
    (hvar : ∀ Γ a (x : ScopedVar Γ a), C Γ a (var x))
    (hnode : ∀ Γ a (op : σ.Op a)
      (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)),
      (∀ p, C _ _ (args p)) → C Γ a (node op args))
    (t : σ.Term Γ a) : C Γ a t :=
  IFreeM.inductionOn (C := fun j t => C j.1 j.2 t)
    (fun j => hvar j.1 j.2) (fun j => hnode j.1 j.2) t

/-- Capture-avoiding renaming, lifting the variable map under each child scope. -/
@[expose] def rename {Γ Δ : List S} {a : S}
    (ρ : Renaming Γ Δ) (t : σ.Term Γ a) : σ.Term Δ a :=
  t.fold (D := fun j => ∀ {Δ}, Renaming j.1 Δ → σ.Term Δ j.2)
    (fun _ x {_} ρ => .pure (ρ x))
    (fun _ op next {_} ρ => .liftBind op
      (fun p => next p (Renaming.liftMany ρ (σ.binders op p)))) ρ

@[simp] theorem rename_var (ρ : Renaming Γ Δ) (x : ScopedVar Γ a) :
    (var (σ := σ) x).rename ρ = var (ρ x) := rfl

@[simp] theorem rename_node (ρ : Renaming Γ Δ) (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (node op args).rename ρ = node op
      (fun p => (args p).rename (ρ.liftMany (σ.binders op p))) := rfl

/-- Embed a term below one fresh binder. -/
@[expose] def weaken (t : σ.Term Γ a) (b : S) : σ.Term (b :: Γ) a :=
  t.rename ScopedVar.succ

end Term

/-- A simultaneous substitution, preserving each variable's sort. -/
abbrev Substitution (σ : ScopedSignature.{u, v, w} S) (Γ Δ : List S) :=
  ∀ {a}, ScopedVar Γ a → σ.Term Δ a

namespace Substitution

variable {σ : ScopedSignature.{u, v, w} S} {Γ Δ : List S}

/-- Extend a substitution with a fresh variable, weakening all older images. -/
@[expose] def lift (θ : σ.Substitution Γ Δ) (a : S) :
    σ.Substitution (a :: Γ) (a :: Δ)
  | _, .zero => .pure .zero
  | _, .succ x => (θ x).weaken a

/-- Lift a substitution through all binders of one constructor argument. -/
@[expose] def liftMany (θ : σ.Substitution Γ Δ) :
    (Ξ : List S) → σ.Substitution (Ξ ++ Γ) (Ξ ++ Δ)
  | [] => θ
  | a :: Ξ => lift (liftMany θ Ξ) a

end Substitution

namespace Term

variable {σ : ScopedSignature.{u, v, w} S} {Γ Δ : List S} {a : S}

/-- Capture-avoiding simultaneous substitution. -/
@[expose] def subst {Γ Δ : List S} {a : S}
    (θ : σ.Substitution Γ Δ) (t : σ.Term Γ a) : σ.Term Δ a :=
  t.fold (D := fun j => ∀ {Δ}, σ.Substitution j.1 Δ → σ.Term Δ j.2)
    (fun _ x {_} θ => θ x)
    (fun _ op next {_} θ => .liftBind op
      (fun p => next p (Substitution.liftMany θ (σ.binders op p)))) θ

@[simp] theorem subst_var (θ : σ.Substitution Γ Δ) (x : ScopedVar Γ a) :
    (var (σ := σ) x).subst θ = θ x := rfl

@[simp] theorem subst_node (θ : σ.Substitution Γ Δ) (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (node op args).subst θ = node op
      (fun p => (args p).subst (θ.liftMany (σ.binders op p))) := rfl

end Term
end ScopedSignature
end IPFunctor
