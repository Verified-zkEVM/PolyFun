/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Transport
public import PolyFun.IPFunctor.Free.Traversal

/-!
# Binding signatures over changing parameter contexts

Each child can enter a different parameter context, reindex the types of existing
variables, and bind new value variables. The resulting finite syntax is an indexed
free polynomial tree. Ordinary binding signatures are the constant-context case.
-/

public section

universe u v w z

namespace IPFunctor

/-- Constructor arguments may change the parameter context and extend the value scope. -/
structure ScopedFamily (W : Type u) (S : W → Type v) where
  /-- Constructor heads at a parameter context and result sort. -/
  Op : (w : W) → S w → Type w
  /-- Recursive argument positions. -/
  Arg : {w : W} → {a : S w} → Op w a → Type z
  /-- The parameter context of an argument. -/
  world : {w : W} → {a : S w} → (op : Op w a) → Arg op → W
  /-- Reindex existing variable sorts into the argument's parameter context. -/
  reindex : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) → S w → S (world op p)
  /-- Additional value variables, nearest first. -/
  binders : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) → List (S (world op p))
  /-- The argument's result sort. -/
  sort : {w : W} → {a : S w} → (op : Op w a) → (p : Arg op) → S (world op p)

namespace ScopedFamily

variable {W : Type u} {S : W → Type v}

/-- Parameter context, value context, and result sort. -/
abbrev Judgment (S : W → Type v) := (w : W) × List (S w) × S w

/-- The polynomial associated with a context-changing binding signature. -/
@[expose, reducible] def polynomial (σ : ScopedFamily.{u, v, w, z} W S) :
    Endo (Judgment S) where
  A j := σ.Op j.1 j.2.2
  B _ op := σ.Arg op
  src j op p := ⟨σ.world op p,
    σ.binders op p ++ j.2.1.map (σ.reindex op p), σ.sort op p⟩

/-- Finite syntax with typed variables at the leaves. -/
abbrev Term (σ : ScopedFamily.{u, v, w, z} W S) (w : W) (Γ : List (S w)) (a : S w) :=
  IFreeM σ.polynomial (fun j => ScopedVar j.2.1 j.2.2) ⟨w, Γ, a⟩

namespace Term

variable {σ : ScopedFamily.{u, v, w, z} W S}

/-- A variable occurrence in its parameter and value contexts. -/
@[expose, match_pattern] def var {w : W} {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : σ.Term w Γ a := .pure x

/-- A constructor whose children enter their prescribed contexts. -/
@[expose, match_pattern] def node {w : W} {Γ : List (S w)} {a : S w} (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) : σ.Term w Γ a :=
  .liftBind op args

/-- Structural induction, retaining the changing parameter context in the motive. -/
@[elab_as_elim] protected theorem inductionOn
    {C : ∀ w Γ a, σ.Term w Γ a → Prop}
    (hvar : ∀ w Γ a (x : ScopedVar Γ a), C w Γ a (var x))
    (hnode : ∀ w Γ a (op : σ.Op w a)
      (args : (p : σ.Arg op) → σ.Term (σ.world op p)
        (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)),
      (∀ p, C _ _ _ (args p)) → C w Γ a (node op args))
    {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) : C w Γ a t :=
  IFreeM.inductionOn (C := fun j t => C j.1 j.2.1 j.2.2 t)
    (fun j => hvar j.1 j.2.1 j.2.2) (fun j => hnode j.1 j.2.1 j.2.2) t

/-- Renaming follows value binders and reindexes old variable positions at parameter binders. -/
@[expose] def rename {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (t : σ.Term w Γ a) : σ.Term w Δ a :=
  t.fold (D := fun j => ∀ Δ : List (S j.1),
      ScopedSignature.Renaming j.2.1 Δ → σ.Term j.1 Δ j.2.2)
    (fun _ x _ ρ => .pure (ρ x))
    (fun _ op next _ ρ => .liftBind op (fun p => next p _
      (ScopedSignature.Renaming.liftMany
        (ScopedSignature.Renaming.map (σ.reindex op p) ρ) (σ.binders op p)))) Δ ρ

@[simp] theorem rename_var {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (x : ScopedVar Γ a) :
    (var (σ := σ) x).rename ρ = var (ρ x) := rfl

@[simp] theorem rename_node {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) :
    (node op args).rename ρ = node op (fun p => (args p).rename
      (ScopedSignature.Renaming.liftMany (ScopedSignature.Renaming.map
        (σ.reindex op p) ρ) (σ.binders op p))) := rfl

/-- Identity renaming remains identity under parameter-context changes. -/
@[simp] theorem rename_id {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) :
    t.rename (fun x => x) = t := by
  induction t using Term.inductionOn with
  | hvar w Γ a x => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node, ScopedSignature.Renaming.map_id]
      congr 1
      funext p
      have h : (ScopedSignature.Renaming.liftMany
          (Γ := Γ.map (σ.reindex op p)) (fun x => x) (σ.binders op p) :
          ScopedSignature.Renaming _ _) = fun {_} x => x := by
        funext a x
        exact ScopedSignature.Renaming.liftMany_id _ x
      rw [h]
      exact ih p

/-- Renaming composition commutes with every parameter and value binder. -/
theorem rename_rename {w : W} {Γ Δ Θ : List (S w)} {a : S w} (t : σ.Term w Γ a)
    (ρ : ScopedSignature.Renaming Γ Δ) (τ : ScopedSignature.Renaming Δ Θ) :
    (t.rename ρ).rename τ = t.rename (fun x => τ (ρ x)) := by
  induction t using Term.inductionOn with
  | hvar w Γ a x => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node]
      congr 1
      funext p
      rw [ih p]
      congr 1
      funext a x
      rw [ScopedSignature.Renaming.map_comp (σ.reindex op p) ρ τ]
      exact (ScopedSignature.Renaming.liftMany_comp _ _ _ x).symm

end Term
end ScopedFamily
end IPFunctor
