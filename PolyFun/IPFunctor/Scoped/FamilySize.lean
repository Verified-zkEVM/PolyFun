/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Family
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Description size under parameter binders

Each stored variable and constructor counts once, regardless of how many times
an interpretation instantiates its body. Constructor payloads are labels and are
not included in this count. No evaluation-time bound follows from this measure.
-/

public section

universe u v w z

namespace IPFunctor.ScopedFamily.Term

variable {W : Type u} {S : W → Type v} {σ : ScopedFamily.{u, v, w, z} W S}
  [∀ {w a} (op : σ.Op w a), Fintype (σ.Arg op)]

/-- Count variables and constructor nodes in the stored finite tree. -/
@[expose] def nodeCount {w : W} {Γ : List (S w)} {a : S w} (t : σ.Term w Γ a) : Nat :=
  t.fold (D := fun _ => Nat) (fun _ _ => 1) (fun _ _ next => 1 + ∑ p, next p)

@[simp] theorem nodeCount_var {w : W} {Γ : List (S w)} {a : S w} (x : ScopedVar Γ a) :
    (var (σ := σ) x).nodeCount = 1 := rfl

@[simp] theorem nodeCount_node {w : W} {Γ : List (S w)} {a : S w} (op : σ.Op w a)
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p)) :
    (node op args).nodeCount = 1 + ∑ p, (args p).nodeCount := rfl

/-- Value renaming preserves description size across both sorts of binders. -/
theorem nodeCount_rename {w : W} {Γ Δ : List (S w)} {a : S w}
    (ρ : ScopedSignature.Renaming Γ Δ) (t : σ.Term w Γ a) :
    (t.rename ρ).nodeCount = t.nodeCount := by
  induction t using Term.inductionOn with
  | hvar => rfl
  | hnode w Γ a op args ih =>
      simp only [rename_node, nodeCount_node]
      congr 1
      exact Finset.sum_congr rfl (fun p _ => ih p _)

end IPFunctor.ScopedFamily.Term
