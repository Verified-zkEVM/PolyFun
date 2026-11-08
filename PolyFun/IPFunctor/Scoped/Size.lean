/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Description size of finitely branching scoped terms

Count every variable and operation once. Bound syntax bodies are counted as
stored descriptions, independently of how often an interpretation executes
them. This is a syntax measure, not a bound on evaluation time or output size.
-/

public section

universe u v w

namespace IPFunctor.ScopedSignature.Term

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S}
  [∀ {a} (op : σ.Op a), Fintype (σ.Arg op)]

/-- Number of variables and constructor occurrences in a finite-branching term. -/
@[expose] def nodeCount {Γ : List S} {a : S} (t : σ.Term Γ a) : Nat :=
  t.fold (D := fun _ => Nat) (fun _ _ => 1) (fun _ _ next => 1 + ∑ p, next p)

@[simp] theorem nodeCount_var {Γ : List S} {a : S} (x : ScopedVar Γ a) :
    (var (σ := σ) x).nodeCount = 1 := rfl

@[simp] theorem nodeCount_node {Γ : List S} {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) :
    (node op args).nodeCount = 1 + ∑ p, (args p).nodeCount := rfl

end IPFunctor.ScopedSignature.Term
