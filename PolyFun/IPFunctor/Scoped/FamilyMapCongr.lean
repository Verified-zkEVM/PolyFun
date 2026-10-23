/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMap

/-!
# Congruence of binding-family maps

Constructor translations with related parameter states act identically on finite
syntax when they select the same children and preserve the relation under binders.
The result uses heterogeneous equality to retain arbitrary context transports.
-/

public section

namespace IPFunctor.ScopedFamily.Term

universe u v w z
variable {W : Type u} {S : W → Type v} {σ : ScopedFamily.{u, v, w, z} W S}

/-- Equal constructor heads and children give equal trees across transported judgments. -/
theorem node_heq {a b : W} {Γ : List (S a)} {Δ : List (S b)}
    {s : S a} {t : S b} {op : σ.Op a s} {op' : σ.Op b t}
    (hw : a = b) (hc : HEq Γ Δ) (hs : HEq s t) (ho : HEq op op')
    (args : (p : σ.Arg op) → σ.Term (σ.world op p)
      (σ.binders op p ++ Γ.map (σ.reindex op p)) (σ.sort op p))
    (args' : (p : σ.Arg op') → σ.Term (σ.world op' p)
      (σ.binders op' p ++ Δ.map (σ.reindex op' p)) (σ.sort op' p))
    (hargs : ∀ p q, HEq p q → HEq (args p) (args' q)) :
    HEq (node op args) (node op' args') := by
  cases hw
  cases eq_of_heq hc
  cases eq_of_heq hs
  cases eq_of_heq ho
  exact heq_of_eq (congrArg (node op) (funext (fun p => eq_of_heq (hargs p p HEq.rfl))))
end IPFunctor.ScopedFamily.Term

namespace IPFunctor.ScopedFamily.Term

universe u v w z m n
variable {W : Type u} {S : W → Type v}
  {σ τ : ScopedFamily.{u, v, w, z} W S}
  {M : W → W → Type m} {N : W → W → Type n}
  {f : ∀ {a b}, M a b → S a → S b} {g : ∀ {a b}, N a b → S a → S b}

/-- A relation preserved by constructor and child maps identifies their whole-term actions. -/
theorem map_congr (h : Hom σ τ M f) (k : Hom σ τ N g)
    (R : ∀ {a b c}, M a b → N a c → Prop)
    (hw : ∀ {a b c} {μ : M a b} {ν : N a c}, R μ ν → b = c)
    (hf : ∀ {a b c} {μ : M a b} {ν : N a c}, R μ ν → HEq (f μ) (g ν))
    (ho : ∀ {a b c} {μ : M a b} {ν : N a c}, R μ ν →
      ∀ {s} (op : σ.Op a s), HEq (h.op μ op) (k.op ν op))
    (hp : ∀ {a b c} {μ : M a b} {ν : N a c}, R μ ν →
      ∀ {s} (op : σ.Op a s) (p : τ.Arg (h.op μ op)) (q : τ.Arg (k.op ν op)),
      HEq p q → h.arg μ op p = k.arg ν op q)
    (hn : ∀ {a b c} {μ : M a b} {ν : N a c} (hr : R μ ν)
      {s} (op : σ.Op a s) (p : τ.Arg (h.op μ op)) (q : τ.Arg (k.op ν op))
      (he : HEq p q),
      R (h.next μ op p) ((congrArg (fun p => σ.world op p) (hp hr op p q he)).symm ▸
        k.next ν op q))
    {a b c} {μ : M a b} {ν : N a c} (hr : R μ ν)
    {Γ : List (S a)} {s : S a} (t : σ.Term a Γ s) :
    HEq (t.map h μ) (t.map k ν) := by
  induction t using Term.inductionOn generalizing b c with
  | hvar a Γ s x =>
    cases hw hr
    have hh := eq_of_heq (hf hr)
    simp only [map_var]
    exact leaf_congr x hh
  | hnode a Γ s op args ih =>
    simp only [map_node]
    have hctx : HEq (Γ.map (f μ)) (Γ.map (g ν)) := by
      cases hw hr
      exact heq_of_eq (congrArg (List.map · Γ) (eq_of_heq (hf hr)))
    have hsort : HEq (f μ s) (g ν s) := by
      cases hw hr
      exact heq_of_eq (congrFun (eq_of_heq (hf hr)) s)
    apply node_heq (hw hr) hctx hsort (ho hr op)
    intro p q he
    apply (cast_heq _ _ _).trans
    apply HEq.trans ?_ (cast_heq _ _ _).symm
    have hr' := hn hr op p q he
    have he' := hp hr op p q he
    have step (p' q' : σ.Arg op) (e : p' = q') {b c : W}
        (μ' : M (σ.world op p') b) (ν' : N (σ.world op q') c)
        (hr' : R μ' ((congrArg (σ.world op) e).symm ▸ ν')) :
        HEq ((args p').map h μ') ((args q').map k ν') := by
      cases e
      exact ih p' hr'
    exact step _ _ he' _ _ hr'
where
  leaf_congr {a b : W} {Γ : List (S a)} {s : S a} (x : ScopedVar Γ s)
      {F G : S a → S b} (he : F = G) :
      HEq (var (σ := τ) (x.map F)) (var (σ := τ) (x.map G)) := by
    cases he
    rfl
end IPFunctor.ScopedFamily.Term
