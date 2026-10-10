/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Family

/-!
# Parameter substitutions for binding families

A family homomorphism supplies constructor-local compatibility with changing
parameter contexts. Its finite-tree action is an indexed traversal, so generic
traversal fusion and relational interpretation laws apply to it.
-/

public section

universe u v w z m

namespace IPFunctor.ScopedFamily

variable {W : Type u} {S : W → Type v}

/-- A constructor translation that lifts its parameter map at each child. -/
structure Hom (σ τ : ScopedFamily.{u, v, w, z} W S)
    (M : W → W → Type m) (f : ∀ {w z}, M w z → S w → S z) where
  /-- Translate a constructor's head. -/
  op : ∀ {w z} (μ : M w z) {a}, σ.Op w a → τ.Op z (f μ a)
  /-- Select the original child supplying each target child. -/
  arg : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a), τ.Arg (op μ o) → σ.Arg o
  /-- Lift the parameter map into each recursive argument. -/
  next : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    M (σ.world o (arg μ o p)) (τ.world (op μ o) p)
  /-- Preserve the positions and translated sorts of freshly bound variables. -/
  binders : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    (σ.binders o (arg μ o p)).map (f (next μ o p)) = τ.binders (op μ o) p
  /-- Parameter substitution commutes with entering the child's context. -/
  reindex : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)) (b : S w),
    f (next μ o p) (σ.reindex o (arg μ o p) b) = τ.reindex (op μ o) p (f μ b)
  /-- Preserve each child's translated result sort. -/
  sort : ∀ {w z} (μ : M w z) {a} (o : σ.Op w a) (p : τ.Arg (op μ o)),
    f (next μ o p) (σ.sort o (arg μ o p)) = τ.sort (op μ o) p

/-- A parameter map together with the local context and result it transports. -/
inductive MapState (M : W → W → Type m) (f : ∀ {w z}, M w z → S w → S z) :
    Judgment S → Judgment S → Type (max u v m) where
  | mk {w z} (μ : M w z) (Γ : List (S w)) (a : S w) :
      MapState M f ⟨w, Γ, a⟩ ⟨z, Γ.map (f μ), f μ a⟩

namespace Hom

variable {σ τ : ScopedFamily.{u, v, w, z} W S}
  {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}

/-- Assemble the local context equations into an indexed traversal. -/
@[expose] def toTraversal (h : Hom σ τ M f) :
    Traversal σ.polynomial τ.polynomial (MapState M f) where
  op s o := match s with
    | .mk μ _ _ => h.op μ o
  arg s o p := match s with
    | .mk μ _ _ => h.arg μ o p
  next s o p := by
    cases s with
    | @mk w z μ Γ a =>
        have hc : (σ.binders o (h.arg μ o p) ++ Γ.map (σ.reindex o (h.arg μ o p))).map
            (f (h.next μ o p)) = τ.binders (h.op μ o) p ++
              (Γ.map (f μ)).map (τ.reindex (h.op μ o) p) := by
          rw [List.map_append, h.binders, List.map_map, List.map_map]
          congr 1
          apply List.map_congr_left
          intro b _
          exact h.reindex μ o p b
        have he : (⟨τ.world (h.op μ o) p,
            (σ.binders o (h.arg μ o p) ++ Γ.map (σ.reindex o (h.arg μ o p))).map
              (f (h.next μ o p)), f (h.next μ o p) (σ.sort o (h.arg μ o p))⟩ : Judgment S) =
            τ.polynomial.src ⟨z, Γ.map (f μ), f μ a⟩ (h.op μ o) p := by
          exact congrArg (fun q => (⟨τ.world (h.op μ o) p, q⟩ : Judgment S))
            (Prod.ext hc (h.sort μ o p))
        exact he ▸ MapState.mk (h.next μ o p) _ _

/-- Translate variable leaves by their original positions. -/
@[expose] def leaf {i j : Judgment S} (s : MapState M f i j) (x : ScopedVar i.2.1 i.2.2) :
    IFreeM τ.polynomial (fun j => ScopedVar j.2.1 j.2.2) j :=
  match s with
  | .mk μ _ _ => .pure (x.map (f μ))

end Hom

/-- Substitute parameters in finite syntax using the language's constructor laws. -/
@[expose] def Term.map {σ τ : ScopedFamily.{u, v, w, z} W S}
    {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}
    (h : Hom σ τ M f) {w z : W} (μ : M w z) {Γ : List (S w)} {a : S w}
    (t : σ.Term w Γ a) : τ.Term z (Γ.map (f μ)) (f μ a) :=
  t.traverse h.toTraversal Hom.leaf (.mk μ Γ a)

@[simp] theorem Term.map_var {σ τ : ScopedFamily.{u, v, w, z} W S}
    {M : W → W → Type m} {f : ∀ {w z}, M w z → S w → S z}
    (h : Hom σ τ M f) {w z : W} (μ : M w z) {Γ : List (S w)} {a : S w}
    (x : ScopedVar Γ a) : (var x).map h μ = var (x.map (f μ)) := rfl

end IPFunctor.ScopedFamily
