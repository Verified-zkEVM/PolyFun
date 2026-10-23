/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic
public import PolyFun.IPFunctor.Free.Reindex

/-!
# Reindexing binding signatures

Changing sorts translates the context, result type, and each argument's new
binders together. The resulting term map is the generic indexed-tree
reindexing. It preserves binding positions even when the sort map is not
injective, as can happen when instantiating type variables.
-/

public section

universe u v w u' v' w'

namespace IPFunctor.ScopedSignature

variable {S : Type u} {T : Type u'}

/-- A constructor map compatible with a change of sorts and binding scopes. -/
structure Hom (σ : ScopedSignature.{u, v, w} S) (τ : ScopedSignature.{u', v', w'} T)
    (f : S → T) where
  /-- Translate a constructor. -/
  op : {a : S} → σ.Op a → τ.Op (f a)
  /-- Supply each target argument from an original argument. -/
  arg : ∀ {a} (o : σ.Op a), τ.Arg (op o) → σ.Arg o
  /-- Translate every newly bound sort in its original order. -/
  binders : ∀ {a} (o : σ.Op a) p,
    (σ.binders o (arg o p)).map f = τ.binders (op o) p
  /-- Translate the result sort of each argument. -/
  sort : ∀ {a} (o : σ.Op a) p, f (σ.sort o (arg o p)) = τ.sort (op o) p

variable {σ : ScopedSignature.{u, v, w} S} {τ : ScopedSignature.{u', v', w'} T} {f : S → T}

/-- Translate the context and result sort of a typing judgment. -/
@[expose, reducible] def mapJudgment (f : S → T) (j : Judgment S) : Judgment T :=
  (j.1.map f, f j.2)

/-- A binding-signature homomorphism gives an indexed-polynomial reindexing. -/
@[expose] def Hom.toReindexing (h : Hom σ τ f) :
    Reindexing σ.polynomial τ.polynomial (mapJudgment f) where
  op _ o := h.op o
  arg _ o p := h.arg o p
  source j o p := by
    apply Prod.ext
    · change (σ.binders o (h.arg o p) ++ j.1).map f = _
      rw [List.map_append, h.binders]
    · exact h.sort o p

/-- Instantiate or translate all sorts in a term without changing variable positions. -/
@[expose] def Term.map (h : Hom σ τ f) {Γ : List S} {a : S}
    (t : σ.Term Γ a) : τ.Term (Γ.map f) (f a) :=
  t.reindex h.toReindexing (fun _ x => x.map f)

@[simp] theorem Term.map_var (h : Hom σ τ f) {Γ : List S} {a : S} (x : ScopedVar Γ a) :
    (Term.var (σ := σ) x).map h = Term.var (x.map f) := rfl

end IPFunctor.ScopedSignature
