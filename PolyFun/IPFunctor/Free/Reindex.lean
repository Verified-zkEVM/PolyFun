/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Fold

/-!
# Changing the indices of polynomial syntax

A reindexing changes both the judgment and the available constructors. The
source equation records how argument judgments change. In a typed language,
this can instantiate types as well as change the variable context.
-/

public section

universe uI uJ uA uB uC uD uX uY uV

namespace IPFunctor

variable {I : Type uI} {J : Type uJ}

/-- A polynomial map whose source and target may use different index types. -/
structure Reindexing (P : Endo.{uI, uA, uB} I) (Q : Endo.{uJ, uC, uD} J)
    (f : I → J) where
  /-- Translate each constructor at the translated index. -/
  op : ∀ s, P.A s → Q.A (f s)
  /-- Supply each target argument from a source argument. -/
  arg : ∀ s a, Q.B (f s) (op s a) → P.B s a
  /-- Argument indices agree with the change of judgment. -/
  source : ∀ s a b, f (P.src s a (arg s a b)) = Q.src (f s) (op s a) b

/-- Leave indices, constructors, and arguments unchanged. -/
@[expose] def Reindexing.id (P : Endo.{uI, uA, uB} I) : Reindexing P P id where
  op _ a := a
  arg _ _ b := b
  source _ _ _ := rfl

namespace IFreeM

variable {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J} {f : I → J}
  {X : I → Type uX} {Y : J → Type uY}

/-- Translate an indexed tree, retaining its variables through an explicit leaf map. -/
@[expose] protected def reindex (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    {s : I} (t : IFreeM P X s) : IFreeM Q Y (f s) :=
  t.fold (D := fun s => IFreeM Q Y (f s)) (fun s x => .pure (leaf s x))
    (fun s a next => .liftBind (h.op s a) (fun b => h.source s a b ▸ next (h.arg s a b)))

@[simp] theorem reindex_pure (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).reindex h leaf = .pure (leaf s x) := rfl

@[simp] theorem reindex_liftBind (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    {s : I} (a : P.A s) (next : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a next).reindex h leaf = .liftBind (h.op s a)
      (fun b => h.source s a b ▸ (next (h.arg s a b)).reindex h leaf) := rfl

@[simp] theorem reindex_id {s : I} (t : IFreeM P X s) :
    t.reindex (Reindexing.id P) (fun _ x => x) = t := by
  induction t with
  | pure x => rfl
  | liftBind a next ih =>
    simp only [reindex_liftBind, Reindexing.id]
    congr 1
    exact funext ih

/-- Interpreting a transported tree transports its meaning at the same index. -/
theorem fold_cast {V : J → Type uV} (leaf : ∀ s, Y s → V s) (alg : Algebra Q V)
    {j k : J} (h : j = k) (t : IFreeM Q Y j) :
    (h ▸ t).fold leaf alg = h ▸ t.fold leaf alg := by
  cases h
  rfl

/-- Reindexing commutes with interpretation through the translated constructor algebra. -/
theorem fold_reindex {V : J → Type uV} (h : Reindexing P Q f)
    (vars : ∀ s, X s → Y (f s)) (leaf : ∀ s, Y s → V s) (alg : Algebra Q V)
    {s : I} (t : IFreeM P X s) :
    (t.reindex h vars).fold leaf alg =
      t.fold (fun s x => leaf (f s) (vars s x))
        (fun s a next => alg (f s) (h.op s a)
          (fun b => h.source s a b ▸ next (h.arg s a b))) := by
  induction t with
  | pure x => rfl
  | liftBind a next ih =>
    simp only [reindex_liftBind, fold_liftBind, fold_cast, ih]

end IFreeM
end IPFunctor
