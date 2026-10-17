/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Fold
public import PolyFun.IPFunctor.Lens.Basic

/-!
# Changing the indices of polynomial syntax

A reindexing changes both the judgment and the available constructors. The
source equation records how argument judgments change. In a typed language,
this can instantiate types as well as change the variable context.

An indexed lens between endomorphic polynomials is a reindexing along the identity
(`Lens.toReindexing`); reindexing along successive lenses is reindexing along
their composite.
-/

public section

universe uI uJ uK uA uB uC uD uE uF uX uY uZ uV

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

/-- Compose index and constructor translations, retaining the child equations. -/
@[expose] def Reindexing.comp {K : Type uK} {P : Endo.{uI, uA, uB} I}
    {Q : Endo.{uJ, uC, uD} J} {R : Endo.{uK, uE, uF} K} {f : I → J} {g : J → K}
    (h : Reindexing P Q f) (k : Reindexing Q R g) : Reindexing P R (g ∘ f) where
  op i a := k.op (f i) (h.op i a)
  arg i a b := h.arg i a (k.arg (f i) (h.op i a) b)
  source i a b := (congrArg g (h.source i a _)).trans (k.source (f i) (h.op i a) b)

namespace Lens

variable {P : Endo.{uI, uA, uB} I} {Q : Endo.{uI, uC, uD} I}

/-- A lens between endomorphic polynomials reindexes along the identity: positions
move forward, responses pull back, and `src_eq` is the child-index equation. -/
@[expose] def toReindexing (l : Lens P Q) : Reindexing P Q id where
  op := l.toFunA
  arg := l.toFunB
  source := l.src_eq

@[simp] theorem toReindexing_op (l : Lens P Q) (s : I) (a : P.A s) :
    l.toReindexing.op s a = l.toFunA s a := rfl

@[simp] theorem toReindexing_arg (l : Lens P Q) (s : I) (a : P.A s)
    (b : Q.B s (l.toFunA s a)) : l.toReindexing.arg s a b = l.toFunB s a b := rfl

/-- The identity lens reindexes by the identity reindexing. -/
@[simp] theorem toReindexing_id : (Lens.id P).toReindexing = Reindexing.id P := rfl

/-- Lens composition is reindexing composition in diagrammatic order. -/
theorem toReindexing_comp {R : Endo.{uI, uE, uF} I} (l : Lens Q R) (l' : Lens P Q) :
    (l ∘ₗ l').toReindexing = l'.toReindexing.comp l.toReindexing := rfl

end Lens

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

/-- Index transport commutes with reindexing. -/
theorem reindex_cast (h : Reindexing P Q f) (leaf : ∀ s, X s → Y (f s))
    {i j : I} (e : i = j) (t : IFreeM P X i) :
    (e ▸ t).reindex h leaf = congrArg f e ▸ t.reindex h leaf := by
  cases e
  rfl

/-- Successive changes of indices equal their composite translation. -/
theorem reindex_comp {K : Type uK} {R : Endo.{uK, uE, uF} K}
    {Z : K → Type uZ} {g : J → K} (h : Reindexing P Q f) (k : Reindexing Q R g)
    (leafH : ∀ i, X i → Y (f i)) (leafK : ∀ j, Y j → Z (g j))
    {i : I} (t : IFreeM P X i) :
    (t.reindex h leafH).reindex k leafK =
      t.reindex (h.comp k) (fun i x => leafK (f i) (leafH i x)) := by
  induction t with
  | pure x => rfl
  | liftBind a next ih =>
      simp only [reindex_liftBind, reindex_cast, ih, Reindexing.comp]
      congr 1
      funext b
      exact transport_trans _ _ _
where
  transport_trans {j k l : K} (e : j = k) (d : k = l) (t : IFreeM R Z j) :
      d ▸ (e ▸ t) = (e.trans d) ▸ t := by
    cases e
    cases d
    rfl

/-- Interpreting a transported tree transports its meaning at the same index. -/
theorem fold_cast {V : J → Type uV} (leaf : ∀ s, Y s → V s) (alg : FoldAlgebra Q V)
    {j k : J} (h : j = k) (t : IFreeM Q Y j) :
    (h ▸ t).fold leaf alg = h ▸ t.fold leaf alg := by
  cases h
  rfl

/-- Reindexing commutes with interpretation through the translated constructor algebra. -/
theorem fold_reindex {V : J → Type uV} (h : Reindexing P Q f)
    (vars : ∀ s, X s → Y (f s)) (leaf : ∀ s, Y s → V s) (alg : FoldAlgebra Q V)
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

/-! ## Reindexing along lenses -/

namespace IFreeM

variable {P : Endo.{uI, uA, uB} I} {Q : Endo.{uI, uC, uD} I} {R : Endo.{uI, uE, uF} I}
  {X : I → Type uX} {Y : I → Type uY} {Z : I → Type uZ}

/-- One constructor reindexed along a lens, stated with the lens fields. -/
theorem reindex_toReindexing_liftBind (l : Lens P Q) (leaf : ∀ s, X s → Y s) {s : I}
    (a : P.A s) (next : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a next).reindex l.toReindexing leaf = .liftBind (l.toFunA s a)
      (fun b => l.src_eq s a b ▸ (next (l.toFunB s a b)).reindex l.toReindexing leaf) := rfl

/-- Reindexing along successive lenses is reindexing along their composite. -/
@[simp] theorem reindex_toReindexing_comp (l' : Lens P Q) (l : Lens Q R)
    (leaf' : ∀ s, X s → Y s) (leaf : ∀ s, Y s → Z s) {s : I} (t : IFreeM P X s) :
    (t.reindex l'.toReindexing leaf').reindex l.toReindexing leaf =
      t.reindex (l.comp l').toReindexing (fun s x => leaf s (leaf' s x)) :=
  reindex_comp l'.toReindexing l.toReindexing leaf' leaf t

end IFreeM
end IPFunctor
