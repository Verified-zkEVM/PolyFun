/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Reindex

/-!
# Indexed traversals with a state at every child

A traversal changes constructors and carries an indexed state into each child.
The state can describe a renaming, a type instantiation, or a substitution;
entering a binder changes that state. Leaves may be replaced by whole trees.
Composition and interpretation laws apply independently of the binding language.

A reindexing is the traversal whose state records the translated judgment
(`Reindexing.toTraversal`); with pure leaves, traversing along it is reindexing.
-/

public section

universe uI uJ uK uA uB uC uD uE uF uR uS uX uY uZ uV

namespace IPFunctor

variable {I : Type uI} {J : Type uJ} {K : Type uK}

/-- A constructor translation carrying a possibly different state into each child. -/
structure Traversal (P : Endo.{uI, uA, uB} I) (Q : Endo.{uJ, uC, uD} J)
    (State : I → J → Type uR) where
  /-- The target constructor. -/
  op : ∀ {i j}, State i j → P.A i → Q.A j
  /-- Supply each target child from a source child. -/
  arg : ∀ {i j} (s : State i j) (a : P.A i), Q.B j (op s a) → P.B i a
  /-- State under the selected constructor argument. -/
  next : ∀ {i j} (s : State i j) (a : P.A i) (b : Q.B j (op s a)),
    State (P.src i a (arg s a b)) (Q.src j (op s a) b)

namespace Traversal

variable {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J}
  {R : Endo.{uK, uE, uF} K} {S : I → J → Type uR} {T : J → K → Type uS}

/-- Compose traversal states through an explicit intermediate judgment. -/
abbrev Composite (S : I → J → Type uR) (T : J → K → Type uS) (i : I) (k : K) :=
  (j : J) × S i j × T j k

/-- Compose constructor translations and their binder-lifting actions. -/
@[expose] def comp (f : Traversal P Q S) (g : Traversal Q R T) :
    Traversal P R (Composite S T) where
  op s a := g.op s.2.2 (f.op s.2.1 a)
  arg s a b := f.arg s.2.1 a (g.arg s.2.2 (f.op s.2.1 a) b)
  next s a b := ⟨_, f.next s.2.1 a (g.arg s.2.2 (f.op s.2.1 a) b),
    g.next s.2.2 (f.op s.2.1 a) b⟩

/-- The identity traversal transports only along equality of judgments. -/
@[expose] def identity (P : Endo.{uI, uA, uB} I) : Traversal P P (fun i j => PLift (i = j)) where
  op s a := s.down ▸ a
  arg s a b := by cases s.down; exact b
  next s a b := by cases s.down; exact ⟨rfl⟩

end Traversal

/-- A reindexing as a traversal whose state records that the target judgment is the
translated source judgment. -/
@[expose] def Reindexing.toTraversal {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J}
    {f : I → J} (h : Reindexing P Q f) : Traversal P Q (fun i j => PLift (f i = j)) where
  op s a := s.down ▸ h.op _ a
  arg s a b := by cases s.down; exact h.arg _ a b
  next s a b := by cases s.down; exact ⟨h.source _ a b⟩

/-- The identity reindexing gives the identity traversal. -/
theorem Reindexing.toTraversal_id (P : Endo.{uI, uA, uB} I) :
    (Reindexing.id P).toTraversal = Traversal.identity P := rfl

namespace IFreeM

variable {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J}
  {R : Endo.{uK, uE, uF} K} {S : I → J → Type uR} {T : J → K → Type uS}
  {X : I → Type uX} {Y : J → Type uY} {Z : K → Type uZ}

/-- Traverse finite syntax, lifting the state at binders and replacing variable leaves. -/
@[expose] protected def traverse (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j) {i j} (s : S i j)
    (t : IFreeM P X i) : IFreeM Q Y j :=
  t.fold (D := fun i => ∀ j, S i j → IFreeM Q Y j)
    (fun _ x _ s => leaf s x)
    (fun _ a next _ s => .liftBind (f.op s a)
      (fun b => next (f.arg s a b) _ (f.next s a b))) j s

@[simp] theorem traverse_pure (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j) {i j} (s : S i j) (x : X i) :
    (pure x).traverse f leaf s = leaf s x := rfl

@[simp] theorem traverse_liftBind (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j) {i j} (s : S i j)
    (a : P.A i) (next : (b : P.B i a) → IFreeM P X (P.src i a b)) :
    (liftBind a next).traverse f leaf s = .liftBind (f.op s a)
      (fun b => (next (f.arg s a b)).traverse f leaf (f.next s a b)) := rfl

/-- Successive traversals compose, including the traversals of substituted leaves. -/
theorem traverse_comp (f : Traversal P Q S) (g : Traversal Q R T)
    (leafF : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (leafG : ∀ {j k}, T j k → Y j → IFreeM R Z k)
    {i j k} (s : S i j) (r : T j k) (t : IFreeM P X i) :
    (t.traverse f leafF s).traverse g leafG r =
      t.traverse (f.comp g) (fun s x => (leafF s.2.1 x).traverse g leafG s.2.2)
        ⟨j, s, r⟩ := by
  induction t generalizing j k with
  | pure x => rfl
  | liftBind a next ih =>
      simp only [traverse_liftBind, Traversal.comp]
      congr 1
      funext b
      exact ih _ _ _

/-- An identity traversal only transports the tree to the equal target judgment. -/
@[simp] theorem traverse_identity {i j} (t : IFreeM P X i) (s : PLift (i = j)) :
    t.traverse (Traversal.identity P) (fun s x => .pure (s.down ▸ x)) s = s.down ▸ t := by
  rcases s with ⟨e⟩
  cases e
  induction t with
  | pure x => rfl
  | liftBind a next ih =>
      simp only [traverse_liftBind, Traversal.identity]
      congr 1
      exact funext ih

/-- An interpretation after traversal is a fold carrying the traversal state. -/
theorem fold_traverse {V : J → Type uV} (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (vars : ∀ j, Y j → V j) (alg : FoldAlgebra Q V)
    {i j} (s : S i j) (t : IFreeM P X i) :
    (t.traverse f leaf s).fold vars alg =
      t.fold (D := fun i => ∀ j, S i j → V j)
        (fun _ x _ s => (leaf s x).fold vars alg)
        (fun _ a next _ s => alg _ (f.op s a)
          (fun b => next (f.arg s a b) _ (f.next s a b))) j s := by
  induction t generalizing j with
  | pure x => rfl
  | liftBind a next ih =>
      simp only [traverse_liftBind, fold_liftBind, ih]

/-- Constructor-local semantic compatibility suffices for every term and lifted state. -/
theorem fold_traverse_rel {D : I → Type uZ} {V : J → Type uV} (f : Traversal P Q S)
    (leaf : ∀ {i j}, S i j → X i → IFreeM Q Y j)
    (sourceVars : ∀ i, X i → D i) (sourceAlg : FoldAlgebra P D)
    (targetVars : ∀ j, Y j → V j) (targetAlg : FoldAlgebra Q V)
    (Rel : ∀ {i j}, S i j → D i → V j → Prop)
    (hvar : ∀ {i j} (s : S i j) x,
      Rel s (sourceVars i x) ((leaf s x).fold targetVars targetAlg))
    (hnode : ∀ {i j} (s : S i j) a (ds : (b : P.B i a) → D (P.src i a b))
      (vs : (b : Q.B j (f.op s a)) → V (Q.src j (f.op s a) b)),
      (∀ b, Rel (f.next s a b) (ds (f.arg s a b)) (vs b)) →
      Rel s (sourceAlg i a ds) (targetAlg j (f.op s a) vs))
    {i j} (s : S i j) (t : IFreeM P X i) :
    Rel s (t.fold sourceVars sourceAlg) ((t.traverse f leaf s).fold targetVars targetAlg) := by
  induction t generalizing j with
  | pure x => exact hvar s x
  | liftBind a next ih =>
      simp only [traverse_liftBind, fold_liftBind]
      exact hnode s a _ _ (fun b => ih _ _)

/-- Traversing along a reindexing with pure leaves reindexes the tree and transports it
to the recorded target judgment. -/
@[simp] theorem traverse_toTraversal {f : I → J} (h : Reindexing P Q f) (leaf : ∀ i, X i → Y (f i))
    {i j} (s : PLift (f i = j)) (t : IFreeM P X i) :
    t.traverse h.toTraversal (fun s x => .pure (s.down ▸ leaf _ x)) s =
      s.down ▸ t.reindex h leaf := by
  induction t generalizing j with
  | pure x =>
      rcases s with ⟨rfl⟩
      rfl
  | liftBind a next ih =>
      rcases s with ⟨rfl⟩
      change IFreeM.liftBind (h.op _ a)
          (fun b => (next (h.arg _ a b)).traverse h.toTraversal _ ⟨h.source _ a b⟩) =
        IFreeM.liftBind (h.op _ a) (fun b => h.source _ a b ▸ (next (h.arg _ a b)).reindex h leaf)
      congr 1
      funext b
      exact ih _ _

/-- At the translated judgment itself, traversal along a reindexing is reindexing. -/
theorem traverse_toTraversal_rfl {f : I → J} (h : Reindexing P Q f)
    (leaf : ∀ i, X i → Y (f i)) {i} (t : IFreeM P X i) :
    t.traverse h.toTraversal (fun s x => .pure (s.down ▸ leaf _ x)) ⟨rfl⟩ = t.reindex h leaf :=
  traverse_toTraversal h leaf ⟨rfl⟩ t

end IFreeM
end IPFunctor
