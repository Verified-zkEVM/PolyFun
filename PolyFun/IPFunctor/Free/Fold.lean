/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Family

/-!
# Algebras and relational folds for indexed free trees

A fold algebra consumes every child meaning at its own index. Unlike an effect
handler, it need not choose a single response. Function-valued carriers can
delay evaluation of children, including children under language binders.
The name `FoldAlgebra` leaves Mathlib's `Algebra` unshadowed under `open IPFunctor`.
-/

public section

universe uI uA uB uX uD uE

namespace IPFunctor

variable {I : Type uI} (P : Endo.{uI, uA, uB} I)

/-- An indexed algebra interpreting one constructor and its child meanings. -/
abbrev FoldAlgebra (D : I → Type uD) :=
  ∀ s (a : P.A s), ((b : P.B s a) → D (P.src s a b)) → D s

namespace IFreeM

variable {P} {X : I → Type uX} {D : I → Type uD} {E : I → Type uE}

/-- Interpret all nodes of a finite indexed tree in an algebra. -/
@[expose] protected def fold (leaf : ∀ s, X s → D s) (alg : FoldAlgebra P D) :
    {s : I} → IFreeM P X s → D s
  | _, .pure x => leaf _ x
  | _, .liftBind a next => alg _ a (fun b => (next b).fold leaf alg)

@[simp] theorem fold_pure (leaf : ∀ s, X s → D s) (alg : FoldAlgebra P D)
    {s : I} (x : X s) : (IFreeM.pure (P := P) x).fold leaf alg = leaf s x := rfl

@[simp] theorem fold_liftBind (leaf : ∀ s, X s → D s) (alg : FoldAlgebra P D)
    {s : I} (a : P.A s) (next : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a next).fold leaf alg =
      alg s a (fun b => (next b).fold leaf alg) := rfl

/-- Related leaves and constructors give related whole-tree interpretations. -/
theorem fold_rel (R : ∀ s, D s → E s → Prop)
    (leafD : ∀ s, X s → D s) (leafE : ∀ s, X s → E s)
    (algD : FoldAlgebra P D) (algE : FoldAlgebra P E)
    (hleaf : ∀ s x, R s (leafD s x) (leafE s x))
    (halg : ∀ s a ds es, (∀ b, R (P.src s a b) (ds b) (es b)) →
      R s (algD s a ds) (algE s a es)) {s : I} (t : IFreeM P X s) :
    R s (t.fold leafD algD) (t.fold leafE algE) := by
  induction t with
  | pure x => exact hleaf _ x
  | liftBind a next ih => exact halg _ a _ _ ih

/-- A homomorphism of algebras commutes with their whole-tree folds. -/
theorem fold_fusion (f : ∀ s, D s → E s)
    (leafD : ∀ s, X s → D s) (leafE : ∀ s, X s → E s)
    (algD : FoldAlgebra P D) (algE : FoldAlgebra P E)
    (hleaf : ∀ s x, f s (leafD s x) = leafE s x)
    (halg : ∀ s a ds, f s (algD s a ds) =
      algE s a (fun b => f (P.src s a b) (ds b)))
    {s : I} (t : IFreeM P X s) : f s (t.fold leafD algD) = t.fold leafE algE := by
  apply fold_rel (fun s d e => f s d = e) leafD leafE algD algE hleaf _ t
  intro s a ds es h
  rw [halg]
  congr 1
  exact funext h

/-- The algebra fold is determined by its equations on leaves and constructors. -/
theorem fold_unique (leaf : ∀ s, X s → D s) (alg : FoldAlgebra P D)
    (f : ∀ s, IFreeM P X s → D s)
    (hpure : ∀ s x, f s (.pure x) = leaf s x)
    (hnode : ∀ s a next, f s (.liftBind a next) =
      alg s a (fun b => f (P.src s a b) (next b)))
    {s : I} (t : IFreeM P X s) : f s t = t.fold leaf alg := by
  induction t with
  | pure x => exact hpure _ x
  | liftBind a next ih =>
    rw [hnode, fold_liftBind]
    congr 1
    exact funext ih

end IFreeM
end IPFunctor
