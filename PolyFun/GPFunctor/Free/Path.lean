/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Free.Basic
public import PolyFun.PFunctor.Free.Path

/-!
# Path-Product Soundness of the Grade Index

The grade of a `GFreeM` tree lives in its *type*; after grade erasure only the plain tree
remains, but the grading of the underlying container still assigns each root-to-leaf path a
product of shape grades. This file shows the two agree:

* `pathProd` — the product of shape grades along a canonical
  [`PFunctor.FreeM.Path`](../../PFunctor/Free/Path.lean) of a plain tree over the
  underlying container;
* `GFreeM.pathProd_erase` — for a tree of type-level grade `g`, *every* root-to-leaf path
  of the erased plain tree has grade product `g`;
* `GFreeM.pathProd_eq_pathProd` — consequently the grade product is path-invariant on
  erased trees: the grade index is exactly the (well-defined) path product.

This is the semantic soundness of the grade index: the type-level grade is not an arbitrary
annotation but the runtime cost along every execution path.
-/

@[expose] public section

universe uG uA uB v

namespace GPFunctor

variable {G : Type uG} [Monoid G] {P : GPFunctor.{uG, uA, uB} G} {α : Type v}

/-- The product of the shape grades along a canonical root-to-leaf path of a plain tree
over the underlying container of a graded polynomial. -/
def pathProd (P : GPFunctor.{uG, uA, uB} G) [Monoid G] {α : Type v} :
    (s : P.toPFunctor.FreeM α) → PFunctor.FreeM.Path s → G
  | .pure _, _ => 1
  | .roll a rest, ⟨b, p⟩ => P.grade a * pathProd P (rest b) p

@[simp]
lemma pathProd_pure (x : α)
    (p : PFunctor.FreeM.Path (PFunctor.FreeM.pure (P := P.toPFunctor) x)) :
    pathProd P (PFunctor.FreeM.pure x) p = 1 := rfl

@[simp]
lemma pathProd_roll (a : P.A) (rest : P.B a → P.toPFunctor.FreeM α)
    (b : P.B a) (p : PFunctor.FreeM.Path (rest b)) :
    pathProd P (PFunctor.FreeM.roll a rest) ⟨b, p⟩ =
      P.grade a * pathProd P (rest b) p := rfl

namespace GFreeM

/-- **Path-product soundness** of the grade index: a grade-`g` tree erases to a plain tree
whose every root-to-leaf path has grade product exactly `g`. -/
theorem pathProd_erase {g : G} (x : GFreeM P g α) (p : PFunctor.FreeM.Path x.erase) :
    pathProd P x.erase p = g := by
  induction x using GFreeM.inductionOn with
  | pure x => exact rfl
  | roll g a r ih =>
    obtain ⟨b, p⟩ := p
    exact congrArg (P.grade a * ·) (ih b p)

/-- The grade product is path-invariant on erased trees: any two root-to-leaf paths of the
same erased graded tree have the same grade product. -/
theorem pathProd_eq_pathProd {g : G} (x : GFreeM P g α)
    (p q : PFunctor.FreeM.Path x.erase) :
    pathProd P x.erase p = pathProd P x.erase q :=
  (pathProd_erase x p).trans (pathProd_erase x q).symm

end GFreeM

end GPFunctor
