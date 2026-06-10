/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import PolyFun.GPFunctor.Free.Indexed
public import PolyFun.GPFunctor.Free.MapGrade
public import PolyFun.GPFunctor.Free.Path
public import PolyFun.GPFunctor.Lens.Basic

/-!
# Worked Examples for `GPFunctor` and `GPFunctor.GFreeM`

This module is a worked-examples companion to
[`docs/wiki/gpfunctor.md`](../../docs/wiki/gpfunctor.md). It gives the graded surface
concrete uses that compile inside the library.

The running example is a cost-graded signature over `Multiplicative ℕ` (so grades multiply
exactly when costs add): a `tick` operation of cost `1` returning `Unit`, and a `query`
operation of cost `2` returning a `ℕ`. The examples exercise:

* building programs with `gbind` / `GFreeM.liftA`, with the total cost read off the *type*;
* `gcast` transport to a normalized grade — definitional over a concrete monoid;
* the `bind_liftA` cast collapse and the transparent nested-`roll` normal form;
* interpretation: `GFreeM.mapGM` into another free graded monad and `GFreeM.mapM` into `Id`;
* the forgetful maps `GFreeM.erase` (to `PFunctor.FreeM`) and `GFreeM.toFreeM₂` (to the
  accumulated-grade `IPFunctor.FreeM₂` over `cost.toIPFunctor`);
* a grade-preserving `GPFunctor.Lens` and its induced `IPFunctor.Lens`;
* program transport along the lens (`GFreeM.mapLens`) and its naturality in `erase` and
  `toFreeM₂`;
* grade reindexing along a `MonoidHom` (`GFreeM.mapGrade`), with cost doubling as the
  running homomorphism;
* path-product soundness: every root-to-leaf path of the erased program has grade product
  the type-level total cost (`pathProd`, `GFreeM.pathProd_erase`);
* injectivity of the translation over the cancellative `Multiplicative ℕ`
  (`GFreeM.toFreeM₂_injective`) and the full equivalence over the group `Multiplicative ℤ`
  (`GFreeM.equivFreeM₂`).
-/

@[expose] public section

namespace GPFunctor.Examples

/-! ## Cost-graded fixture -/

/-- The operations of the cost-graded signature. -/
inductive CostOp where
  /-- A unit-cost step returning nothing. -/
  | tick
  /-- A cost-two query returning a `ℕ`. -/
  | query
deriving DecidableEq, Inhabited

/-- The cost-graded signature: `tick` at cost `1`, `query` at cost `2`. Grades live in
`Multiplicative ℕ`, so sequencing multiplies grades exactly when it adds costs. -/
@[expose] def cost : GPFunctor (Multiplicative ℕ) where
  A := CostOp
  B
    | .tick  => Unit
    | .query => ℕ
  grade
    | .tick  => Multiplicative.ofAdd 1
    | .query => Multiplicative.ofAdd 2

/-- `tick` as a one-step program, at its own grade. -/
@[expose] def tick : GFreeM cost (Multiplicative.ofAdd 1) Unit :=
  GFreeM.liftA (P := cost) CostOp.tick

/-- `query` as a one-step program, at its own grade. -/
@[expose] def query : GFreeM cost (Multiplicative.ofAdd 2) ℕ :=
  GFreeM.liftA (P := cost) CostOp.query

/-! ## Programs: the type carries the total cost -/

/-- One `tick`, then two `query`s, summing the responses. The grade in the type is the
unnormalized product accumulated by `gbind` — multiplicatively `1 * (2 * (2 * 1))`, i.e.
total cost `5`. -/
@[expose] def run :
    GFreeM cost (Multiplicative.ofAdd 1 * (Multiplicative.ofAdd 2 *
      (Multiplicative.ofAdd 2 * 1))) ℕ :=
  gbind tick fun _ => gbind query fun a => gbind query fun b => gpure (a + b)

/-- The same program transported to the normalized total cost `5`. Over a concrete monoid
the grade arithmetic is definitional, so the transport is along a `rfl`-provable equation. -/
@[expose] def run' : GFreeM cost (Multiplicative.ofAdd 5) ℕ :=
  gcast rfl run

/-- Binding a lifted shape is `roll` on the nose (`bind_liftA`); over the concrete monoid
the collapse is definitional. -/
example : gbind tick (fun _ => query) = GFreeM.roll CostOp.tick (fun _ => query) := rfl

/-- The whole program unfolds to a transparent nested `roll` tree: every cast introduced by
`liftA` and `gbind` collapses definitionally over `Multiplicative ℕ`. -/
example :
    run = GFreeM.roll (P := cost) CostOp.tick (fun _ =>
      GFreeM.roll (P := cost) CostOp.query (fun a : ℕ =>
        GFreeM.roll (P := cost) CostOp.query (fun b : ℕ =>
          GFreeM.pure (a + b)))) := rfl

/-! ## Interpretation -/

/-- A coarser cost-graded signature: a single `spend n` operation for each `n`, at grade
`n`, returning nothing. -/
@[expose] def spend : GPFunctor (Multiplicative ℕ) where
  A := ℕ
  B _ := Unit
  grade n := Multiplicative.ofAdd n

/-- Interpret the `cost` signature into the free graded monad on `spend`: each operation
becomes a `spend` of its own cost, with `query` answering `0`. Grade-matching is enforced by
`mapGM`'s type, and the interpretation is cast-free. -/
@[expose] def runSpend :
    GFreeM spend (Multiplicative.ofAdd 1 * (Multiplicative.ofAdd 2 *
      (Multiplicative.ofAdd 2 * 1))) ℕ :=
  run.mapGM (P := cost) (m := GFreeM spend) fun
    | .tick  => GFreeM.liftA (P := spend) (1 : ℕ)
    | .query => GFreeM.map (fun _ => (0 : ℕ)) (GFreeM.liftA (P := spend) (2 : ℕ))

/-- Interpret into the ordinary `Id` monad, dropping grades: `query` answers `21`, so the
program computes `21 + 21`. -/
example :
    run.mapM (P := cost) (m := Id)
      (fun | .tick => pure () | .query => pure (21 : ℕ)) = 42 := rfl

/-! ## Forgetful maps -/

/-- Grade erasure lands in the plain free monad over the underlying container. -/
example :
    run'.erase = PFunctor.FreeM.roll (P := cost.toPFunctor) CostOp.tick (fun _ =>
      PFunctor.FreeM.roll CostOp.query (fun a : ℕ =>
        PFunctor.FreeM.roll CostOp.query (fun b : ℕ =>
          PFunctor.FreeM.pure (a + b)))) := rfl

/-- A one-step translation into the accumulated-grade two-index free monad: the tree starts
at accumulator `1` and every leaf carries a witness that the accumulated grade is the total
`Multiplicative.ofAdd 2`. -/
example :
    GFreeM.toFreeM₂ query =
      IPFunctor.FreeM₂.roll (P := cost.toIPFunctor) CostOp.query (fun n =>
        IPFunctor.FreeM₂.pureCast (one_mul (Multiplicative.ofAdd 2)) n) := rfl

/-! ## Morphisms -/

/-- The grade-preserving lens collapsing `cost` onto `spend`: each operation maps to a
`spend` of its own cost, and responses pull back trivially (`query`'s pulled-back response
is `0`). `grade_eq` closes by `rfl` per shape. -/
@[expose] def costToSpend : Lens cost spend where
  toFunA
    | .tick  => (1 : ℕ)
    | .query => (2 : ℕ)
  toFunB
    | .tick,  _ => ()
    | .query, _ => (0 : ℕ)
  grade_eq a := by cases a <;> rfl

/-- The induced indexed lens between the accumulated-grade indexed images: the source-index
preservation law is grade preservation under left multiplication. -/
@[expose] def costToSpendIP : IPFunctor.Lens cost.toIPFunctor spend.toIPFunctor :=
  costToSpend.toIPLens

/-! ## Program transport along the lens -/

/-- Transporting the whole program along the lens preserves the grade: the type still
carries total cost `5` (unnormalized). -/
@[expose] def runSpendLens :
    GFreeM spend (Multiplicative.ofAdd 1 * (Multiplicative.ofAdd 2 *
      (Multiplicative.ofAdd 2 * 1))) ℕ :=
  run.mapLens costToSpend

/-- Transport commutes with grade erasure: transport the graded tree and erase, or erase
and transport the plain tree along the induced plain lens. -/
example : (run.mapLens costToSpend).erase = run.erase.mapLens costToSpend.toPLens :=
  GFreeM.erase_mapLens costToSpend run

/-- Transport commutes with the accumulated-grade translation, along the induced indexed
lens. -/
example : GFreeM.toFreeM₂ (run.mapLens costToSpend) =
    (GFreeM.toFreeM₂ run).mapLens costToSpendIP :=
  GFreeM.toFreeM₂_mapLens costToSpend run

/-! ## Grade reindexing -/

/-- Cost doubling as a monoid homomorphism on `Multiplicative ℕ`: squaring multiplies
additive costs by two. -/
@[expose] def doubleCost : Multiplicative ℕ →* Multiplicative ℕ where
  toFun n := n * n
  map_one' := rfl
  map_mul' a b := mul_mul_mul_comm a b a b

/-- Reindexing `query` along the doubling homomorphism: cost `2` becomes cost `4`, read
off the type. Over the concrete monoid the normalization is definitional. -/
@[expose] def queryDoubled :
    GFreeM (cost.mapGrade doubleCost) (Multiplicative.ofAdd 4) ℕ :=
  gcast rfl (query.mapGrade doubleCost)

/-- Reindexing is invisible to grade erasure: the underlying plain tree is unchanged. -/
example : (run.mapGrade doubleCost).erase = run.erase :=
  GFreeM.erase_mapGrade doubleCost run

/-! ## Path-product soundness -/

/-- Every root-to-leaf path of the erased program has grade product exactly the type-level
total cost `5`. -/
example (p : PFunctor.FreeM.Path run'.erase) :
    pathProd cost run'.erase p = Multiplicative.ofAdd 5 :=
  GFreeM.pathProd_erase run' p

/-! ## Cancellativity and the group case -/

/-- Over the cancellative monoid `Multiplicative ℕ`, the accumulated-grade translation is
injective: a program is recoverable from its indexed translation. -/
example : Function.Injective
    (GFreeM.toFreeM₂ (P := cost) (g := Multiplicative.ofAdd 5) (α := ℕ)) :=
  GFreeM.toFreeM₂_injective

/-- A signed-cost signature over the group `Multiplicative ℤ`: spend or refund `n`. -/
@[expose] def spendRefund : GPFunctor (Multiplicative ℤ) where
  A := ℤ
  B _ := Unit
  grade n := Multiplicative.ofAdd n

/-- Over a group, graded trees and accumulated-grade indexed trees are the same data. -/
example (g : Multiplicative ℤ) :
    GFreeM spendRefund g ℕ ≃ IPFunctor.FreeM₂ spendRefund.toIPFunctor 1 g ℕ :=
  GFreeM.equivFreeM₂ g

end GPFunctor.Examples
