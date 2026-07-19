/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Polynomial

/-!
# Regression tests for the free polynomial monad

These examples distinguish leaf labels, node order, path splitting, and the
backward direction of a nontrivial generator lens. They also pin the
independence of source and target position/direction universes.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace FreePolynomialTest

/-- A binary-branching signature whose operation positions are also bits. -/
abbrev binaryP : PFunctor := ⟨Bool, fun _ => Bool⟩

def binaryLeaf : FreeM binaryP PUnit :=
  .pure PUnit.unit

def binaryOp (label : Bool) : FreeM binaryP PUnit :=
  .liftBind label fun _ => binaryLeaf

/-- Four distinct payloads make both an outer and an inner binary direction
observable. -/
def branchPayload (outer inner : Bool) : Nat :=
  match outer, inner with
  | false, false => 3
  | false, true => 5
  | true, false => 7
  | true, true => 11

/-- Three binary substitution layers with independently observable path
components. -/
def binaryTriple : ((FreeP binaryP ◃ FreeP binaryP) ◃ FreeP binaryP).A :=
  ⟨⟨binaryOp false, fun _ => binaryOp true⟩,
    fun _ => binaryOp false⟩

/-- A binary tree with distinguishable payloads at its two leaves. -/
def labelledBinaryTree : FreeM binaryP Nat :=
  .liftBind false fun branch => .pure (if branch then 7 else 3)

/-- Encoding records the payload at the `false` branch. -/
example : (FreeP.encode labelledBinaryTree).2 ⟨false, ⟨⟩⟩ = 3 :=
  rfl

/-- Encoding records a different payload at the `true` branch. -/
example : (FreeP.encode labelledBinaryTree).2 ⟨true, ⟨⟩⟩ = 7 :=
  rfl

/-- The packaged polynomial equivalence reconstructs the original branching
tree, not only its erased shape. -/
example : FreeP.objEquiv (FreeP.encode labelledBinaryTree) =
    labelledBinaryTree :=
  rfl

/-- A unary-operation signature used to make grafting order observable. -/
abbrev unaryP : PFunctor := ⟨Bool, fun _ => PUnit⟩

def leaf : FreeM unaryP PUnit :=
  .pure PUnit.unit

def op (label : Bool) (next : FreeM unaryP PUnit) :
    FreeM unaryP PUnit :=
  .liftBind label fun _ => next

/-- Three nested substitution layers with three distinguishable operation
labels. -/
def triple : ((FreeP unaryP ◃ FreeP unaryP) ◃ FreeP unaryP).A :=
  ⟨⟨op false leaf, fun _ => op true leaf⟩,
    fun _ => op false leaf⟩

/-- Left-associated multiplication preserves outer-to-inner node order. -/
example : (FreeP.multAssocLeft (P := unaryP)).toFunA triple =
    op false (op true (op false leaf)) :=
  rfl

/-- Right-associated multiplication computes the same ordered tree. -/
example : (FreeP.multAssocRight (P := unaryP)).toFunA triple =
    op false (op true (op false leaf)) :=
  rfl

/-- Splitting the unique path through a two-node graft recovers one path from
each substitution layer. -/
example :
    (FreeP.mult (P := unaryP)).toFunB
      ⟨op false leaf, fun _ => op true leaf⟩
      ⟨PUnit.unit, PUnit.unit, ⟨⟩⟩ =
    ⟨⟨PUnit.unit, ⟨⟩⟩, ⟨PUnit.unit, ⟨⟩⟩⟩ :=
  rfl

/-- Splitting must preserve both nontrivial branch choices; a unary signature
would not detect swapping or duplicating the outer and inner components. -/
example :
    (FreeP.mult (P := binaryP)).toFunB
      ⟨binaryOp false, fun _ => binaryOp true⟩
      ⟨false, true, ⟨⟩⟩ =
    ⟨⟨false, ⟨⟩⟩, ⟨true, ⟨⟩⟩⟩ :=
  rfl

/-- A two-layer labelled free polynomial whose inner operation label is the
outer direction and whose payload observes both path components. -/
def nestedBinaryObj : (FreeP binaryP ◃ FreeP binaryP).Obj Nat :=
  ⟨⟨binaryOp false, fun outerPath => binaryOp outerPath.1⟩,
    fun paths => branchPayload paths.1.1 paths.2.1⟩

/-- `nest` preserves the outer tree while decoding each direction-indexed
inner tree, including its operation label and both payload indices. -/
example : FreeP.decode (FreeP.nest nestedBinaryObj) =
    FreeM.liftBind false (fun outer =>
      FreeM.pure (FreeM.liftBind outer (fun inner =>
        FreeM.pure (branchPayload outer inner)))) :=
  rfl

/-- Decoding multiplication joins the same nested computation in
outer-then-inner order. Reversing the two path components changes either the
inner operation label or one of the four leaf payloads. -/
example :
    FreeP.decode
        (Lens.mapObj (FreeP.mult (P := binaryP)) nestedBinaryObj) =
      FreeM.liftBind false (fun outer =>
        FreeM.liftBind outer (fun inner =>
          FreeM.pure (branchPayload outer inner))) :=
  rfl

/-- Left-associated multiplication reassociates all three path components
without permuting them. -/
example :
    (FreeP.multAssocLeft (P := binaryP)).toFunB binaryTriple
      ⟨false, true, false, ⟨⟩⟩ =
    ⟨⟨⟨false, ⟨⟩⟩, ⟨true, ⟨⟩⟩⟩, ⟨false, ⟨⟩⟩⟩ :=
  rfl

/-- The right-associated composite has the same observable reassociation of
three nontrivial path components. -/
example :
    (FreeP.multAssocRight (P := binaryP)).toFunB binaryTriple
      ⟨false, true, false, ⟨⟩⟩ =
    ⟨⟨⟨false, ⟨⟩⟩, ⟨true, ⟨⟩⟩⟩, ⟨false, ⟨⟩⟩⟩ :=
  rfl

/-- A target signature with natural-number operation labels. -/
abbrev natBinaryP : PFunctor := ⟨Nat, fun _ => Bool⟩

/-- Map bit positions to `0`/`1`, while reversing the runtime branch returned
to the source tree. -/
def reverseBranchLens : Lens binaryP natBinaryP :=
  (fun label => if label then 1 else 0) ⇆ (fun _ branch => !branch)

def controlTree : FreeM binaryP PUnit :=
  .liftBind false fun branch =>
    .liftBind branch fun _ => .pure PUnit.unit

/-- A labelled control tree whose second operation and leaf payload both
depend on the directions pulled back through `reverseBranchLens`. -/
def labelledControlTree : FreeM binaryP Nat :=
  .liftBind false fun outer =>
    .liftBind outer fun inner =>
      .pure (branchPayload outer inner)

/-- Decoding `FreeP.map` observes both parts of the nontrivial lens: positions
are mapped to naturals and each runtime direction is reversed before selecting
the next operation and final payload. -/
example :
    FreeP.decode
        (Lens.mapObj (FreeP.map reverseBranchLens)
          (FreeP.encode labelledControlTree)) =
      FreeM.liftBind (P := natBinaryP) 0 (fun outer =>
        FreeM.liftBind (P := natBinaryP) (if !outer then 1 else 0) (fun inner =>
          FreeM.pure (branchPayload (!outer) (!inner)))) :=
  rfl

/-- The backward lens direction is observable: runtime `false` selects the
source `true` child (label `1`), while runtime `true` selects label `0`. -/
example : FreeP.mapShape reverseBranchLens controlTree =
    (FreeM.liftBind (P := natBinaryP) 0 (fun branch =>
      FreeM.liftBind (if branch then 0 else 1) fun _ =>
        FreeM.pure PUnit.unit) : FreeM natBinaryP PUnit) := by
  apply congrArg (FreeM.liftBind (P := natBinaryP) 0)
  funext branch
  cases branch <;> rfl

/-- The mapped polynomial's backward component itself reverses both runtime
branch choices. This pins path pullback directly, rather than observing it
only through the mapped tree shape. -/
example : (FreeP.map reverseBranchLens).toFunB controlTree
    ⟨false, true, ⟨⟩⟩ = ⟨true, false, ⟨⟩⟩ :=
  rfl

/-- Mapping `FreeP` does not couple source and target position or direction
universes. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (l : Lens P Q) : Lens (FreeP P) (FreeP Q) :=
  FreeP.map l

/-- Composition preservation also keeps all three signature universe pairs
independent. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) (l₁ : Lens P Q) (l₂ : Lens Q R) :
    FreeP.map l₂ ∘ₗ FreeP.map l₁ = FreeP.map (l₂ ∘ₗ l₁) :=
  FreeP.map_comp l₂ l₁

/-- The constructed carrier exposes all substitution-monoid laws. -/
example (P : PFunctor.{uA, uB}) :
    Lens.comp
      (Lens.comp (FreeP.substMonoid P).mult
        (Lens.compMap (FreeP.substMonoid P).unit
          (Lens.id (FreeP.substMonoid P).carrier)))
      Lens.Equiv.XComp.invLens =
    Lens.id (FreeP.substMonoid P).carrier :=
  (FreeP.substMonoid P).unit_left

end FreePolynomialTest
end PFunctor
