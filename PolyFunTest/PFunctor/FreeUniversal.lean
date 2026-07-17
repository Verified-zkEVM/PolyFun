/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Universal
public import PolyFunTest.PFunctor.FreePolynomial
public import PolyFunTest.PFunctor.SubstMonoid

/-!
# Regression tests for the free substitution-monoid universal property

The tests make multiplication order observable in the word monoid, exercise
both inverse directions of the hom-lens equivalence, and pin the independent
position/direction universes of the construction.
-/

@[expose] public section

universe uA uB

namespace PFunctor
namespace FreeUniversalTest

open SubstMonoidTest
open FreePolynomialTest

/-- A unary bit-operation signature. -/
abbrev bitUnary : PFunctor := ⟨Bool, fun _ => PUnit⟩

/-- Interpret each bit operation as the corresponding one-letter word. -/
def bitToWord : Lens bitUnary wordP :=
  (fun bit => [bit]) ⇆ (fun _ _ => PUnit.unit)

/-- A two-node tree whose outer and inner labels are distinct. -/
def twoBits : (FreeP bitUnary).A :=
  .liftBind false fun _ =>
    .liftBind true fun _ => .pure PUnit.unit

/-- The universal fold respects outer-before-inner substitution order. -/
example : (FreeP.extend wordMonoid bitToWord).toLens.toFunA twoBits =
    [false, true] :=
  rfl

/-- Bind in the extension monad has the same observable order. -/
example :
    let outer : SubstMonoid.Extension wordMonoid Bool :=
      ⟨[false], fun _ => true⟩
    (outer >>= fun bit =>
      (⟨[bit], fun _ => PUnit.unit⟩ :
        SubstMonoid.Extension wordMonoid PUnit)).1 = [false, true] :=
  rfl

/-- Restricting the universal extension returns the exact generator lens. -/
example : FreeP.restrict wordMonoid (FreeP.extend wordMonoid bitToWord) =
    bitToWord :=
  FreeP.restrict_extend wordMonoid bitToWord

/-- The other roundtrip holds for an arbitrary homomorphism, not only the
homomorphism constructed immediately above. -/
example (f : SubstMonoid.Hom (FreeP.substMonoid bitUnary) wordMonoid) :
    FreeP.extend wordMonoid (FreeP.restrict wordMonoid f) = f :=
  FreeP.extend_restrict wordMonoid f

/-- The packaged equivalence exposes both inverse laws. -/
example : (FreeP.homEquiv wordMonoid).symm
    ((FreeP.homEquiv wordMonoid) (FreeP.extend wordMonoid bitToWord)) =
      FreeP.extend wordMonoid bitToWord :=
  (FreeP.homEquiv wordMonoid).symm_apply_apply _

/-- The homomorphism packaging uses the already established `FreeP.map`
lens, including its backward path action. -/
example : (FreeP.mapHom reverseBranchLens).toLens =
    FreeP.map reverseBranchLens :=
  rfl

def oneBinaryNode : (FreeP binaryP).A :=
  .liftBind false fun _ => .pure PUnit.unit

/-- Runtime branch `false` is pulled back to source branch `true`; this checks
the nontrivial backward component, not only the mapped shape. -/
example : (FreeP.mapHom reverseBranchLens).toLens.toFunB oneBinaryNode
    ⟨false, ⟨⟩⟩ = ⟨true, ⟨⟩⟩ :=
  rfl

/-- The polynomial fold is definitionally the existing `FreeM.liftM` fold on
the path-labelled computation. -/
example (s : (FreeP bitUnary).A) :
    FreeP.foldObjAt wordMonoid bitToWord s id =
      FreeM.liftM (FreeP.extensionHandler wordMonoid bitToWord)
        (FreeP.decodeAt s id) :=
  rfl

/-- Position and direction universes remain independent throughout the
universal construction. -/
example (P : PFunctor.{uA, uB})
    (M : SubstMonoid.{max uA uB, uB}) (l : Lens P M.carrier) :
    SubstMonoid.Hom (FreeP.substMonoid P) M :=
  FreeP.extend M l

end FreeUniversalTest
end PFunctor
