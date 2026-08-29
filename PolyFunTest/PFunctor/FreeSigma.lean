/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Sigma

/-!
# Indexed-family free-program canaries

These examples pin both the operation and result tags of sigma-family packing,
including a family whose answer type genuinely depends on its index.
-/

@[expose] public section

universe uI uA uB uX uY

namespace PolyFunTest.FreeSigma

open PFunctor
open PFunctor.FreeM

inductive FamilyIx where
  | bit
  | trit

def FamilyAnswer : FamilyIx → Type
  | .bit => Bool
  | .trit => Fin 3

def familyP (i : FamilyIx) : PFunctor.{0, 0} :=
  ⟨PUnit, fun _ => FamilyAnswer i⟩

def familyProgram (i : FamilyIx) : PUnit → FreeM (familyP i) ((familyP i).B PUnit.unit) :=
  fun _ => FreeM.lift PUnit.unit

/-- Packing retains the selected index on both the query and its dependent
returned answer. -/
example (i : FamilyIx) :
    packFamily familyProgram ⟨i, PUnit.unit⟩ =
      FreeM.liftBind (P := PFunctor.sigma familyP) ⟨i, PUnit.unit⟩
        (fun answer => pure ⟨i, answer⟩) :=
  rfl

/-- The API does not identify the index, interface, input, and output
universes. -/
example {I : Type uI} {P : I → PFunctor.{uA, uB}}
    {X : I → Type uX} {Y : I → Type uY}
    (program : (i : I) → X i → FreeM (P i) (Y i))
    (i : I) (input : X i) :
    packFamily program ⟨i, input⟩ = sigmaInj i (program i input) :=
  rfl

end PolyFunTest.FreeSigma
