/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Lens.Cartesian

/-!
# Indexed families of finite free programs

This file packages an indexed family of `FreeM` programs over possibly
different polynomial interfaces as one program over their indexed coproduct.
Both queries and returned values retain their family index. The construction is
purely syntactic and makes no uniformity, termination, or complexity claim.
-/

@[expose] public section

universe uI uA uB uX uY

namespace PFunctor.FreeM

variable {I : Type uI} {P : I → PFunctor.{uA, uB}}
  {X : I → Type uX} {Y : I → Type uY}

/-- Inject one member of an indexed family into the free monad over the
indexed coproduct, tagging both its operations and returned values by the
fixed family index. -/
def sigmaInj (i : I) (program : FreeM (P i) (X i)) :
    FreeM (PFunctor.sigma P) (Σ i, X i) :=
  FreeM.map (Sigma.mk i) <| program.mapLens (Lens.sigmaInj (F := P) i)

@[simp]
theorem sigmaInj_pure (i : I) (value : X i) :
    sigmaInj (P := P) i (pure value) = pure ⟨i, value⟩ :=
  rfl

@[simp]
theorem sigmaInj_liftBind (i : I) (position : (P i).A)
    (next : (P i).B position → FreeM (P i) (X i)) :
    sigmaInj i ((FreeM.lift position).bind next) =
      FreeM.liftBind (P := PFunctor.sigma P) ⟨i, position⟩
        (fun direction => sigmaInj i (next direction)) :=
  rfl

/-- Package an indexed family of programs as one program family over the
indexed coproduct interface. A single dependent input selects the member, and
the returned value carries the same index. -/
def packFamily (program : (i : I) → X i → FreeM (P i) (Y i)) :
    (Σ i, X i) → FreeM (PFunctor.sigma P) (Σ i, Y i)
  | ⟨i, input⟩ => sigmaInj i (program i input)

@[simp]
theorem packFamily_mk (program : (i : I) → X i → FreeM (P i) (Y i))
    (i : I) (input : X i) :
    packFamily program ⟨i, input⟩ = sigmaInj i (program i input) :=
  rfl

end PFunctor.FreeM
