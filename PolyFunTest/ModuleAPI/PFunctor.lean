/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
import PolyFun.PFunctor.Free.Basic

/-!
# Ordinary-import canaries for the polynomial-functor API

These examples pin generic laws used by VCVio through ordinary imports, so
their availability does not accidentally depend on imported implementation
bodies.
-/

@[expose] public section

universe u v w uA uB uA₂ uB₂ uα uβ

namespace PolyFunTest.ModuleAPI.PFunctor

open _root_.PFunctor

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} (lens : Lens P Q) (position : P.A)
    (next : P.B position → FreeM P α) :
    FreeM.mapLens lens (FreeM.liftBind position next) =
      FreeM.liftBind (lens.toFunA position)
        (fun direction ↦ FreeM.mapLens lens (next (lens.toFunB position direction))) :=
  FreeM.mapLens_liftBind lens position next

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} {β : Type uβ}
    (M : DynSystem.DynComputation.{u} P α β) (lens : Lens P Q)
    (k : Nat) (state : M.State) :
    (M.wrap lens).unroll k state = FreeM.mapLens lens (M.unroll k state) :=
  M.unroll_wrap lens k state

example {P : PFunctor.{uA, uB}} {m : Type uB → Type v}
    {n : Type uB → Type w} [Monad m] [Monad n]
    (handler : (position : P.A) → m (P.B position))
    (hom : m →ᵐ n) {X : Type uB} (program : FreeM P X) :
    hom (program.liftM handler) =
      program.liftM (fun position => hom (handler position)) :=
  FreeM.liftM_natural handler hom program

end PolyFunTest.ModuleAPI.PFunctor
