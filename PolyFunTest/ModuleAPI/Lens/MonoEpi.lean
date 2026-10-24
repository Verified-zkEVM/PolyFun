/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Factorization
public import PolyFun.PFunctor.Lens.MonoEpi

/-!
# Ordinary-import canaries for cancellable and cartesian lenses

The joint fibre map at a position's own image, and the lens built from a family of direction
equivalences, compute by `rfl` through ordinary imports. A cartesian lens is recovered from its
routes by `rfl`. Each polynomial lives in its own universes.
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂

namespace PolyFunTest.ModuleAPI.Lens.MonoEpi

open _root_.PFunctor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

example (l : Lens P Q) (a : P.A) (d : Q.B (l.toFunA a)) :
    l.fiberJoint (l.toFunA a) d ⟨a, rfl⟩ = l.toFunB a d := rfl

example (r : (a : P.A) → Σ b : Q.A, Q.B b ≃ P.B a) (a : P.A) :
    (Lens.ofDirectionEquiv r).toFunA a = (r a).1 := rfl

example (r : (a : P.A) → Σ b : Q.A, Q.B b ≃ P.B a) (a : P.A) (d : Q.B (r a).1) :
    (Lens.ofDirectionEquiv r).toFunB a d = (r a).2 d := rfl

example (l : {l : Lens P Q // l.IsCartesian}) :
    Lens.cartesianEquiv.symm (Lens.cartesianEquiv l) = l := rfl

end PolyFunTest.ModuleAPI.Lens.MonoEpi
