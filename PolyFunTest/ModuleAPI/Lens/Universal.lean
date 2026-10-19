/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Universal

/-!
# Ordinary-import canaries for universal properties and special hom-isomorphisms

The indexed universal properties, the agreement of sums and products with their actions, and
the hom-isomorphisms of Niu–Spivak §5.1 are definitional. These examples check that their
round trips and naturality equations hold by `rfl` through ordinary imports, with independent
universes.
-/

@[expose] public section

universe v w uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PolyFunTest.ModuleAPI.Lens.Universal

open _root_.PFunctor

variable {I : Type v} {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₃, uB₃}}

example {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}} (l : Lens (sigma F) R) :
    Lens.sigmaExists (Lens.sigmaEquiv l) = l := rfl

example {F : I → PFunctor.{uA₂, uB₂}} (l : ∀ i, Lens p (F i)) (i : I) :
    Lens.piProj i ∘ₗ Lens.piForall l = l i := rfl

example {F : I → PFunctor.{uA₁, uB₁}} {X : Type w} (x : (sigma F).Obj X) :
    (Obj.sigmaEquiv F X).symm (Obj.sigmaEquiv F X x) = x := rfl

example {F : I → PFunctor.{uA₁, uB₁}} {X : Type w} (x : (pi F).Obj X) :
    (Obj.piEquiv F X).symm (Obj.piEquiv F X x) = x := rfl

example {J : Type uA₂} (l : Lens (linear J : PFunctor.{uA₂, uB₂}) p) :
    Lens.linearEquiv.symm (Lens.linearEquiv l) = l := rfl

example (l : Lens p (y : PFunctor.{uA₂, uB₂})) :
    Lens.sectionEquiv.symm (Lens.sectionEquiv l) = l := rfl

example {A : Type uB₂} (l : Lens p (y^A : PFunctor.{uA₂, uB₂})) :
    Lens.toPurePowerEquiv.symm (Lens.toPurePowerEquiv l) = l := rfl

example {J : Type uA₂} {A : Type uB₂} (l : Lens p (J y^ A)) :
    Lens.toMonomialEquiv.symm (Lens.toMonomialEquiv l) = l := rfl

example (l : Lens (p ⊗ q) (y : PFunctor.{uA₂, uB₂})) :
    Lens.sectionTensorEquiv.symm (Lens.sectionTensorEquiv l) = l := rfl

example (s : Lens q (y : PFunctor.{uA₂, uB₂})) (f : Lens p q) :
    Lens.sectionEquiv (s ∘ₗ f) = fun a => f.toFunB a (Lens.sectionEquiv s (f.toFunA a)) := rfl

end PolyFunTest.ModuleAPI.Lens.Universal
