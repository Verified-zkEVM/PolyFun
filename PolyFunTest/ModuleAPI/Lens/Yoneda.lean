/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Yoneda
public import PolyFun.PFunctor.Equiv.Special

/-!
# Ordinary-import canaries for Yoneda and the normal form

The Yoneda bijection, the hom formula `Lens P Q ≃ Π a, Q.Obj (P.B a)`, the values `p(1)` and
`p(0)`, the normal form, and the lens-to-natural-transformation direction are definitional.
These examples check that those equations hold by `rfl` through ordinary imports, with
independent universes, as a consumer in another package sees them.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PolyFunTest.ModuleAPI.Lens.Yoneda

open _root_.PFunctor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

example {S : Type uB} (l : Lens (y^S : PFunctor.{uA, uB}) Q) :
    Lens.purePowerEquiv.symm (Lens.purePowerEquiv l) = l := rfl

example {S : Type uB} (x : Q.Obj S) :
    Lens.purePowerEquiv (Lens.purePowerEquiv.symm x : Lens (y^S : PFunctor.{uA, uB}) Q) = x :=
  rfl

example {S : Type uB} (g : Lens Q R) (l : Lens (y^S : PFunctor.{uA, uB}) Q) :
    Lens.purePowerEquiv (g ∘ₗ l) = g.mapObj (Lens.purePowerEquiv l) := rfl

example (l : Lens P Q) : Lens.equivPiObj.symm (Lens.equivPiObj l) = l := rfl

example (l : Lens P Q) (a : P.A) : Lens.equivPiObj l a = l.mapObj (Obj.mk a id) := rfl

example (l : Lens P Q) : Lens.objHomEquiv.symm (Lens.objHomEquiv l) = l := rfl

example {X Y : Type uB₁} (l : Lens P Q) (h : X → Y) (x : P.Obj X) :
    l.mapObj (P.map h x) = Q.map h (l.mapObj x) := rfl

example (x : P.Obj PUnit.{uB + 1}) : (Obj.punitEquiv P).symm (Obj.punitEquiv P x) = x := rfl

example (a : P.A) : Obj.punitEquiv P ((Obj.punitEquiv.{uB} P).symm a) = a := rfl

example (a : P.A) :
    (Equiv.sigmaPurePower P).equivA ((Equiv.sigmaPurePower P).equivA.symm a) = a := rfl

end PolyFunTest.ModuleAPI.Lens.Yoneda
