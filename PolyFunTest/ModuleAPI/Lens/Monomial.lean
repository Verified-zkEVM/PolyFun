/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Monomial

/-!
# Ordinary-import canaries for monomial lenses

ArkLib's statement, witness, and context lenses are lenses between monomials
`OuterIn y^ OuterOut ⇆ InnerIn y^ InnerOut`, read as a projection of inputs and a lift of
outputs. These examples check that `Lens.ofMonomial`, `monomialMapFst`, and `monomialMapSnd`
provide that reading through ordinary imports, with independent universes on the four types.
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PolyFunTest.ModuleAPI.Lens

open _root_.PFunctor

variable {OuterIn : Type uA₁} {OuterOut : Type uB₁} {InnerIn : Type uA₂} {InnerOut : Type uB₂}

/-- A context lens in ArkLib's reading: project the outer input statement to the inner one
and lift the inner output statement back, given the outer input. -/
abbrev StatementLens (OuterIn : Type uA₁) (OuterOut : Type uB₁) (InnerIn : Type uA₂)
    (InnerOut : Type uB₂) :=
  Lens (OuterIn y^ OuterOut) (InnerIn y^ InnerOut)

/-- The projection is the forward map. -/
example (proj : OuterIn → InnerIn) (lift : OuterIn → InnerOut → OuterOut) (x : OuterIn) :
    (Lens.ofMonomial proj lift : StatementLens OuterIn OuterOut InnerIn InnerOut).toFunA x =
      proj x :=
  Lens.ofMonomial_toFunA proj lift x

/-- The lift is the backward map. -/
example (proj : OuterIn → InnerIn) (lift : OuterIn → InnerOut → OuterOut) (x : OuterIn)
    (y : InnerOut) :
    (Lens.ofMonomial proj lift : StatementLens OuterIn OuterOut InnerIn InnerOut).toFunB x y =
      lift x y :=
  Lens.ofMonomial_toFunB proj lift x y

/-- An input-only lens leaves outputs alone. -/
example (proj : OuterIn → InnerIn) (x : OuterIn) (y : OuterOut) :
    (Lens.monomialMapFst proj : StatementLens OuterIn OuterOut InnerIn OuterOut).toFunB x y =
      y :=
  Lens.monomialMapFst_toFunB proj x y

/-- An output-only lens leaves inputs alone. -/
example (lift : OuterIn → InnerOut → OuterOut) (x : OuterIn) :
    (Lens.monomialMapSnd lift : StatementLens OuterIn OuterOut OuterIn InnerOut).toFunA x =
      x :=
  Lens.monomialMapSnd_toFunA lift x

/-- Lifting through two contexts composes the projections and threads the lifts. -/
example {Mid : Type uA₃} {MidOut : Type uB₃} (proj₁ : OuterIn → Mid)
    (lift₁ : OuterIn → MidOut → OuterOut) (proj₂ : Mid → InnerIn)
    (lift₂ : Mid → InnerOut → MidOut) :
    (Lens.ofMonomial proj₂ lift₂ ∘ₗ Lens.ofMonomial proj₁ lift₁ :
        StatementLens OuterIn OuterOut InnerIn InnerOut) =
      Lens.ofMonomial (fun x => proj₂ (proj₁ x)) (fun x y => lift₁ x (lift₂ (proj₁ x) y)) :=
  Lens.ofMonomial_comp proj₂ lift₂ proj₁ lift₁

/-- Every context lens is its own components. -/
example (l : StatementLens OuterIn OuterOut InnerIn InnerOut) :
    Lens.ofMonomial l.toFunA l.toFunB = l :=
  Lens.ofMonomial_eta l

end PolyFunTest.ModuleAPI.Lens
