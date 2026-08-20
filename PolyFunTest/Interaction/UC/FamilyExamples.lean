/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenSyntax.Expr
public import PolyFun.Interaction.UC.OpenTheory.Family

/-!
# Pointwise open-theory family examples

These examples pin the intended use of `OpenTheory.pi`: structural laws and
allowed-system predicates lift componentwise while the family index remains
semantically uninterpreted by PolyFun.
-/

public section

universe u

namespace Interaction.UC.OpenTheoryFamilyExamples

variable {Atom : PortBoundary → Type u}

abbrev ExprFamily : OpenTheory :=
  OpenTheory.pi (fun _ : Nat => OpenSyntax.Expr.theory Atom)

example : OpenTheory.HasPlugWireFactor (ExprFamily (Atom := Atom)) := inferInstance

abbrev TopFamily : SubTheory (ExprFamily (Atom := Atom)) :=
  SubTheory.pi (fun _ : Nat => SubTheory.top (OpenSyntax.Expr.theory Atom))

example : (TopFamily (Atom := Atom)).IsPlugClosed := inferInstance

example : (TopFamily (Atom := Atom)).IsStructural := inferInstance

example {Δ : PortBoundary} (W : (ExprFamily (Atom := Atom)).Obj Δ) :
    (ExprFamily (Atom := Atom)).map (PortBoundary.Hom.id Δ) W = W :=
  OpenTheory.map_id W

example {Δ₁ Δ₂ : PortBoundary}
    {W₁ : (ExprFamily (Atom := Atom)).Obj Δ₁}
    {W₂ : (ExprFamily (Atom := Atom)).Obj Δ₂}
    (hW₁ : (TopFamily (Atom := Atom)).mem W₁)
    (hW₂ : (TopFamily (Atom := Atom)).mem W₂) :
    (TopFamily (Atom := Atom)).mem ((ExprFamily (Atom := Atom)).par W₁ W₂) :=
  (TopFamily (Atom := Atom)).mem_par hW₁ hW₂

end Interaction.UC.OpenTheoryFamilyExamples

