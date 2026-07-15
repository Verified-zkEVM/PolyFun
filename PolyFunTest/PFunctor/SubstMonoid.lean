/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.SubstMonoid

/-!
# Regression tests for substitution monoids

The main canary is the substitution monoid of words. Its unary operations are
lists of bits and multiplication concatenates the outer word before the inner
word. The noncommutative example distinguishes the orientation of
multiplication and of homomorphism composition.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace PFunctor
namespace SubstMonoidTest

/-- The polynomial of unary operations labelled by bit strings. -/
abbrev wordP : PFunctor := ⟨List Bool, fun _ => PUnit⟩

/-- The empty word is the substitution unit. -/
def wordUnit : Lens X wordP :=
  (fun _ => []) ⇆ (fun _ _ => PUnit.unit)

/-- Substitution concatenates the outer label before the inner label. -/
def wordMult : Lens (wordP ◃ wordP) wordP :=
  (fun a => a.1 ++ a.2 PUnit.unit) ⇆
    (fun _ _ => ⟨PUnit.unit, PUnit.unit⟩)

/-- Bit strings under concatenation form a noncommutative substitution
monoid. -/
def wordMonoid : SubstMonoid where
  carrier := wordP
  unit := wordUnit
  mult := wordMult
  unit_left := by
    apply Lens.ext _ _ (fun _ => rfl)
    intro a
    exact Subsingleton.elim _ _
  unit_right := by
    apply Lens.ext _ _ (fun a => List.append_nil a)
    intro a
    exact Subsingleton.elim _ _
  assoc := by
    let hA : ∀ a : ((wordP ◃ wordP) ◃ wordP).A,
        (wordMult ∘ₗ (wordMult ◃ₗ Lens.id wordP)).toFunA a =
          (wordMult ∘ₗ (Lens.id wordP ◃ₗ wordMult) ∘ₗ
            Lens.Equiv.compAssoc.toLens).toFunA a := fun a => by
      exact List.append_assoc a.1.1 (a.1.2 PUnit.unit)
        (a.2 ⟨PUnit.unit, PUnit.unit⟩)
    apply Lens.ext _ _ hA
    intro a
    funext d
    letI : Subsingleton (((wordP ◃ wordP) ◃ wordP).B a) :=
      ⟨fun x y => by
        rcases x with ⟨⟨x₁, x₂⟩, x₃⟩
        rcases y with ⟨⟨y₁, y₂⟩, y₃⟩
        cases x₁
        cases x₂
        cases x₃
        cases y₁
        cases y₂
        cases y₃
        rfl⟩
    exact Subsingleton.elim _ _

/-- The multiplication order is observable and is outer-before-inner. -/
example : wordMonoid.mult.toFunA
    (⟨[false], fun _ : PUnit => [true]⟩ : (wordP ◃ wordP).A) =
      [false, true] := rfl

/-- Extending a map on bit generators to words gives a substitution-monoid
homomorphism. -/
def wordMapHom (f : Bool → List Bool) :
    SubstMonoid.Hom wordMonoid wordMonoid where
  toLens := List.flatMap f ⇆ (fun _ d => d)
  map_unit := rfl
  map_mult := by
    let hA : ∀ a : (wordP ◃ wordP).A,
        ((List.flatMap f ⇆ fun _ d => d) ∘ₗ wordMult).toFunA a =
          (wordMult ∘ₗ ((List.flatMap f ⇆ fun _ d => d) ◃ₗ
            (List.flatMap f ⇆ fun _ d => d))).toFunA a := fun a => by
      exact List.flatMap_append
    apply Lens.ext _ _ hA
    intro a
    funext d
    letI : Subsingleton ((wordP ◃ wordP).B a) :=
      ⟨fun x y => by
        rcases x with ⟨x₁, x₂⟩
        rcases y with ⟨y₁, y₂⟩
        cases x₁
        cases x₂
        cases y₁
        cases y₂
        rfl⟩
    exact Subsingleton.elim _ _

/-- Expand the `false` generator by a trailing `true`. -/
def expandFalse : Bool → List Bool
  | false => [false, true]
  | true => [true]

/-- Collapse either generator to `false`. -/
def collapseTrue : Bool → List Bool
  | false => [false]
  | true => [false]

/-- Hom composition is observable in diagrammatic order: first expand, then
collapse. Reversing the two maps produces `[false, true]` instead. -/
example : ((wordMapHom expandFalse).comp (wordMapHom collapseTrue)).toLens.toFunA
    [false] = [false, false] := rfl

/-- Identity and composition expose the underlying lens in diagrammatic
order. -/
example (M : SubstMonoid.{u, v}) : SubstMonoid.Hom M M :=
  SubstMonoid.Hom.id M

example {M N O : SubstMonoid.{u, v}} (f : SubstMonoid.Hom M N)
    (g : SubstMonoid.Hom N O) :
    (f.comp g).toLens = g.toLens ∘ₗ f.toLens := rfl

example {M N O : SubstMonoid.{u, v}} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).toLens = g.toLens ∘ₗ f.toLens := rfl

/-- Position and direction universes of substitution monoids are independent. -/
example (M : SubstMonoid.{u, v}) : M.mult ∘ₗ
    (M.unit ◃ₗ Lens.id M.carrier) ∘ₗ Lens.Equiv.XComp.invLens =
    Lens.id M.carrier := M.unit_left

end SubstMonoidTest
end PFunctor
