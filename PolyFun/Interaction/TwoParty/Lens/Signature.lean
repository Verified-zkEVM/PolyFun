/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Path
public import PolyFun.Interaction.TwoParty.Role

/-!
# Ownership lenses

The target polynomial records an owner and a move carrier. Source directions describe
shape choices; the backward component of the lens selects a shape branch from a move.
-/

public section

universe u uA uB

namespace Interaction.TwoParty.Lens

open PFunctor

/-- Polynomial of roles and move carriers in `Type u`. -/
@[expose, implicit_reducible] def rolePoly : PFunctor.{u+1, u} := ⟨Role × Type u, fun r => r.2⟩

/-- The universe polynomial, with a carrier as position and its elements as directions. -/
@[expose] def universePoly : PFunctor.{u+1, u} := ⟨Type u, id⟩

/-- Assign roles to the positions of a polynomial without erasing its directions. -/
@[expose] def ofRoles {P : PFunctor.{uA, u}} (roles : P.A → Role) :
    PFunctor.Lens P rolePoly where
  toFunA a := (roles a, P.B a)
  toFunB _ x := x

/-- Owner of the move at a source position. -/
@[expose] def owner {P : PFunctor.{uA, uB}} (l : PFunctor.Lens P rolePoly.{u})
    (a : P.A) : Role := (l.toFunA a).1

/-- Runtime move at a source position, which may carry more information than a branch. -/
@[expose, implicit_reducible] def Move {P : PFunctor.{uA, uB}} (l : PFunctor.Lens P rolePoly.{u})
    (a : P.A) : Type u := (l.toFunA a).2

/-- Participants in a focused interaction. -/
inductive Participant : Type u where
  | focal
  | counterpart
  deriving DecidableEq

/-- Order of the two effect slots at every boundary, including the terminal boundary. -/
inductive Schedule where
  | focalFirst
  | counterpartFirst
  deriving DecidableEq

end Interaction.TwoParty.Lens
