/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Resumption

/-!
# Resumption coinduction and lens-transport examples

Branch-sensitive examples pin the orientation, universes, and algebraic laws
of the computational resumption API.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uα uβ

namespace PFunctor.ResumptionLensExamples

open PFunctor
open PFunctor.Resumption

/-- A two-query interface whose answer type depends on the query. -/
def source : PFunctor.{0, 0} :=
  { A := Bool
    B := fun query => if query then Bool else Fin 3 }

/-- A runtime interface that changes both positions and answer encodings. -/
def target : PFunctor.{0, 0} :=
  { A := Fin 2
    B := fun query => if query = 1 then Fin 2 else Fin 4 }

/-- The backward maps are deliberately nonidentity and branch-dependent. -/
def encoding : Lens source target where
  toFunA query := by
    change Bool at query
    change Fin 2
    exact if query then 1 else 0
  toFunB query := by
    change Bool at query
    cases query with
    | false =>
        intro answer
        change Fin 4 at answer
        change Fin 3
        exact ⟨answer.val % 3, Nat.mod_lt _ (by omega)⟩
    | true =>
        intro answer
        change Fin 2 at answer
        change Bool
        exact decide (answer = 1)

def branch : Resumption source Nat :=
  Resumption.query true fun answer => by
    change Bool at answer
    exact Resumption.pure (if answer then 7 else 11)

def mappedBranch : Resumption target Nat :=
  Resumption.query (by change Fin 2; exact 1) fun answer => by
    change Fin 2 at answer
    exact Resumption.pure (if answer = 1 then 7 else 11)

example : mapLens encoding branch = mappedBranch := by
  apply Resumption.eq_of_dest_eq
  simp [branch, mappedBranch, encoding, source, target]

example : mapLens (Lens.id source) branch = branch := by simp

example (r : Resumption source Nat) (k : Nat → Resumption source Bool) :
    mapLens encoding (Resumption.bind r k) =
      Resumption.bind (mapLens encoding r) (fun value => mapLens encoding (k value)) :=
  mapLens_bind encoding r k

example (program : FreeM source Nat) :
    FreeM.toResumption (program.mapLens encoding) =
      mapLens encoding program.toResumption := by simp

def loopStep (seed : Bool) : Nat ⊕ source.Obj Bool :=
  Sum.inr ⟨(by change Bool; exact true), fun answer => by
    change Bool at answer
    exact xor seed answer⟩

def visibleLoop (seed : Bool) : Resumption source Nat :=
  Resumption.corec loopStep seed

example (seed : Bool) :
    Resumption.dest (visibleLoop seed) =
      Sum.map (fun value : Nat => value)
        (source.map (Resumption.corec loopStep)) (loopStep seed) := by
  exact Resumption.dest_corec loopStep seed

example (f : Bool → Resumption source Nat)
    (hf : ∀ seed, Resumption.dest (f seed) =
      Sum.map (fun value : Nat => value) (source.map f) (loopStep seed)) :
    f = Resumption.corec loopStep :=
  Resumption.corec_unique loopStep f hf

/-- Position, direction, and result universes remain independent. -/
def universeCanary {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
    {α : Type uα} (lens : Lens p q) (r : Resumption p α) :
    Resumption q α :=
  mapLens lens r

end PFunctor.ResumptionLensExamples
