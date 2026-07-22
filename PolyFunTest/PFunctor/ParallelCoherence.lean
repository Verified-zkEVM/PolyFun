/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Coherence
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Presentation

/-!
# Regression tests for parallel presentation and behavior coherence

These examples observe componentwise state/witness maps and pin the symmetry,
unit, associativity, and interchange interfaces used by later displayed
coherence.
-/

@[expose] public section

namespace PFunctor.ParallelCoherenceCanary

abbrev Interface : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩

def responder : Responder Nat Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)

abbrev contract : Display Interface where
  position _ := String
  direction _ _ _ := Bool

def Invariant (_ : Nat) : Type := PUnit

def displayed :
    Display.Coalgebra (Display.responder contract) responder.out Invariant :=
  (Display.responderCoalgebraEquiv contract responder Invariant).symm
    fun _ _ _ _ => ⟨false, PUnit.unit⟩

def presentationId :
    Responder.PresentationHom contract
      responder Invariant displayed responder Invariant displayed :=
  Responder.PresentationHom.id

def toTerminal :=
  Responder.PresentationHom.toTerminal contract
    responder Invariant displayed

def mixedParallel := toTerminal.parallel presentationId

example : mixedParallel.toState (5, 7) = (responder.behavior 5, 7) :=
  rfl

example : (mixedParallel.toWitness (5, 7) (PUnit.unit, PUnit.unit)).2 =
    PUnit.unit :=
  rfl

example :
    (Responder.respondDisplayed contract
      (mixedParallel.toWitness (5, 7) (PUnit.unit, PUnit.unit)).1
      PUnit.unit "contract").1 = false :=
  rfl

example : presentationId.parallel presentationId =
    Responder.PresentationHom.id :=
  Responder.PresentationHom.parallel_id

example :
    (toTerminal.parallel presentationId).comp
        (presentationId.parallel presentationId) =
      (toTerminal.comp presentationId).parallel
        (presentationId.comp presentationId) :=
  Responder.PresentationHom.parallel_comp _ _ _ _

def leftBehavior := responder.behavior 5

def rightBehavior := responder.behavior 7

example :
    Responder.mapBehavior (Lens.parallelSumComm Interface Interface)
        (Responder.parallelBehavior rightBehavior leftBehavior) =
      Responder.parallelBehavior leftBehavior rightBehavior :=
  Responder.mapBehavior_parallel_comm leftBehavior rightBehavior

example : (Responder.terminal (P := Interface ∥ Interface)).answer
    (Responder.mapBehavior (Lens.parallelSumComm Interface Interface)
      (Responder.parallelBehavior rightBehavior leftBehavior))
    (.both PUnit.unit PUnit.unit) = (5, 7) :=
  rfl

example :
    Responder.mapBehavior
        (Lens.parallelSumZero Interface :
          Lens (Interface ∥ (0 : PFunctor.{0, 0})) Interface)
        leftBehavior =
      Responder.parallelBehavior leftBehavior Responder.zeroBehavior :=
  Responder.mapBehavior_parallel_zero_right leftBehavior

example :
    Responder.mapBehavior
        (Lens.zeroParallelSum Interface :
          Lens ((0 : PFunctor.{0, 0}) ∥ Interface) Interface)
        leftBehavior =
      Responder.parallelBehavior Responder.zeroBehavior leftBehavior :=
  Responder.mapBehavior_parallel_zero_left leftBehavior

example :
    Responder.mapBehavior
        (Lens.parallelSumAssoc Interface Interface Interface)
        (Responder.parallelBehavior leftBehavior
          (Responder.parallelBehavior rightBehavior leftBehavior)) =
      Responder.parallelBehavior
        (Responder.parallelBehavior leftBehavior rightBehavior)
        leftBehavior :=
  Responder.mapBehavior_parallel_assoc _ _ _

example :
    (Responder.terminal
      (P := (Interface ∥ Interface) ∥ Interface)).answer
      (Responder.mapBehavior
        (Lens.parallelSumAssoc Interface Interface Interface)
        (Responder.parallelBehavior leftBehavior
          (Responder.parallelBehavior rightBehavior leftBehavior)))
      (.both (.both PUnit.unit PUnit.unit) PUnit.unit) = ((5, 7), 5) :=
  rfl

end PFunctor.ParallelCoherenceCanary
