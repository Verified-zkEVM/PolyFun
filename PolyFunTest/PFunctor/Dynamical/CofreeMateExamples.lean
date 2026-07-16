/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.CofreeMate
public import PolyFunTest.PFunctor.CofreeUniversal

/-!
# Regression tests for dynamical-system cofree mates

These tests separate the generic coiteration/behavior identification from the
universe-local retrofunctor packaging.  A branching three-state system makes
the mate's dependent backward map observable at the root, on both one-edge
branches, and after a two-edge path.
-/

@[expose] public section

universe uS uA uB uα

namespace PFunctor
namespace CofreeMateTest

open ComonoidCategoryTest
open CofreePolynomialTest
open CofreeUniversalTest

/-! ## Universe boundaries -/

/-- Generic coiteration identifies with behavior while the state and both
interface universes remain independent. -/
example (P : PFunctor.{uA, uB}) (S : Type uS)
    (system : DynSystem S P) :
    CofreeP.unfoldShape (stateComonoid S) system = system.behavior :=
  DynSystem.unfoldShape_stateComonoid system

/-- Vertex-labelled mate objects and their decoding keep the label universe
independent as well. -/
example (P : PFunctor.{uA, uB}) (S : Type uS) (α : Type uα)
    (system : DynSystem S P) (state : S) (label : S → α) :
    CofreeP.decode (DynSystem.mateObj system state label) =
      DynSystem.labeledTrajectory system label state :=
  DynSystem.decode_mateObj system state label

/-- The full retrofunctor mate is packaged at the homogeneous maximum required
by the current `Comonoid.Hom` API. -/
example (P : PFunctor.{uA, uB}) (S : Type (max uA uB))
    (system : DynSystem S P) :
    Comonoid.Hom (stateComonoid S) (CofreeP.comonoid P) :=
  system.cofreeMate

/-! ## Observable reached-state semantics -/

def branchingSystem : DynSystem ThreeState binaryP :=
  branchingLens

def stateCode : ThreeState → Nat
  | .source => 0
  | .middle => 1
  | .final => 2

def labeledBehavior : CofreeC binaryP Nat :=
  CofreeP.decode
    (DynSystem.mateObj branchingSystem ThreeState.source stateCode)

/-- Decoding observes the initial state's label at the root. -/
example : CofreeC.head labeledBehavior = 0 := by
  simp [labeledBehavior, stateCode]

/-- The false child is labelled by the reached middle state. -/
example : CofreeC.head ((CofreeC.tail labeledBehavior).2 false) = 1 := by
  simp [labeledBehavior, stateCode, branchingSystem, branchingLens,
    DynSystem.update]

/-- Following false and then true reaches the final state, whose distinct label
pins the same outer-then-inner order as the full retrofunctor test below. -/
example : CofreeC.head
    ((CofreeC.tail ((CofreeC.tail labeledBehavior).2 false)).2 true) = 2 := by
  simp [labeledBehavior, stateCode, branchingSystem, branchingLens,
    DynSystem.update]

/-- The exposed-position labelling specializes directly to the established
trajectory. -/
example : CofreeP.decode
    (DynSystem.mateObj branchingSystem ThreeState.source
      branchingSystem.expose) =
    branchingSystem.trajectory .source := by
  rw [DynSystem.decode_mateObj, DynSystem.labeledTrajectory_expose]

def behaviorTree : M binaryP :=
  branchingSystem.cofreeMate.toLens.toFunA .source

example : behaviorTree = branchingSystem.behavior .source := by
  unfold behaviorTree
  rw [DynSystem.cofreeMate_toLens]
  exact congrFun
    (DynSystem.unfoldShape_stateComonoid branchingSystem) ThreeState.source

def falseVertex : M.Vertex behaviorTree :=
  .child false (.root _)

def trueVertex : M.Vertex behaviorTree :=
  .child true (.root _)

def falseTarget : ThreeState :=
  Comonoid.target (stateComonoid ThreeState) ThreeState.source
    (branchingSystem.cofreeMate.toLens.toFunB
      ThreeState.source falseVertex)

def nextTrueVertex : M.Vertex
    (branchingSystem.cofreeMate.toLens.toFunA falseTarget) :=
  .child true (.root _)

def innerTrueVertex : M.Vertex (M.Vertex.subtree falseVertex) :=
  cast (congrArg M.Vertex
    (branchingSystem.cofreeMate.map_target
      ThreeState.source falseVertex)) nextTrueVertex

def falseThenTrueVertex : M.Vertex behaviorTree :=
  M.Vertex.append falseVertex innerTrueVertex

/-- The exported backward-map equation exposes the full retrofunctor component
used by the concrete reached-state canaries below. -/
example (state : ThreeState)
    (vertex : M.Vertex (branchingSystem.cofreeMate.toLens.toFunA state)) :
    branchingSystem.cofreeMate.toLens.toFunB state vertex =
      CofreeP.unfoldDirection (stateComonoid ThreeState)
        branchingSystem state vertex :=
  DynSystem.cofreeMate_toFunB branchingSystem state vertex

/-- The root vertex pulls back to the identity arrow, hence the starting
state. -/
example : branchingSystem.cofreeMate.toLens.toFunB .source
    (.root behaviorTree) = .source := by
  unfold behaviorTree
  calc
    branchingSystem.cofreeMate.toLens.toFunB .source
        (.root (branchingSystem.cofreeMate.toLens.toFunA .source)) =
        Comonoid.identity (stateComonoid ThreeState) .source := by
      simpa only [CofreeP.comonoid_identity] using
        branchingSystem.cofreeMate.map_identity ThreeState.source
    _ = .source := rfl

/-- The `false` branch reaches the observably distinct middle state. -/
theorem cofreeMate_falseVertex :
    branchingSystem.cofreeMate.toLens.toFunB .source falseVertex =
    .middle := by
  change (CofreeP.restrict (stateComonoid ThreeState)
    branchingSystem.cofreeMate).toFunB .source false = .middle
  rw [DynSystem.restrict_cofreeMate]
  rfl

theorem falseTarget_eq_middle : falseTarget = ThreeState.middle := by
  unfold falseTarget
  rw [cofreeMate_falseVertex]
  rfl

theorem stateComonoid_compose (start first second : ThreeState) :
    Comonoid.compose (stateComonoid ThreeState) start first second =
      second := by
  rfl

/-- The `true` branch reaches the final state rather than reversing the branch
labels. -/
theorem cofreeMate_trueVertex :
    branchingSystem.cofreeMate.toLens.toFunB .source trueVertex =
    .final := by
  change (CofreeP.restrict (stateComonoid ThreeState)
    branchingSystem.cofreeMate).toFunB .source true = .final
  rw [DynSystem.restrict_cofreeMate]
  rfl

/-- Two edges are composed in outer-then-inner order: source --false→ middle
--true→ final. -/
example : branchingSystem.cofreeMate.toLens.toFunB .source
    falseThenTrueVertex = .final := by
  have hmap := branchingSystem.cofreeMate.map_compose
    ThreeState.source falseVertex innerTrueVertex
  change branchingSystem.cofreeMate.toLens.toFunB ThreeState.source
    (M.Vertex.append falseVertex innerTrueVertex) = ThreeState.final
  refine hmap.trans ?_
  let transported := cast
    (congrArg (CofreeP.comonoid binaryP).carrier.B
      (branchingSystem.cofreeMate.map_target
        ThreeState.source falseVertex).symm)
    innerTrueVertex
  have htransported : transported = nextTrueVertex := by
    apply eq_of_heq
    exact (cast_heq _ innerTrueVertex).trans
      (cast_heq _ nextTrueVertex)
  have htail :
      branchingSystem.cofreeMate.toLens.toFunB falseTarget transported =
        ThreeState.final := by
    rw [htransported]
    change (CofreeP.restrict (stateComonoid ThreeState)
      branchingSystem.cofreeMate).toFunB falseTarget true =
        ThreeState.final
    rw [DynSystem.restrict_cofreeMate, falseTarget_eq_middle]
    rfl
  rw [stateComonoid_compose]
  exact htail

/-! ## Universal property and trajectory compatibility -/

example : CofreeP.restrict (stateComonoid ThreeState)
    branchingSystem.cofreeMate = branchingSystem := by
  simp

/-- Uniqueness is exercised for an arbitrary full retrofunctor, not merely for
the canonical construction on both sides. -/
example (hom : Comonoid.Hom (stateComonoid ThreeState)
    (CofreeP.comonoid binaryP))
    (h : CofreeP.restrict (stateComonoid ThreeState) hom =
      branchingSystem) :
    hom = branchingSystem.cofreeMate :=
  DynSystem.cofreeMate_unique branchingSystem hom h

/-- The existing trajectory is exactly the mate's behavior tree with each node
self-labelled by its exposed position. -/
example : branchingSystem.trajectory .source =
    M.selfLabel
      (branchingSystem.cofreeMate.toLens.toFunA .source) :=
  DynSystem.trajectory_eq_selfLabel_cofreeMate branchingSystem .source

/-- The trajectory bridge remains available generically at the honest Hom
universe boundary. -/
example (P : PFunctor.{uA, uB}) (S : Type (max uA uB))
    (system : DynSystem S P) (state : S) :
    system.trajectory state =
      M.selfLabel (system.cofreeMate.toLens.toFunA state) :=
  DynSystem.trajectory_eq_selfLabel_cofreeMate system state

end CofreeMateTest
end PFunctor
