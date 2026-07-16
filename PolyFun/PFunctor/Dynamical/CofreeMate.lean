/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Universal
public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# Dynamical systems as cofree-comonoid mates

A dynamical system `s : DynSystem S P` is a lens from the state polynomial
`selfMonomial S` to its interface `P`.  Coiteration from the state comonoid
recovers the existing terminal-coalgebra behavior of `s`.  When the state type
lives in the universe required by the current homogeneous `Comonoid.Hom` API,
the cofree universal property packages this coiteration as the unique
retrofunctor mate `s.cofreeMate`.

This module identifies both presentations without replacing the foundational
`DynSystem.behavior` API.  The mate records more than its behavior-tree object
map: its dependent backward map sends a finite behavior vertex to the state
reached at that vertex.
-/

@[expose] public section

universe uS uA uB uα

namespace PFunctor
namespace DynSystem

variable {S : Type uS} {P : PFunctor.{uA, uB}}
  {α : Type uα}

/-! ## Generic coiteration and behavior -/

/-- Cofree-comonoid coiteration from the state comonoid has exactly the
existing terminal-coalgebra behavior as its object map.  The state and
interface universes remain independent because this theorem does not package a
`Comonoid.Hom`. -/
theorem unfoldShape_stateComonoid (system : DynSystem S P) :
    CofreeP.unfoldShape (stateComonoid S) system = system.behavior :=
  rfl

/-! ## Vertex-labelled mate semantics -/

/-- The infinite trajectory of a dynamical system with every reached state
labelled by `label`. -/
def labeledTrajectory (system : DynSystem S P) (label : S → α)
    (state : S) : CofreeC P α :=
  M.corec
    (fun current =>
      ⟨(label current, system.expose current),
        fun direction => system.update current direction⟩)
    state

/-- One-step unfolding of a labelled trajectory. -/
theorem dest_labeledTrajectory (system : DynSystem S P)
    (label : S → α) (state : S) :
    M.dest (labeledTrajectory system label state) =
      ⟨(label state, system.expose state), fun direction =>
        labeledTrajectory system label (system.update state direction)⟩ := by
  simp only [labeledTrajectory, M.dest_corec_apply]

@[simp]
theorem head_labeledTrajectory (system : DynSystem S P)
    (label : S → α) (state : S) :
    CofreeC.head (labeledTrajectory system label state) = label state := by
  simp only [CofreeC.head, dest_labeledTrajectory]

@[simp]
theorem tail_labeledTrajectory (system : DynSystem S P)
    (label : S → α) (state : S) :
    CofreeC.tail (labeledTrajectory system label state) =
      ⟨system.expose state, fun direction =>
        labeledTrajectory system label (system.update state direction)⟩ := by
  simp only [CofreeC.tail]
  rw [dest_labeledTrajectory]
  rfl

/-- Apply the generic coiterated mate lens to an initial state carrying an
arbitrary state labelling.  Its shape records behavior and its label at a
finite vertex records `label` applied to the state reached there. -/
def mateObj (system : DynSystem S P) (state : S)
    (label : S → α) : (CofreeP P).Obj α :=
  Lens.mapObj (CofreeP.unfoldLens (stateComonoid S) system)
    (⟨state, label⟩ : (selfMonomial S).Obj α)

/-- The unlabelled shape underlying `mateObj` is the existing behavior tree. -/
@[simp]
theorem mateObj_shape (system : DynSystem S P) (state : S)
    (label : S → α) :
    (mateObj system state label).1 = system.behavior state :=
  congrFun (unfoldShape_stateComonoid system) state

private theorem unfoldDirection_stateComonoid_child
    (system : DynSystem S P) (state : S)
    (direction : P.B (M.head
      (CofreeP.unfoldShape (stateComonoid S) system state)))
    (next : M.Vertex
      (M.children
        (CofreeP.unfoldShape (stateComonoid S) system state) direction)) :
    CofreeP.unfoldDirection (stateComonoid S) system state
        (.child direction next) =
      CofreeP.unfoldDirection (stateComonoid S) system
        (CofreeP.unfoldRootDirection
          (stateComonoid S) system state direction)
        (cast (congrArg M.Vertex
          (CofreeP.children_unfoldShape
            (stateComonoid S) system state direction)) next) := by
  rw [CofreeP.unfoldDirection.eq_def]
  rfl

private theorem mateObj_child
    (system : DynSystem S P) (state : S) (label : S → α)
    (direction : P.B (M.head (mateObj system state label).1)) :
    CofreeP.childObj (mateObj system state label) direction =
      mateObj system (system.update state
        (cast (congrArg P.B
          (CofreeP.head_unfoldShape (stateComonoid S) system state))
          direction)) label := by
  let childEq := CofreeP.children_unfoldShape
    (stateComonoid S) system state direction
  apply Sigma.ext childEq
  apply Function.hfunext (congrArg M.Vertex childEq)
  intro leftVertex rightVertex hVertex
  have hcast : cast (congrArg M.Vertex childEq) leftVertex = rightVertex :=
    (cast_eq_iff_heq).2 hVertex
  subst rightVertex
  apply heq_of_eq
  change label
      (CofreeP.unfoldDirection (stateComonoid S) system state
        (.child direction leftVertex)) =
    label
      (CofreeP.unfoldDirection (stateComonoid S) system
        (CofreeP.unfoldRootDirection
          (stateComonoid S) system state direction)
        (cast (congrArg M.Vertex childEq) leftVertex))
  rw [unfoldDirection_stateComonoid_child]

private theorem decodeStep_mateObj
    (system : DynSystem S P) (state : S) (label : S → α) :
    CofreeP.decodeStep (mateObj system state label) =
      ⟨(label state, system.expose state), fun direction =>
        mateObj system (system.update state direction) label⟩ := by
  let hPosition :
      (CofreeP.decodeStep (mateObj system state label)).1 =
        (label state, system.expose state) := by
    apply Prod.ext
    · change label
          (CofreeP.unfoldDirection (stateComonoid S) system state
            (.root (CofreeP.unfoldShape
              (stateComonoid S) system state))) = label state
      rw [CofreeP.unfoldDirection_root]
      rfl
    · exact CofreeP.head_unfoldShape
        (stateComonoid S) system state
  apply Sigma.ext hPosition
  apply Function.hfunext
    (congrArg (constProd P α).B hPosition)
  intro leftDirection rightDirection hDirection
  apply heq_of_eq
  have hSource :
      cast (congrArg P.B
        (CofreeP.head_unfoldShape
          (stateComonoid S) system state)) leftDirection =
        rightDirection := by
    apply eq_of_heq
    exact (cast_heq _ leftDirection).trans hDirection
  calc
    (CofreeP.decodeStep (mateObj system state label)).2 leftDirection =
        mateObj system (system.update state
          (cast (congrArg P.B
            (CofreeP.head_unfoldShape
              (stateComonoid S) system state)) leftDirection)) label :=
      mateObj_child system state label leftDirection
    _ = mateObj system (system.update state rightDirection) label := by
      cases hSource
      rfl

/-- Decoding the vertex-labelled object produced by the generic mate lens gives
the trajectory labelled by `label` applied to the states reached at its finite
vertices. -/
@[simp]
theorem decode_mateObj
    (system : DynSystem S P) (state : S) (label : S → α) :
    CofreeP.decode (mateObj system state label) =
      labeledTrajectory system label state := by
  change M.corec CofreeP.decodeStep (mateObj system state label) =
    M.corec
      (fun current =>
        ⟨(label current, system.expose current),
          fun direction => system.update current direction⟩)
      state
  refine M.corec_eq_corec _ _
    (fun object current => object = mateObj system current label)
    _ _ rfl ?_
  rintro _ current rfl
  refine ⟨(label current, system.expose current),
    (fun direction => mateObj system (system.update current direction) label),
    system.update current, decodeStep_mateObj system current label, rfl, ?_⟩
  intro direction
  rfl

/-- Labelling states by their exposed positions recovers the existing
trajectory definition. -/
@[simp]
theorem labeledTrajectory_expose (system : DynSystem S P) (state : S) :
    labeledTrajectory system system.expose state = system.trajectory state :=
  rfl

/-- Applying the mate lens to the exposed-position labelling and decoding it
recovers the established cofree trajectory. -/
theorem decode_mateObj_expose (system : DynSystem S P) (state : S) :
    CofreeP.decode (mateObj system state system.expose) =
      system.trajectory state := by
  rw [decode_mateObj, labeledTrajectory_expose]

/-! ## The universe-local retrofunctor mate -/

section Mate

variable {S : Type (max uA uB)}

/-- The retrofunctor mate of a dynamical system under the universe-local
cofree-comonoid hom-set equivalence. -/
def cofreeMate (system : DynSystem S P) :
    Comonoid.Hom (stateComonoid S) (CofreeP.comonoid P) :=
  CofreeP.extend (stateComonoid S) system

theorem cofreeMate_toLens (system : DynSystem S P) :
    system.cofreeMate.toLens =
      CofreeP.unfoldLens (stateComonoid S) system :=
  rfl

/-- The mate's object map is the existing terminal-coalgebra behavior. -/
theorem cofreeMate_toFunA (system : DynSystem S P) :
    system.cofreeMate.toLens.toFunA = system.behavior :=
  unfoldShape_stateComonoid system

/-- The mate's dependent backward map pulls a finite behavior vertex back to
the state reached at that vertex. -/
theorem cofreeMate_toFunB (system : DynSystem S P)
    (state : S)
    (vertex : M.Vertex (system.cofreeMate.toLens.toFunA state)) :
    system.cofreeMate.toLens.toFunB state vertex =
      CofreeP.unfoldDirection (stateComonoid S) system state vertex :=
  rfl

/-- Restricting a dynamical system's cofree mate to the one-step cogenerator
recovers the original system. -/
@[simp]
theorem restrict_cofreeMate (system : DynSystem S P) :
    CofreeP.restrict (stateComonoid S) system.cofreeMate = system :=
  CofreeP.restrict_extend _ _

/-- A dynamical system's cofree mate is the unique full retrofunctor with the
given one-step restriction.  This includes uniqueness of the dependent
backward map, not only of the behavior-tree object map. -/
theorem cofreeMate_unique (system : DynSystem S P)
    (hom : Comonoid.Hom (stateComonoid S) (CofreeP.comonoid P))
    (h : CofreeP.restrict (stateComonoid S) hom = system) :
    hom = system.cofreeMate := by
  calc
    hom = CofreeP.extend (stateComonoid S)
        (CofreeP.restrict (stateComonoid S) hom) :=
      (CofreeP.extend_restrict _ hom).symm
    _ = CofreeP.extend (stateComonoid S) system := congrArg _ h
    _ = system.cofreeMate := rfl

/-- The existing cofree trajectory is the mate's behavior shape labelled by
the position exposed at every state. -/
theorem trajectory_eq_selfLabel_cofreeMate
    (system : DynSystem S P) (state : S) :
    system.trajectory state =
      M.selfLabel (system.cofreeMate.toLens.toFunA state) := by
  rw [cofreeMate_toFunA]
  exact system.trajectory_eq_selfLabel_behavior state

end Mate

end DynSystem
end PFunctor
