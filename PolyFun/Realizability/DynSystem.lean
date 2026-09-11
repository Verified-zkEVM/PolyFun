/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.Realizability.StepClass

/-!
# Realizability of polynomial dynamical systems

This file places the first-order realizability boundary directly on a
`PFunctor.DynSystem`.  A system exposes a position and accepts a direction in
the fiber over that position; a complexity class, however, constrains ordinary
functions between represented types.  The two machine-facing maps are:

* `DynSystem.expose : State → p.A`, already provided by the dynamical layer;
* `DynSystem.update? : State × p.Idx → Option State`, the transition flattened
  over the whole dependent index space.

The flattened update is partial for the same reason as
`DynComputation.update?`: a tagged direction whose position is not currently
exposed is not an enabled step.  Keeping that fact as `none` is what allows
interface translations and later process composition to preserve a meaningful
cost boundary.

`DynSystem.Boundary` pins representations of the interface, while
`DynSystem.Realization` chooses the private state representation and an
admissible partial extension of the dependent update.  The extension need only
agree on enabled directions; its behavior on mismatched tags is operationally
irrelevant.  This avoids demanding decidable equality on semantic positions
such as decorated type trees, while still giving a uniform first-order machine
map.  The sibling `DynComputation` realizability boundary in
`PolyFun.Realizability.Basic` constrains returning computations over the
resumption polynomial instead; the two tracks share `StepClass` but neither is
defined in terms of the other.
-/

@[expose] public section

universe u v uS uA uB uA₂ uB₂ vA vB vA₂ vB₂

namespace PFunctor

/- Lean compares the sigma presentations of polynomial objects and indices at
implicit transparency in the flattened maps below. -/
attribute [local implicit_reducible] PFunctor.Obj PFunctor.Idx
  DynSystem.wrap DynSystem.expose DynSystem.update

namespace DynSystem

variable {p q : PFunctor.{u, u}} {State : Type u}

/-! ## Universe normalization -/

/-- Lift both ends of a polynomial lens, preserving its position map and
dependent direction pullback under `ULift`. -/
def _root_.PFunctor.Lens.uliftMap
    {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}} (lens : Lens p q) :
    Lens (PFunctor.ulift.{uA, uB, vA, vB} p)
      (PFunctor.ulift.{uA₂, uB₂, vA₂, vB₂} q) where
  toFunA position := ULift.up (lens.toFunA position.down)
  toFunB position direction :=
    ULift.up (lens.toFunB position.down direction.down)

/-- Lift a dynamical system's state, positions, and directions into one common
universe.  `StepClass` constrains functions between types in a fixed universe;
this normalization is the bridge for systems such as `ProcessOver`, whose
state, decorated-step, and path types naturally occupy different universes. -/
def ulift {p : PFunctor.{uA, uB}} {State : Type uS}
    (system : DynSystem State p) :
    DynSystem (ULift.{max uA uB, uS} State)
      (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} p) :=
  mk'
    (fun state => ULift.up (system.expose state.down))
    (fun state direction => ULift.up (system.update state.down direction.down))

@[simp] theorem ulift_expose {p : PFunctor.{uA, uB}} {State : Type uS}
    (system : DynSystem State p) (state : ULift.{max uA uB, uS} State) :
    (DynSystem.ulift system).expose state = ULift.up (system.expose state.down) := rfl

@[simp] theorem ulift_update {p : PFunctor.{uA, uB}} {State : Type uS}
    (system : DynSystem State p) (state : ULift.{max uA uB, uS} State)
    (direction :
      (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} p).B
        ((DynSystem.ulift system).expose state)) :
    (DynSystem.ulift system).update state direction =
      ULift.up (system.update state.down direction.down) := rfl

/-- Universe normalization commutes with wrapping a system along a lens when
the source and target interfaces occupy the same universe pair. -/
theorem ulift_wrap {p q : PFunctor.{uA, uB}} {State : Type uS}
    (system : DynSystem State p) (lens : Lens p q) :
    DynSystem.ulift (system.wrap lens) =
      (DynSystem.ulift system).wrap
        (lens.uliftMap.{uA, uB, uA, uB, max uS uB, max uS uA,
          max uS uB, max uS uA}) := rfl

/-! ## First-order step maps -/

/-- The transition of a dynamical system flattened over the whole polynomial
index space.  A mismatched position tag is not an enabled transition and is
reported as `none`. -/
def update? [DecidableEq p.A] (system : DynSystem State p) :
    State × p.Idx → Option State := fun step =>
  if h : step.2.1 = system.expose step.1 then
    some (system.update step.1 (h ▸ step.2.2))
  else none

theorem update?_of_eq [DecidableEq p.A] (system : DynSystem State p)
    (state : State) (direction : p.B (system.expose state)) :
    system.update? (state, ⟨system.expose state, direction⟩) =
      some (system.update state direction) := by
  unfold update?
  rw [dite_eq_left rfl]

theorem update?_of_ne [DecidableEq p.A] (system : DynSystem State p)
    (state : State) (index : p.Idx) (hne : index.1 ≠ system.expose state) :
    system.update? (state, index) = none := by
  unfold update?
  rw [dite_eq_right hne]

/-! ## Realizability boundaries and witnesses -/

/-- Pinned representations of a dynamical system's exposed positions and
flattened direction indices.  These are parameters of a realizability claim,
never existentially selected by the machine. -/
structure Boundary (C : StepClass.{u, v}) (p : PFunctor.{u, u}) : Type v where
  /-- Representation of the polynomial's positions. -/
  pos : C.Str p.A
  /-- Representation of the polynomial's flattened index space. -/
  idx : C.Str p.Idx

namespace Boundary

variable {C : StepClass.{u, v}}

/-- Representation of the flattened transition domain. -/
def stateIdx [P : C.HasProd] (bd : Boundary C p) {S : Type u}
    (state : C.Str S) : C.Str (S × p.Idx) :=
  P.prod state bd.idx

end Boundary

/-- A realization of a fixed dynamical system by `C`-admissible first-order
step maps.  The system state is private and therefore receives an existentially
chosen representation; interface representations are fixed by `bd`. -/
structure Realization (C : StepClass.{u, v}) [C.HasProd] [C.HasOption]
    (bd : Boundary C p) (system : DynSystem State p) : Type (max u v) where
  /-- Representation selected for the private state space. -/
  state : C.Str State
  /-- Exposing the current interface position is admissible. -/
  expose_mem : C.Hom state bd.pos system.expose
  /-- A first-order partial extension of the dependent transition. -/
  update? : State × p.Idx → Option State
  /-- The chosen partial extension is admissible. -/
  update_mem : C.Hom (bd.stateIdx state) (StepClass.HasOption.option state)
    update?
  /-- The extension agrees with the dynamical system on every enabled
  direction.  No condition is imposed on mismatched position tags. -/
  update?_enabled : ∀ (state : State) (direction : p.B (system.expose state)),
    update? (state, ⟨system.expose state, direction⟩) =
      some (system.update state direction)

/-- A system is realizable at `bd` when its fixed dynamics admit some private
state representation making both first-order step maps admissible. -/
abbrev IsRealizableBy (C : StepClass.{u, v}) [C.HasProd] [C.HasOption]
    (bd : Boundary C p) (system : DynSystem State p) : Prop :=
  Nonempty (Realization C bd system)

/-! ## Interface transport -/

/-- Pull a flattened target index back along a lens at a supplied source
position.  A target index with a mismatched position tag has no preimage. -/
def _root_.PFunctor.Lens.pullPosIdx [DecidableEq q.A] (lens : Lens p q) :
    p.A × q.Idx → Option p.Idx := fun input =>
  if h : input.2.1 = lens.toFunA input.1 then
    some ⟨input.1, lens.toFunB input.1 (h ▸ input.2.2)⟩
  else none

/-- Admissibility data required to transport a dynamical realization along a
lens.  It constrains the position map and the flattened dependent pullback. -/
structure _root_.PFunctor.Lens.IsDynAdmissible
    (C : StepClass.{u, v}) [C.HasProd] [C.HasOption]
    {p q : PFunctor.{u, u}}
    (source : Boundary C p) (target : Boundary C q) (lens : Lens p q) where
  /-- The lens position map is admissible. -/
  onPos : C.Hom source.pos target.pos lens.toFunA
  /-- A first-order partial extension of the dependent index pullback. -/
  pull? : p.A × q.Idx → Option p.Idx
  /-- Pulling a target index back at a source position is admissible. -/
  onPull : C.Hom
    (StepClass.HasProd.prod source.pos target.idx)
    (StepClass.HasOption.option source.idx) pull?
  /-- The extension agrees with the lens on every enabled target direction. -/
  pull?_enabled : ∀ (position : p.A) (direction : q.B (lens.toFunA position)),
    pull? (position, ⟨lens.toFunA position, direction⟩) =
      some ⟨position, lens.toFunB position direction⟩

/-- Interface transport along an admissible lens preserves structural
realizability. -/
theorem IsRealizableBy.wrap {C : StepClass.{u, v}} [P : C.HasProd]
    [O : C.HasOption]
    {source : Boundary C p} {target : Boundary C q} {system : DynSystem State p}
    {lens : Lens p q} (hlens : lens.IsDynAdmissible C source target)
    (h : IsRealizableBy C source system) :
    IsRealizableBy C target (system.wrap lens) := by
  obtain ⟨R⟩ := h
  refine ⟨⟨R.state, ?_,
    (fun input => (hlens.pull? (system.expose input.1, input.2)).bind
      fun sourceIndex => R.update? (input.1, sourceIndex)), ?_, ?_⟩⟩
  · exact (C.comp_mem R.expose_mem hlens.onPos).congr fun _ => rfl
  · have hpull : C.Hom (P.prod R.state target.idx) (O.option source.idx)
        fun input => hlens.pull? (system.expose input.1, input.2) := by
      exact (C.comp_mem (P.map_mem R.expose_mem (C.id_mem target.idx))
        hlens.onPull).congr fun _ => rfl
    have hpullState : C.Hom (P.prod R.state target.idx)
        (P.prod (O.option source.idx) R.state)
        fun input => (hlens.pull? (system.expose input.1, input.2), input.1) :=
      P.pair_mem hpull (P.fst_mem R.state target.idx)
    have hupdate : C.Hom (P.prod source.idx R.state) (O.option R.state)
        fun input => R.update? (input.2, input.1) := by
      exact (C.comp_mem (P.swap_mem source.idx R.state) R.update_mem).congr fun _ => rfl
    exact C.comp_mem hpullState (O.obindCtx_mem hupdate)
  · intro state direction
    change q.B (lens.toFunA (system.expose state)) at direction
    change (hlens.pull? (system.expose state,
      ⟨lens.toFunA (system.expose state), direction⟩)).bind
        (fun sourceIndex => R.update? (state, sourceIndex)) =
      some ((system.wrap lens).update state direction)
    rw [hlens.pull?_enabled, Option.bind_some, R.update?_enabled]
    exact congrArg some (wrap_update lens system state direction).symm

end DynSystem

end PFunctor
