/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Dynamical systems as dependent lenses

Following Niu–Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*
(Chapter 4), a **`p`-dynamical system** is a dependent lens out of a
self-monomial state polynomial: `selfMonomial State ⟹ p`. Unpacking the lens
gives a state set together with an `expose` map (what the system reads off its
state, valued in the positions `p.A`) and an `update` map (how an incoming
direction `p.B (expose s)` evolves the state). We bundle the state existentially
as a `structure` for ergonomics and record the round-trip identification with the
lens form (`toLens` / `ofLens`), so the entire `PFunctor.Lens` combinator library
applies to dynamical systems.

* `PFunctor.DynSystem p` — a `p`-dynamical system.
* `PFunctor.MooreMachine O I` — the special case over the interface `O X^ I`
  (output set `O`, input set `I`), recovering classical Moore machines.
* `PFunctor.DetAutomaton O I` — a Moore machine with a distinguished start state.

The combinators that build new systems from old (parallel product, wrappers,
wiring diagrams) live in `PolyFun.PFunctor.Dynamical.Combinators`; running a
system lives in `PolyFun.PFunctor.Dynamical.Run` and `…Dynamical.Trajectory`.
-/

@[expose] public section

universe u v uA uB uO uI

namespace PFunctor

/-- A **`p`-dynamical system** (Niu–Spivak §4.1): a state set together with the
data of a dependent lens `selfMonomial State ⟹ p`, unpacked into

* `expose : State → p.A` — the position the system currently presents, and
* `update : (s : State) → p.B (expose s) → State` — the next state, given a
  direction at the exposed position.

The lens identification is `toLens` / `ofLens`. -/
structure DynSystem (p : PFunctor.{uA, uB}) where
  /-- The set of states of the system. -/
  State : Type u
  /-- The position exposed at each state (the "output" of the system). -/
  expose : State → p.A
  /-- The transition: given a direction at the exposed position, the next state. -/
  update : (s : State) → p.B (expose s) → State

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- The interface lens `selfMonomial State ⟹ p` of a dynamical system: the
"a dynamical system *is* a lens" identification. -/
def toLens (s : DynSystem p) : Lens (selfMonomial s.State) p :=
  s.expose ⇆ s.update

/-- Build a dynamical system from a state set and an interface lens
`selfMonomial S ⟹ p`. -/
def ofLens {S : Type u} (l : Lens (selfMonomial S) p) : DynSystem p where
  State := S
  expose := l.toFunA
  update := l.toFunB

@[simp] theorem toLens_ofLens {S : Type u} (l : Lens (selfMonomial S) p) :
    (ofLens l).toLens = l := rfl

@[simp] theorem ofLens_toLens (s : DynSystem p) : ofLens s.toLens = s := rfl

@[simp] theorem toLens_toFunA (s : DynSystem p) : s.toLens.toFunA = s.expose := rfl

@[simp] theorem toLens_toFunB (s : DynSystem p) : s.toLens.toFunB = s.update := rfl

/-- One interactive step: from state `st`, the system exposes a position; given a
direction `d` at that position, `step` produces the next state. -/
def step (s : DynSystem p) (st : s.State) (d : p.B (s.expose st)) : s.State :=
  s.update st d

@[simp] theorem step_eq_update (s : DynSystem p) (st : s.State)
    (d : p.B (s.expose st)) : s.step st d = s.update st d := rfl

end DynSystem

/-! ## Moore machines and deterministic automata -/

/-- A **Moore machine** with output set `O` and input set `I`: a dynamical system
over the interface `monomial O I = O X^ I`. Unpacking, `expose : State → O` is
the Moore output and `update : State → I → State` is the transition function
(Niu–Spivak §4.1). -/
abbrev MooreMachine (O : Type uO) (I : Type uI) : Type _ := DynSystem (monomial O I)

namespace MooreMachine

variable {O : Type uO} {I : Type uI}

/-- The Moore output at each state. -/
def output (m : MooreMachine O I) : m.State → O := m.expose

/-- The transition function `State → I → State`. -/
def transition (m : MooreMachine O I) : m.State → I → m.State := m.update

/-- Build a Moore machine from a state set, an output function and a transition
function, using the classical field names. -/
def mk' {S : Type u} (out : S → O) (tr : S → I → S) : MooreMachine O I :=
  ⟨S, out, tr⟩

@[simp] theorem output_mk' {S : Type u} (out : S → O) (tr : S → I → S) :
    (mk' out tr).output = out := rfl

@[simp] theorem transition_mk' {S : Type u} (out : S → O) (tr : S → I → S) :
    (mk' out tr).transition = tr := rfl

end MooreMachine

/-- A **deterministic automaton** over input alphabet `I` with observation set
`O` (commonly `O = Bool` for acceptance): a state machine with an output, a
transition, and a distinguished start state (Niu–Spivak §4.1.1). It induces a
`MooreMachine` via `toMooreMachine`. -/
structure DetAutomaton (O : Type uO) (I : Type uI) where
  /-- The set of states. -/
  State : Type u
  /-- The output observed at each state. -/
  output : State → O
  /-- The transition function. -/
  transition : State → I → State
  /-- The initial state. -/
  start : State

namespace DetAutomaton

variable {O : Type uO} {I : Type uI}

/-- The Moore machine underlying a deterministic automaton (forgetting the start
state). -/
def toMooreMachine (a : DetAutomaton O I) : MooreMachine O I :=
  MooreMachine.mk' a.output a.transition

@[simp] theorem toMooreMachine_State (a : DetAutomaton O I) :
    a.toMooreMachine.State = a.State := rfl

end DetAutomaton

/-! ## Closed systems, points, and sections -/

/-- A **point** of an interface `p` is a lens `X ⟹ p` (the book's `y ⟹ p`): it
picks a position and discards directions, so `Point p ≅ p.A`. It is the data of a
generalized element of the interface, not enough on its own to close a system. -/
abbrev Point (p : PFunctor.{uA, uB}) : Type _ := Lens X p

/-- A **section** of an interface `p` is a lens `p ⟹ X` (the book's `p ⟹ y`),
equivalently a dependent section `(a : p.A) → p.B a` choosing a direction at every
position. Composing a section after a system's interface lens closes the system off
(Niu–Spivak §4.3.4); see `DynSystem.close`. This is defeq to `Lens.enclose p`. -/
abbrev Section (p : PFunctor.{uA, uB}) : Type _ := Lens p X

/-- The section `p ⟹ X` picking the direction `σ a` at each position `a`. Unpacking
a `Section p`, the position map is trivial and the direction map is `σ`. -/
def sectionLens {p : PFunctor.{uA, uB}} (σ : (a : p.A) → p.B a) : Section p :=
  (fun _ => PUnit.unit) ⇆ (fun a _ => σ a)

/-- A **closed** dynamical system is an `X`-system: its interface is the
composition unit, so the dynamics reduce to a pure state endofunction. -/
abbrev Closed : Type _ := DynSystem X.{uA, uB}

namespace Closed

/-- The pure state transition of a closed system. -/
def step (s : Closed) (st : s.State) : s.State :=
  s.update st PUnit.unit

/-- The state of a closed system after `n` steps from `st`: the `n`-fold iterate of
`step`. The closed system runs autonomously, so its behaviour is this ℕ-indexed
trajectory of states. -/
def iterate (s : Closed) (st : s.State) : ℕ → s.State :=
  fun n => (s.step)^[n] st

@[simp] theorem iterate_zero (s : Closed) (st : s.State) : s.iterate st 0 = st := rfl

theorem iterate_succ (s : Closed) (st : s.State) (n : ℕ) :
    s.iterate st (n + 1) = s.iterate (s.step st) n :=
  Function.iterate_succ_apply s.step n st

end Closed

end PFunctor
