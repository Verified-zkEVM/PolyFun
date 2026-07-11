/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Coalgebra
public import PolyFun.PFunctor.Lens.Basic
import Batteries.Tactic.Lint

/-!
# Dynamical systems as dependent lenses

Following Niu–Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*
(Chapter 4), a **`p`-dynamical system with states `S`** *is* a dependent lens out
of the self-monomial state polynomial: `DynSystem S p` is definitionally
`Lens (selfMonomial S) p`, so the entire `PFunctor.Lens` combinator library
applies to dynamical systems on the nose — wrapping a system along a wiring lens
is literally lens composition. The lens's position map is the system's `expose`
(what the system reads off its state, valued in the positions `p.A`) and its
direction map is `update` (how an incoming direction `p.B (expose s)` evolves the
state); both are provided as definitional accessors under the dynamical names.
Equivalently, repackaging `expose` / `update` as `out : S → p.Obj S`
(`DynSystem.out`) exhibits a dynamical system as an F-coalgebra of the extension
functor of `p`, with a `Coalg p.Obj` instance: dynamical systems are the
coalgebras of polynomial functors.

* `PFunctor.DynSystem S p` — a `p`-dynamical system with state set `S`, i.e. a
  lens `selfMonomial S ⟹ p`.
* `PFunctor.MooreMachine S O I` — the special case over the interface `O X^ I`
  (output set `O`, input set `I`), recovering classical Moore machines.
* `PFunctor.DeterministicAutomaton O I` — a Moore machine with a distinguished start state.

The combinators that build new systems from old (parallel product, wrappers,
wiring diagrams) live in `PolyFun.PFunctor.Dynamical.Combinators`; running a
system lives in `PolyFun.PFunctor.Dynamical.Run` and `…Dynamical.Trajectory`.
-/

@[expose] public section

universe u uA uB uO uI

namespace PFunctor

/-- A **`p`-dynamical system with states `S`** (Niu–Spivak §4.1): a dependent
lens `selfMonomial S ⟹ p`. Under the dynamical accessors this is

* `expose : S → p.A` — the position the system currently presents (the lens's
  position map `toFunA`), and
* `update : (s : S) → p.B (expose s) → S` — the next state, given a direction at
  the exposed position (the lens's direction map `toFunB`).

The identification is definitional — "a dynamical system *is* a lens" — so lens
combinators, lens equalities, and the diagrammatic composition `⨟` apply to
dynamical systems directly. -/
abbrev DynSystem (S : Type u) (p : PFunctor.{uA, uB}) : Type _ :=
  Lens (selfMonomial S) p

namespace DynSystem

variable {S : Type u} {p : PFunctor.{uA, uB}}

/-- The position exposed at each state (the "output" of the system): the lens's
position map under its dynamical name. -/
def expose (s : DynSystem S p) : S → p.A := s.toFunA

/-- The transition: given a direction at the exposed position, the next state.
The lens's direction map under its dynamical name. -/
def update (s : DynSystem S p) : (st : S) → p.B (s.expose st) → S := s.toFunB

/-- Build a dynamical system from its dynamical data; definitionally `Lens.mk`
(and so also writable as `expose ⇆ update`). -/
def mk' (expose : S → p.A) (update : (st : S) → p.B (expose st) → S) :
    DynSystem S p :=
  expose ⇆ update

@[simp] theorem expose_mk' (e : S → p.A) (t : (st : S) → p.B (e st) → S) :
    (mk' e t).expose = e := rfl

@[simp] theorem update_mk' (e : S → p.A) (t : (st : S) → p.B (e st) → S) :
    (mk' e t).update = t := rfl

/-- Normalize the lens position map of a dynamical system to `expose`. -/
@[simp] theorem toFunA_eq_expose (s : DynSystem S p) : s.toFunA = s.expose := rfl

/-- Normalize the lens direction map of a dynamical system to `update`. -/
@[simp] theorem toFunB_eq_update (s : DynSystem S p) : s.toFunB = s.update := rfl

/-! ## The coalgebra structure map -/

/-- The coalgebra structure map of a dynamical system: at each state, the exposed
position together with the transition function at that position. A `DynSystem S p`
is exactly a coalgebra `S → p.Obj S` of the extension functor of `p`, unpacked
into the `expose` / `update` accessors. -/
def out (s : DynSystem S p) (st : S) : p.Obj S := ⟨s.expose st, s.update st⟩

@[simp] theorem out_fst (s : DynSystem S p) (st : S) : (s.out st).1 = s.expose st := rfl

@[simp] theorem out_snd (s : DynSystem S p) (st : S) (d : p.B (s.expose st)) :
    (s.out st).2 d = s.update st d := rfl

/-- Every dynamical system is an F-coalgebra of its interface's extension functor.
Not an instance: with the state a parameter, the system no longer appears in the
class's return type, so synthesis could not select one. -/
@[reducible] def coalg (s : DynSystem S p) : Coalg p.Obj S := ⟨s.out⟩

end DynSystem

/-! ## Moore machines and deterministic automata -/

/-- A **Moore machine** with states `S`, output set `O` and input set `I`: a
dynamical system over the interface `monomial O I = O X^ I`. Unpacking,
`expose : S → O` is the Moore output and `update : S → I → S` is the transition
function (Niu–Spivak §4.1). -/
abbrev MooreMachine (S : Type u) (O : Type uO) (I : Type uI) : Type _ :=
  DynSystem S (monomial O I)

namespace MooreMachine

variable {S : Type u} {O : Type uO} {I : Type uI}

/-- The Moore output at each state. -/
def output (m : MooreMachine S O I) : S → O := m.expose

/-- The transition function `S → I → S`. -/
def transition (m : MooreMachine S O I) : S → I → S := m.update

/-- Build a Moore machine from an output function and a transition function,
using the classical field names; definitionally `out ⇆ tr`. -/
def mk' (out : S → O) (tr : S → I → S) : MooreMachine S O I := out ⇆ tr

@[simp] theorem output_mk' (out : S → O) (tr : S → I → S) :
    (mk' out tr).output = out := rfl

@[simp] theorem transition_mk' (out : S → O) (tr : S → I → S) :
    (mk' out tr).transition = tr := rfl

end MooreMachine

/-- A **deterministic automaton** over input alphabet `I` with observation set
`O` (commonly `O = Bool` for acceptance): a state machine with an output, a
transition, and a distinguished start state (Niu–Spivak §4.1.1). It induces a
`MooreMachine` via `toMooreMachine`. -/
structure DeterministicAutomaton (O : Type uO) (I : Type uI) where
  /-- The set of states. -/
  State : Type u
  /-- The output observed at each state. -/
  output : State → O
  /-- The transition function. -/
  transition : State → I → State
  /-- The initial state. -/
  start : State

namespace DeterministicAutomaton

variable {O : Type uO} {I : Type uI}

/-- The Moore machine underlying a deterministic automaton (forgetting the start state). -/
def toMooreMachine (a : DeterministicAutomaton O I) : MooreMachine a.State O I :=
  MooreMachine.mk' a.output a.transition

end DeterministicAutomaton

/-! ## Closed systems, points, and sections -/

/-- A **point** of an interface `p` is a lens `X ⟹ p` (the book's `y ⟹ p`): it
picks a position and discards directions, so `Point p ≅ p.A`. It is the data of a
generalized element of the interface, not enough on its own to close a system. -/
abbrev Point (p : PFunctor.{uA, uB}) : Type _ := Lens X.{uA, uB} p

/-- A **section** of an interface `p` is a lens `p ⟹ X` (the book's `p ⟹ y`),
equivalently a dependent section `(a : p.A) → p.B a` choosing a direction at every
position. Composing a section after a system's interface lens closes the system off
(Niu–Spivak §4.3.4); see `DynSystem.close`. This is `Lens.enclose p` with the unit's
universes instantiated at those of `p`. -/
abbrev Section (p : PFunctor.{uA, uB}) : Type _ := Lens p X.{uA, uB}

/-- The section `p ⟹ X` picking the direction `σ a` at each position `a`. Unpacking
a `Section p`, the position map is trivial and the direction map is `σ`. -/
def sectionLens {p : PFunctor.{uA, uB}} (σ : (a : p.A) → p.B a) : Section p :=
  (fun _ => PUnit.unit) ⇆ (fun a _ => σ a)

/-- A **closed** dynamical system on states `S` is an `X`-system: its interface is
the composition unit, so the dynamics reduce to a pure state endofunction. -/
-- `Closed`'s universes are the composition-unit interface's independent position (`uA`) and
-- direction (`uB`) universes; kept separate for generality.
@[nolint checkUnivs]
abbrev Closed (S : Type u) : Type _ := DynSystem S X.{uA, uB}

namespace Closed

variable {S : Type u}

/-- The pure state transition of a closed system. -/
def step (s : Closed S) (st : S) : S := s.update st PUnit.unit

/-- The state of a closed system after `n` steps from `st`: the `n`-fold iterate of
`step`. The closed system runs autonomously, so its behaviour is this ℕ-indexed
trajectory of states. -/
def iterate (s : Closed S) (st : S) : ℕ → S := fun n => s.step^[n] st

@[simp] theorem iterate_zero (s : Closed S) (st : S) : s.iterate st 0 = st := rfl

theorem iterate_succ (s : Closed S) (st : S) (n : ℕ) :
    s.iterate st (n + 1) = s.iterate (s.step st) n := rfl

end Closed

end PFunctor
