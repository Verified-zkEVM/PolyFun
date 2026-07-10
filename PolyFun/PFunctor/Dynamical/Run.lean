/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.System

/-!
# Running dynamical systems

The run semantics of dynamical systems: finite and infinite orbits of a general
`p`-system, and the classical input-driven semantics of Moore machines
(Niu–Spivak §4.1: a Moore machine consumes a sequence of inputs, threading the
state through its transition function and observing an output at each visited
state).

For a general `p`-system:

* `DynSystem.Prefix` — a finite orbit: a chosen direction at each visited state.
* `DynSystem.Run` — an infinite orbit: the state at each time, the direction
  chosen there, and the proof that states follow the transition; with
  `Run.take` truncating to a `Prefix` and `Run.eventsUpTo` / `Run.ticketsUpTo`
  reading off labels along the way.
* `DynSystem.Run.RelUpTo` / `DynSystem.Run.Rel` — step-by-step matching of two
  runs by a `DirRel`.

For Moore machines and closed systems:

* `MooreMachine.stepInput` — a single input step.
* `MooreMachine.run` — the final state after folding a list of inputs.
* `MooreMachine.trace` — the list of outputs observed along the way (classical
  Moore semantics: one more output than inputs, including the initial output).
* `MooreMachine.outputOn` — the final output after consuming a word.
* `DeterministicAutomaton.accepts` — language membership for a Boolean automaton.
* `MooreMachine.streamRun` / `Closed.iterateRun` — the input-stream and
  closed-system orbits as generic `Run`s, with `state_eq_stateStream` /
  `state_eq_iterate` identifying every generic run with them.
-/

@[expose] public section

universe u u₁ u₂ uA uB uA₂ uB₂ uO uI w

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

/-! ## Finite and infinite orbits -/

/-- A length-`n` finite orbit of a `p`-system from `st`: at each step, a chosen
direction at the exposed position, then a shorter orbit from the successor
state. Unlike a run to quiescence, a `Prefix` may stop at any state, making it
the finite-truncation object for infinite runs (see `Run.take`). -/
inductive Prefix (s : DynSystem.{u} p) : s.State → ℕ → Sort _ where
  | /-- The empty orbit. -/
    nil {st : s.State} : Prefix s st 0
  | /-- Extend an orbit by one chosen direction at the current state. -/
    step {st : s.State} {n : ℕ} (d : p.B (s.expose st)) :
      Prefix s (s.update st d) n → Prefix s st n.succ

namespace Prefix

/-- The stable event labels attached to the steps of a finite orbit. -/
def events {s : DynSystem.{u} p} {Event : Type w} (eventMap : s.EventMap Event) :
    {st : s.State} → {n : ℕ} → Prefix s st n → List Event
  | _, _, .nil => []
  | st, _, .step d tail => eventMap st d :: tail.events eventMap

/-- The stable tickets attached to the steps of a finite orbit. -/
def tickets {s : DynSystem.{u} p} {Ticket : Type w} (ticketMap : s.Tickets Ticket) :
    {st : s.State} → {n : ℕ} → Prefix s st n → List Ticket
  | _, _, .nil => []
  | st, _, .step d tail => ticketMap st d :: tail.tickets ticketMap

@[simp] theorem events_nil {s : DynSystem.{u} p} {Event : Type w}
    (eventMap : s.EventMap Event) {st : s.State} :
    events eventMap (.nil : Prefix s st 0) = [] := rfl

@[simp] theorem tickets_nil {s : DynSystem.{u} p} {Ticket : Type w}
    (ticketMap : s.Tickets Ticket) {st : s.State} :
    tickets ticketMap (.nil : Prefix s st 0) = [] := rfl

@[simp] theorem events_step {s : DynSystem.{u} p} {Event : Type w}
    (eventMap : s.EventMap Event) {st : s.State} {n : ℕ}
    (d : p.B (s.expose st)) (tail : Prefix s (s.update st d) n) :
    events eventMap (.step d tail) = eventMap st d :: tail.events eventMap := rfl

@[simp] theorem tickets_step {s : DynSystem.{u} p} {Ticket : Type w}
    (ticketMap : s.Tickets Ticket) {st : s.State} {n : ℕ}
    (d : p.B (s.expose st)) (tail : Prefix s (s.update st d) n) :
    tickets ticketMap (.step d tail) = ticketMap st d :: tail.tickets ticketMap := rfl

end Prefix

/-- An infinite orbit of a `p`-system: the state at each time, the direction
chosen there, and the proof that the state stream follows the transition
function. The run does not introduce an operational state space of its own; it
records how a state evolves when one direction is chosen at each time. -/
structure Run (s : DynSystem.{u} p) where
  /-- The state at time `n`. -/
  state : ℕ → s.State
  /-- The direction chosen at the state visited at time `n`. -/
  dir : (n : ℕ) → p.B (s.expose (state n))
  /-- The state stream follows the transition function. -/
  next_state : ∀ n, state (n + 1) = s.update (state n) (dir n)

namespace Run

variable {s : DynSystem.{u} p}

/-- The initial state of a run. -/
def initial (r : Run s) : s.State := r.state 0

/-- The first direction chosen by a run. -/
def head (r : Run s) : p.B (s.expose r.initial) := r.dir 0

/-- The tail of a run after its first step. -/
def tail (r : Run s) : Run s where
  state n := r.state n.succ
  dir n := r.dir n.succ
  next_state n := r.next_state n.succ

/-- The initial state of `r.tail` is the successor of `r.initial` along the
first chosen direction. -/
theorem tail_initial (r : Run s) : r.tail.initial = s.update r.initial r.head :=
  r.next_state 0

/-- The length-`n` finite orbit truncating an infinite run. -/
def take (r : Run s) : (n : ℕ) → Prefix s r.initial n
  | 0 => .nil
  | n + 1 => .step r.head (r.tail_initial ▸ r.tail.take n)

@[simp] theorem take_zero (r : Run s) : r.take 0 = Prefix.nil := rfl

@[simp] theorem take_succ (r : Run s) (n : ℕ) :
    r.take (n + 1) = Prefix.step r.head (r.tail_initial ▸ r.tail.take n) := rfl

/-- The stable event label attached to step `n` of a run. -/
def event {Event : Type w} (eventMap : s.EventMap Event) (r : Run s) (n : ℕ) : Event :=
  eventMap (r.state n) (r.dir n)

/-- The stable event labels attached to the first `n` steps of a run. -/
def eventsUpTo {Event : Type w} (eventMap : s.EventMap Event) (r : Run s) : ℕ → List Event
  | 0 => []
  | n + 1 => r.event eventMap 0 :: r.tail.eventsUpTo eventMap n

/-- The stable ticket attached to step `n` of a run. -/
def ticket {Ticket : Type w} (ticketMap : s.Tickets Ticket) (r : Run s) (n : ℕ) : Ticket :=
  ticketMap (r.state n) (r.dir n)

/-- The stable tickets attached to the first `n` steps of a run. -/
def ticketsUpTo {Ticket : Type w} (ticketMap : s.Tickets Ticket) (r : Run s) : ℕ → List Ticket
  | 0 => []
  | n + 1 => r.ticket ticketMap 0 :: r.tail.ticketsUpTo ticketMap n

@[simp] theorem eventsUpTo_zero {Event : Type w} (eventMap : s.EventMap Event) (r : Run s) :
    r.eventsUpTo eventMap 0 = [] := rfl

@[simp] theorem eventsUpTo_succ {Event : Type w} (eventMap : s.EventMap Event)
    (r : Run s) (n : ℕ) :
    r.eventsUpTo eventMap (n + 1) = r.event eventMap 0 :: r.tail.eventsUpTo eventMap n := rfl

@[simp] theorem ticketsUpTo_zero {Ticket : Type w} (ticketMap : s.Tickets Ticket) (r : Run s) :
    r.ticketsUpTo ticketMap 0 = [] := rfl

@[simp] theorem ticketsUpTo_succ {Ticket : Type w} (ticketMap : s.Tickets Ticket)
    (r : Run s) (n : ℕ) :
    r.ticketsUpTo ticketMap (n + 1) = r.ticket ticketMap 0 :: r.tail.ticketsUpTo ticketMap n := rfl

/-! ## Matching two runs step-by-step -/

variable {s₁ : DynSystem.{u₁} p} {s₂ : DynSystem.{u₂} q}

/-- `RelUpTo rel r₁ r₂ n` states that the first `n` steps of the runs `r₁` and
`r₂` match step-by-step according to `rel`. -/
def RelUpTo (rel : DirRel s₁ s₂) (r₁ : Run s₁) (r₂ : Run s₂) : ℕ → Prop
  | 0 => True
  | n + 1 => rel (r₁.dir 0) (r₂.dir 0) ∧ RelUpTo rel r₁.tail r₂.tail n

/-- `Rel rel r₁ r₂` states that every finite prefix of the runs `r₁` and `r₂`
matches according to `rel`. -/
def Rel (rel : DirRel s₁ s₂) (r₁ : Run s₁) (r₂ : Run s₂) : Prop :=
  ∀ n, RelUpTo rel r₁ r₂ n

/-- Pointwise step matching implies prefix matching of the first `n` steps. -/
theorem relUpTo_of_pointwise (rel : DirRel s₁ s₂) (r₁ : Run s₁) (r₂ : Run s₂)
    (hrel : ∀ n, rel (r₁.dir n) (r₂.dir n)) : ∀ n, RelUpTo rel r₁ r₂ n := by
  intro n
  induction n generalizing r₁ r₂ with
  | zero => trivial
  | succ n ih => exact ⟨hrel 0, ih r₁.tail r₂.tail (fun k => hrel k.succ)⟩

/-- Pointwise step matching implies full run matching. -/
theorem rel_of_pointwise (rel : DirRel s₁ s₂) (r₁ : Run s₁) (r₂ : Run s₂)
    (hrel : ∀ n, rel (r₁.dir n) (r₂.dir n)) : Rel rel r₁ r₂ :=
  relUpTo_of_pointwise rel r₁ r₂ hrel

end Run

end DynSystem

namespace MooreMachine

variable {O : Type uO} {I : Type uI}

/-- A single input step of a Moore machine. -/
def stepInput (m : MooreMachine O I) (st : m.State) (i : I) : m.State := m.transition st i

/-- The state reached after consuming a list of inputs from `st`. -/
def run (m : MooreMachine O I) (st : m.State) : List I → m.State := List.foldl m.stepInput st

/-- The list of outputs observed while consuming a word, including the initial
output. Its length is `inputs.length + 1`. -/
def trace (m : MooreMachine O I) (st : m.State) : List I → List O
  | [] => [m.output st]
  | i :: is => m.output st :: m.trace (m.stepInput st i) is

/-- The final output after consuming a word from `st`. -/
def outputOn (m : MooreMachine O I) (st : m.State) (is : List I) : O := m.output (m.run st is)

@[simp] theorem run_nil (m : MooreMachine O I) (st : m.State) : m.run st [] = st := rfl

@[simp] theorem run_cons (m : MooreMachine O I) (st : m.State) (i : I) (is : List I) :
    m.run st (i :: is) = m.run (m.stepInput st i) is := rfl

theorem run_append (m : MooreMachine O I) (st : m.State) (is js : List I) :
    m.run st (is ++ js) = m.run (m.run st is) js := List.foldl_append

@[simp] theorem trace_length (m : MooreMachine O I) (st : m.State) (is : List I) :
    (m.trace st is).length = is.length + 1 := by
  induction is generalizing st <;> simp [trace, *]

/-! ## Streams

The behaviour of a Moore machine driven by an infinite stream of inputs
`ins : ℕ → I`: the state visited at each time, the output observed there, and the
identification with the finite `run` on every prefix. -/

/-- The state of the machine at time `n`, started from `st` and driven by the input
stream `ins`. -/
def stateStream (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) : ℕ → m.State
  | 0 => st
  | n + 1 => m.stepInput (m.stateStream st ins n) (ins n)

/-- The output observed at time `n` along the stream-driven run. -/
def outputStream (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) (n : ℕ) : O :=
  m.output (m.stateStream st ins n)

@[simp] theorem stateStream_zero (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) :
    m.stateStream st ins 0 = st := rfl

@[simp] theorem stateStream_succ (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) (n : ℕ) :
    m.stateStream st ins (n + 1) = m.stepInput (m.stateStream st ins n) (ins n) := rfl

/-- The stream-driven state at time `n` is the finite `run` on the first `n` inputs:
streams and finite runs agree on every prefix. -/
theorem stateStream_eq_run (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) (n : ℕ) :
    m.stateStream st ins n = m.run st ((List.range n).map ins) := by
  induction n <;> simp_all [List.range_succ, run_append]

end MooreMachine

namespace DeterministicAutomaton

variable {I : Type uI}

/-- Whether a Boolean deterministic automaton accepts a word: its final output is `true`. -/
def accepts (a : DeterministicAutomaton Bool I) (w : List I) : Prop :=
  a.toMooreMachine.outputOn a.start w = true

instance (a : DeterministicAutomaton Bool I) (w : List I) : Decidable (a.accepts w) :=
  inferInstanceAs (Decidable (_ = true))

end DeterministicAutomaton

/-! ## Input streams and iterates as generic runs

A Moore machine's directions are the constant input set, so an input stream *is*
a choice of direction at each time; a closed system's directions are trivial, so
it has exactly one run from each state. The identifications below express the
`stateStream` / `iterate` semantics as the generic `DynSystem.Run` orbits. -/

namespace MooreMachine

variable {O : Type uO} {I : Type uI}

/-- The generic run of a Moore machine driven by an input stream: the states are
`stateStream` and the chosen directions are the inputs themselves. -/
def streamRun (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) : DynSystem.Run m :=
  ⟨m.stateStream st ins, ins, fun _ => rfl⟩

@[simp] theorem streamRun_state (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) :
    (m.streamRun st ins).state = m.stateStream st ins := rfl

@[simp] theorem streamRun_dir (m : MooreMachine O I) (st : m.State) (ins : ℕ → I) :
    (m.streamRun st ins).dir = ins := rfl

/-- Every generic run of a Moore machine is the input-stream-driven state stream
from its initial state: runs of Moore machines are exactly `streamRun`s. -/
theorem state_eq_stateStream (m : MooreMachine O I) (run : DynSystem.Run m) (n : ℕ) :
    run.state n = m.stateStream run.initial run.dir n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run.next_state n, ih]; rfl

end MooreMachine

namespace Closed

/-- The unique generic run of a closed system from a state: its spine is the
`iterate` of states, and every direction is the trivial one. -/
def iterateRun (s : Closed) (st : s.State) : DynSystem.Run s :=
  ⟨s.iterate st, fun _ => PUnit.unit, fun n => Function.iterate_succ_apply' s.step n st⟩

@[simp] theorem iterateRun_state (s : Closed) (st : s.State) :
    (s.iterateRun st).state = s.iterate st := rfl

/-- Every generic run of a closed system is the `iterate` of its initial state:
closed systems run autonomously, so their runs are unique. -/
theorem state_eq_iterate (s : Closed) (run : DynSystem.Run s) (n : ℕ) :
    run.state n = s.iterate run.initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : run.state (n + 1) = s.step (run.state n) := run.next_state n
    rw [h, ih]
    exact (Function.iterate_succ_apply' s.step n run.initial).symm

end Closed

end PFunctor
