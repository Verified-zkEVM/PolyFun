/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Init

/-!
# Environment-driven action alphabets

This file introduces `EnvAction m Event X`, a typed channel for
environment-fired events that update a per-step state via reactions
in an arbitrary monad `m`.

## Why a separate channel from `BoundaryAction`

`OpenProcess Party Δ` already has one effect channel: the
**boundary**, carrying port traffic *between participants* (Alice
sends a packet to the network, the network delivers to Bob). That
channel is the natural home for everything routed through ports.

But the environment can also act on a process directly, *without
going through any port*. In CJSV22 §3.2 the canonical example is
corruption: the environment may fire `compromise(m)` or
`refresh(m)` for a machine `m`, and crucially the adversary cannot
trigger this through Alice's input port. The same shape recurs
elsewhere: a global broadcast reset, a time-advance pulse, an
environment-controlled randomness reseed. None of these are
port-routed; all of them update bookkeeping state that the
adversary then observes.

`EnvAction` gives that pattern a typed home:

* `Event` is the alphabet of things the environment can fire (a
  user-supplied sum type, e.g.
  `compromise(m) | refresh(m) | broadcastReset`).
* `X` is the bookkeeping state the events mutate (corruption flags,
  epoch counters, broadcast clocks).
* `react : Event → X → m X` is the per-event reaction, valued in
  whatever monad `m` the consumer chose (the identity monad for
  deterministic reactions, a probability monad for randomized ones,
  etc.).

Pairing an `OpenProcess` with an `EnvAction` then keeps the two
channels structurally orthogonal: port traffic through
`BoundaryAction`, environment effects through `EnvAction`. The
pairing is `EnvOpenProcess` in `EnvOpenProcess.lean`.

## "Env" vs "Event"

The naming `EnvAction Event X` is asymmetric on purpose:

* **`Env`** (in the type name) names *who* fires the action — the
  environment, in the UC sense (one level above the adversary in
  the CJSV22 universe; not adversary-accessible directly).
* **`Event`** (the alphabet parameter) names *what* they fire.

So `EnvAction m Event X` reads as "actions fired by the environment,
drawn from the `Event` alphabet, mutating state of type `X` in
monad `m`". The two `Env`/`Event` are not redundant: `Env` carries
security-relevant routing info (env-only, not adversary-accessible),
`Event` is just the algebra of messages.

The alphabet parameter is named `Event` rather than the CJSV22-style
`Σ` because `Σ` is a reserved Lean keyword (sigma types). The CSP /
π-calculus convention "events" is also a more literal description of
what the alphabet contains than the bare letter `Σ`.

## Monad-parametric reactions

`react` is `m X`-valued for an arbitrary monad `m`, so environment-
driven state transitions can themselves be effectful in whatever way
the consumer needs (deterministic via `Id`, probabilistic via a
probability monad, oracle-using via a free interaction monad, etc.).
Deterministic events use `pure ∘ update` and pay no extra cost.

Crypto-flavored consumers (e.g. VCV-io) instantiate `m := ProbComp`
to recover the original probabilistic-corruption interface; this
file itself depends only on `Pure` / `Monad` from `Mathlib.Init`.

## Additive design

`EnvAction` is intentionally **standalone**: it is *not* threaded
into `OpenNodeProfile`. Existing `OpenProcess Party Δ`
constructions are unaffected, and protocols that do not need
environment-driven events incur zero cost. The corruption-aware
wrapper that pairs an `OpenProcess` with a state-indexed
`EnvAction` lives in `EnvOpenProcess.lean`; the canonical CJSV22
instantiation (corruption with refresh-based healing) lives in
`MomentaryCorruption.lean`.
-/

universe u v w

namespace Interaction
namespace UC

/--
`EnvAction m Event X` is the per-event reaction of a per-step state
`x : X` to environment events drawn from the alphabet `Event`,
returning a value in monad `m`.

`react : Event → X → m X` specifies how each event transforms the
state. The default `react` is `fun _ x => pure x` (every event is a
no-op), which keeps the empty alphabet `Event := Empty` trivially
satisfiable; this default requires `[Pure m]`.

Two concrete instantiations matter here:

* `EnvAction m Empty X` — the trivial alphabet, used by every
  protocol that doesn't participate in environment-driven corruption.
  Costs nothing; the canonical inhabitant is `EnvAction.empty`.
* `EnvAction m (MomentaryCorruption.Alphabet Sid Pid)
  (MomentaryCorruption.State Sid Pid)` — the canonical CJSV22
  instantiation, with the consumer choosing `m` (typically a
  probability monad downstream).

The structure is independent of the boundary `Δ` so that environment
events are *not* keyed by port: an environment event acts on whatever
`X`-typed slice of state the protocol exposes, with no dependence on
which ports happen to be in scope.

Categorically this is a **Kleisli Mealy machine**: an event-indexed state
transition valued in the Kleisli category of `m`. It is intentionally not
unified with `PFunctor.DynSystem` — dynamical systems are pure coalgebras
`State → p.Obj State`, and identifying monadic transition systems with
dynamical systems would require a monadic-dynamical abstraction (coalgebras of
the composite `m ∘ p.Obj`) that the library does not yet provide.
-/
@[ext]
structure EnvAction (m : Type v → Type w) (Event : Type u) (X : Type v)
    [Pure m] where
  /-- The state transition triggered by each event. -/
  react : Event → X → m X := fun _ x => pure x

namespace EnvAction

variable {m : Type v → Type w} {Event : Type u} {X : Type v}

/--
The trivial environment-action over the empty alphabet: no events
ever fire.

Useful as the default for processes that do not care about
environment-driven dynamics.
-/
def empty [Pure m] (X : Type v) : EnvAction m Empty X where
  react e _ := e.elim

/--
The constant environment-action: every event leaves the state
unchanged.

This is the canonical "passive observer" reaction, useful when a
process participates in an alphabet (so its `EnvAction` slot is
non-trivially typed) but its state has no per-event update.
-/
def passive [Pure m] (Event : Type u) (X : Type v) : EnvAction m Event X where
  react _ x := pure x

/--
Adapt the alphabet of an environment-action along a function
`g : Event → Event'`.

The new alphabet is `Event`; an event `s : Event` is reacted to by
routing it through `g` to obtain `s' : Event'` and applying the
original reaction. This is the contravariant action on the alphabet
that lets coarser alphabets be embedded into finer ones.
-/
def comap [Pure m] {Event Event' : Type u} {X : Type v}
    (g : Event → Event') (e : EnvAction m Event' X) : EnvAction m Event X where
  react s x := e.react (g s) x

/--
Adapt the state of an environment-action along a state-projection.

Given `e : EnvAction m Event X` and a projection `π : Y → X` together
with a re-installation `ι : X → Y → Y` that re-installs the updated
`X` slice into a larger state `Y`, the lifted action operates on `Y`
by reacting on the `X`-slice and re-installing the result.

This is the structural lift used when corruption-aware reactions need
to thread through richer per-step states; the `MomentaryCorruption`
layer uses it to lift the canonical `MomentaryCorruption.react` over
state-bundled `MachineProcess`es.
-/
def liftState [Monad m] {Event : Type u} {X Y : Type v}
    (π : Y → X) (ι : X → Y → Y) (e : EnvAction m Event X) :
    EnvAction m Event Y where
  react s y := do
    let x' ← e.react s (π y)
    return ι x' y

@[simp]
theorem comap_id [Pure m] (e : EnvAction m Event X) :
    comap (id : Event → Event) e = e := by
  ext s x; rfl

@[simp]
theorem comap_comap [Pure m] {Event Event' Event'' : Type u} {X : Type v}
    (h : Event → Event') (g : Event' → Event'') (e : EnvAction m Event'' X) :
    comap h (comap g e) = comap (g ∘ h) e := by
  ext s x; rfl

@[simp]
theorem passive_react [Pure m] (Event : Type u) (X : Type v) (s : Event) (x : X) :
    (passive (m := m) Event X).react s x = pure x := rfl

@[simp]
theorem empty_react [Pure m] (X : Type v) (e : Empty) (x : X) :
    (empty (m := m) X).react e x = e.elim := rfl

end EnvAction

end UC
end Interaction
