/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import Mathlib.Init

/-!
# Environment-event reactions

`EnvAction m Event X` bundles a reaction `Event → X → m X`. Typical uses include
compromise/refresh bookkeeping, resets, and clock updates. `EnvOpenProcess`
pairs such a reaction with an open process's port boundary.

The event alphabet and state are independent of ports. The consumer supplies
routing, scheduling, and authority to issue events; the type itself imposes no
access-control restriction or observation policy.

The structure requires only `[Pure m]`, for the default reaction that preserves
the state. `empty` handles an empty alphabet, `passive` preserves the state for
any event, `comap` adapts an alphabet, and `liftState` lifts a reaction to a
larger state using `[Monad m]`.

`MomentaryCorruption.envAction` in
`PolyFun/Interaction/UC/MomentaryCorruption.lean` is one instance, with event
type `MomentaryCorruption.Alphabet M` and state type `MomentaryCorruption.State M`.
Its updates require decidable equality on `M`.
-/

public section

universe u v w

namespace Interaction
namespace UC

/--
A reaction transforming an `X`-valued state for each event, with result in `m`.
The default reaction returns the supplied state through `pure`. Both the event
alphabet and state are independent of any port boundary or party type.
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
@[expose]
def empty [Pure m] (X : Type v) : EnvAction m Empty X where
  react e _ := e.elim

/--
The constant environment-action: every event leaves the state
unchanged.

This is the canonical "passive observer" reaction, useful when a
process participates in an alphabet (so its `EnvAction` slot is
non-trivially typed) but its state has no per-event update.
-/
@[expose]
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
@[expose]
def comap [Pure m] {Event Event' : Type u} {X : Type v}
    (g : Event → Event') (e : EnvAction m Event' X) : EnvAction m Event X where
  react s x := e.react (g s) x

/--
Lift a reaction to a larger state using a projection and an update function.
For an event and state `y : Y`, react on `π y`, then return `ι x' y` for the
resulting `x'`. Laws relating `π` and `ι` are separate assumptions when needed.
-/
def liftState [Monad m] {Event : Type u} {X Y : Type v}
    (π : Y → X) (ι : X → Y → Y) (e : EnvAction m Event X) : EnvAction m Event Y where
  react s y := do
    let x' ← e.react s (π y)
    return ι x' y

@[simp]
theorem comap_id [Pure m] (e : EnvAction m Event X) : comap (id : Event → Event) e = e := rfl

@[simp]
theorem comap_comap [Pure m] {Event Event' Event'' : Type u} {X : Type v}
    (h : Event → Event') (g : Event' → Event'') (e : EnvAction m Event'' X) :
    comap h (comap g e) = comap (g ∘ h) e := rfl

@[simp]
theorem passive_react [Pure m] (Event : Type u) (X : Type v) (s : Event) (x : X) :
    (passive (m := m) Event X).react s x = pure x := rfl

@[simp]
theorem empty_react [Pure m] (X : Type v) (e : Empty) (x : X) :
    (empty (m := m) X).react e x = e.elim := rfl

end EnvAction

end UC
end Interaction
