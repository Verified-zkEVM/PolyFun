/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Notation
public import PolyFun.IPFunctor.Notation.Indexed
public import PolyFun.IPFunctor.Notation.Deterministic

/-!
# Worked Examples for `IPFunctor.FreeM` / `IPFunctor.FreeM₂` and Their `do`-Notation

This module is a worked-examples companion to
[`docs/wiki/ipfunctor.md`](../../docs/wiki/ipfunctor.md) and
[`docs/wiki/ipfunctor-do-notation.md`](../../docs/wiki/ipfunctor-do-notation.md).
It exists to give the new `IPFunctor` surface concrete uses that compile inside
the library, distinct from the per-elaborator smoke tests in the `Notation*`
files (which deliberately stay minimal so the test sections double as
regressions for one elaborator at a time).

The running example is a tiny two-phase protocol over an `IPFunctor` indexed
by a custom `Phase` type:

```
Phase.opn      ─ init ──▶ Phase.counting ─ tick ──▶ Phase.counting
                                          ╰─ tick ──▶ Phase.counting
                                          ╰─ ⋯
```

* `Phase.opn` is the initial state; only `init` is available.
* After `init`, the protocol enters `Phase.counting`, where `tick` is
  available indefinitely and returns a `Nat`.

We compile the same three-step run three ways:

1. `IPFunctor.FreeM₂` — pre/post-state tracked statically in the type.
2. `IPFunctor.FreeM` with a `DeterministicTransitions proto` instance —
   single-index `IPFunctor.FreeM`, post-states recovered from the
   deterministic-class.
3. The result mapped down to a plain `PFunctor.FreeM` via the Σ-bundled
   `IPFunctor.FreeM.toSigmaFreeM`, since the index type `Phase` is not a
   `Unique` (so the `[Unique I]`-gated `IPFunctor.FreeM.erase` does not
   apply).

A final small example exercises `PFunctor.FreeM.equivW_of_isEmpty` to show
that an empty leaf type collapses `PFunctor.FreeM` structurally to the
W-type.
-/

@[expose] public section

set_option backward.do.legacy false

namespace IPFunctor.Examples

/-! ## Two-phase protocol fixture -/

/-- The two phases of the running protocol. Once we leave `opn`, we never
return: every transition from either state goes to `counting`. The
constructor is named `opn` rather than `open` to avoid clashing with Lean's
`open` keyword in pattern positions. -/
inductive Phase where
  /-- The initial state, before any `init` step. -/
  | opn
  /-- The post-`init` state, where `tick` is available indefinitely. -/
  | counting
deriving DecidableEq, Inhabited

/-- The protocol as an `IPFunctor.Endo`. At `Phase.opn` the only shape is the
trivial unit (read as "`init`"), which transitions to `counting`; at
`Phase.counting` the only shape is the trivial unit (read as "`tick`"),
which returns a `Nat` and stays at `counting`. -/
@[expose] def proto : IPFunctor.Endo Phase where
  A
    | .opn      => Unit
    | .counting => Unit
  B
    | .opn, _      => Unit
    | .counting, _ => Nat
  src
    | .opn, _, _      => .counting
    | .counting, _, _ => .counting

/-- Transitions are independent of the response, so `proto` has
deterministic transitions. The class instance lets the
[`Notation/Deterministic.lean`](Notation/Deterministic.lean) `do`-elaborator
specialize `liftA`-style steps to a concrete post-state. -/
@[expose] instance : IPFunctor.DeterministicTransitions proto where
  next
    | .opn, _      => .counting
    | .counting, _ => .counting
  spec s _ _ := by cases s <;> rfl

/-! ## Flavor 1: `IPFunctor.FreeM₂` with statically-tracked post-states

The two-index variant tracks pre- and post-state in the type, so chains
compose without restriction and the `IndexedMonad` instance from
[`Free/Indexed.lean`](Free/Indexed.lean) drives `do`-notation through
[`Notation/Indexed.lean`](Notation/Indexed.lean). -/

namespace TwoIndex

/-- `init` as a `FreeM₂` step: pre-state `opn`, post-state `counting`. -/
@[expose] def init : IPFunctor.FreeM₂ proto .opn .counting Unit :=
  IPFunctor.FreeM₂.roll () (fun _ => IPFunctor.FreeM₂.pure ())

/-- `tick` as a `FreeM₂` step: stays at `counting`, returns a `Nat`. -/
@[expose] def tick : IPFunctor.FreeM₂ proto .counting .counting Nat :=
  IPFunctor.FreeM₂.roll () (fun n => IPFunctor.FreeM₂.pure n)

/-- A three-step protocol run: one `init` then two `tick`s, summing the
responses. The intermediate post-state after `init` is `counting`, which
becomes the pre-state of the first `tick`; both `tick`s land at
`counting`, matching the do-block's overall post-state. -/
@[expose] def run : IPFunctor.FreeM₂ proto .opn .counting Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)

/-- The run unfolds to a transparent nested `roll` tree, exercising the
`FreeM₂.bind` simp lemmas. -/
example :
    run = IPFunctor.FreeM₂.roll () (fun _ =>
      IPFunctor.FreeM₂.roll () (fun a : Nat =>
        IPFunctor.FreeM₂.roll () (fun b : Nat =>
          IPFunctor.FreeM₂.pure (a + b)))) := rfl

end TwoIndex

/-! ## Flavor 2: single-index `IPFunctor.FreeM` under `DeterministicTransitions`

When transitions are deterministic, a single-index `IPFunctor.FreeM` chain
can still compose arbitrarily because each `IPFunctor.FreeM.liftA s a`
lands at the unique post-state `det.next s a`. The
[`Notation/Deterministic.lean`](Notation/Deterministic.lean) elaborator
detects the `IPFunctor.FreeM.liftA`-shape and uses the specialized
`IPFunctor.FreeM.bindLiftA` to thread that concrete post-state, lifting the
universal-quantification restriction that bites generic single-index
`do`-blocks. -/

namespace Deterministic

/-- `init` as a `FreeM` `liftA`-style step. Marked `@[reducible]` so the
deterministic elaborator can see through it to the underlying `liftA`.
`liftA`'s state argument is explicit, so we use the fully-qualified
`Phase.opn` rather than the dotted form, which has no type to infer
from at that position. -/
@[reducible, expose] def init : IPFunctor.FreeM proto Phase.opn Unit :=
  IPFunctor.FreeM.liftA Phase.opn ()

/-- `tick` as a `FreeM` `liftA`-style step. -/
@[reducible, expose] def tick : IPFunctor.FreeM proto Phase.counting Nat :=
  IPFunctor.FreeM.liftA Phase.counting ()

/-- The same three-step protocol run, this time as a single-index `FreeM`.
With `DeterministicTransitions proto` in scope, each step's post-state is
known to the elaborator, so the chain composes without the universal-
quantification restriction. -/
@[expose] def run : IPFunctor.FreeM proto .opn Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)

/-- The deterministic elaborator emits a nested `roll` chain whose post-states
are pinned by the `DeterministicTransitions` instance; the `(det.spec _).symm ▸`
transports inside `bindLiftA` collapse by `rfl` because `proto`'s `spec` proof
is itself `rfl` after `cases s`. Mirrors the parallel `TwoIndex.run` check
above. -/
example :
    run = IPFunctor.FreeM.roll Phase.opn () (fun _ : Unit =>
      IPFunctor.FreeM.roll Phase.counting () (fun a : Nat =>
        IPFunctor.FreeM.roll Phase.counting () (fun b : Nat =>
          IPFunctor.FreeM.pure Phase.counting (a + b)))) := rfl

end Deterministic

/-! ## Flavor 3: erasing into a plain `PFunctor.FreeM` via `IPFunctor.FreeM.toSigmaFreeM`

`IPFunctor.FreeM.erase` requires `[Unique I]`, which `Phase` is not. The
Σ-bundled forgetful map `IPFunctor.FreeM.toSigmaFreeM` (in
[`Free/Basic.lean`](Free/Basic.lean)) works for any index type by recording
the originating state inside each position; the result sits over
`proto.sigmaPFunctor` rather than `proto.toPFunctor`. We test the
collapsing simp lemmas (`toSigmaFreeM_pure`, `toSigmaFreeM_roll`) by
checking that the `TwoIndex.run` tree, viewed as an `IPFunctor.FreeM`,
agrees definitionally with the expected nested `PFunctor.FreeM.roll`. -/

example :
    IPFunctor.FreeM.toSigmaFreeM proto TwoIndex.run.toFreeM
    = PFunctor.FreeM.roll
        (P := proto.sigmaPFunctor) ⟨.opn, ()⟩ (fun _ =>
      PFunctor.FreeM.roll ⟨.counting, ()⟩ (fun a : Nat =>
        PFunctor.FreeM.roll ⟨.counting, ()⟩ (fun b : Nat =>
          PFunctor.FreeM.pure (a + b)))) := by
  rfl

/-! ## `PFunctor.FreeM.equivW_of_isEmpty` round-trip

When the value type `α` is empty, every `pure` leaf is unreachable and
`PFunctor.FreeM P α` collapses structurally to `P.W`. The forward direction
`toW` reinterprets each `roll` as a W-node; the inverse `ofW` rebuilds
the tree. Both directions are mutual inverses by induction; this example
just confirms the equivalence resolves and either round-trip is
`rfl` after unfolding. -/

example (P : PFunctor) (w : P.W) :
    (PFunctor.FreeM.equivW_of_isEmpty (P := P) (α := PEmpty)).invFun w =
      PFunctor.FreeM.ofW w := rfl

end IPFunctor.Examples
