# `do`-notation for `IPFunctor.FreeM` / `IPFunctor.FreeM₂`

Three parallel files in
[`PolyFun/IPFunctor/Notation/`](../../PolyFun/IPFunctor/Notation/) plug
custom `@[doElem_elab]` overrides into Lean 4.29's extensible
do-elaborator so that ordinary `do { let x ← e; … }` blocks elaborate
to the right `bind`-trees over `IPFunctor.FreeM` and `IPFunctor.FreeM₂`.

This page is a worked walkthrough; the canonical definitions live in
the linked Lean files. The full running example below is also compiled
inside the library at
[`PolyFun/IPFunctor/Examples.lean`](../../PolyFun/IPFunctor/Examples.lean),
which serves as the live-Lean companion to this prose.

## Activation

All three flavors require `set_option backward.do.legacy false` (or a
project-wide entry in `[leanOptions]` of `lakefile.toml`). This switches
Lean from the legacy do-elaborator to the new extensible one, which is
where our overrides plug in. The flag is transitional; when upstream
Lean retires it the lines come out.

## The three flavors at a glance

| File | Monad | When to reach for it |
|---|---|---|
| [`Notation.lean`](../../PolyFun/IPFunctor/Notation.lean) | `IPFunctor.FreeM P s α` | Tail of the block is state-polymorphic. Custom error messages call out state-mismatches and non-polymorphic remainders. |
| [`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean) | `IPFunctor.FreeM₂ P s t α` | Statically-tracked pre/post-states; chains of any length compose. |
| [`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) | `IPFunctor.FreeM P s α` + `[DeterministicTransitions P]` | Stay on single-index `IPFunctor.FreeM` and lift the universal-quantification constraint when `P.st s a b` is independent of `b`. |
| [`Notation/Mixed.lean`](../../PolyFun/IPFunctor/Notation/Mixed.lean) | (tests) | Sanity tests confirming the three overrides cohabit correctly. |

## Worked example: a tiny two-phase protocol

Pick a state machine with two phases:

```
Phase = opn | counting
```

At `opn`, an `init` action transitions us to `counting`. At `counting`,
a `tick` action returns a `Nat` and stays at `counting`. There is no
data-dependent branching — both transitions are deterministic. (We
spell the first constructor `opn` rather than `open` so it cannot be
confused with the Lean `open` keyword; this matches the live example
in [`Examples.lean`](../../PolyFun/IPFunctor/Examples.lean).)

```lean
inductive Phase | opn | counting
deriving DecidableEq

def proto : IPFunctor Phase where
  A
    | Phase.opn     => Unit       -- only `init` available
    | Phase.counting => Unit       -- only `tick` available
  B
    | Phase.opn,     _ => Unit
    | Phase.counting, _ => Nat
  st
    | Phase.opn,     _, _ => Phase.counting
    | Phase.counting, _, _ => Phase.counting
```

### Flavor 1: `IPFunctor.FreeM₂` — full chain support

Statically-tracked indices, no metavariable gymnastics. Best when you
want the type to record the start and end phases.

```lean
import PolyFun.IPFunctor.Notation.Indexed
set_option backward.do.legacy false

def init : IPFunctor.FreeM₂ proto Phase.opn Phase.counting Unit :=
  IPFunctor.FreeM₂.roll () (fun _ => IPFunctor.FreeM₂.pure ())

def tick : IPFunctor.FreeM₂ proto Phase.counting Phase.counting Nat :=
  IPFunctor.FreeM₂.roll () (fun n => IPFunctor.FreeM₂.pure n)

example : IPFunctor.FreeM₂ proto Phase.opn Phase.counting Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)
```

The chain `.opn → .counting → .counting → .counting` is threaded
through the type at every step.

### Flavor 2: `IPFunctor.FreeM` + `DeterministicTransitions` — same chain, single index

Same protocol, but stay on single-index `IPFunctor.FreeM`. We add a class
instance certifying that transitions are deterministic, then the
elaborator specializes each `IPFunctor.FreeM.liftA`-style step to its
known post-state.

```lean
import PolyFun.IPFunctor.Notation.Deterministic
set_option backward.do.legacy false

instance : IPFunctor.DeterministicTransitions proto where
  next
    | Phase.opn,     _ => Phase.counting
    | Phase.counting, _ => Phase.counting
  spec s a b := by cases s <;> rfl

@[reducible] def init : IPFunctor.FreeM proto Phase.opn Unit :=
  IPFunctor.FreeM.liftA Phase.opn ()

@[reducible] def tick : IPFunctor.FreeM proto Phase.counting Nat :=
  IPFunctor.FreeM.liftA Phase.counting ()

example : IPFunctor.FreeM proto Phase.opn Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)
```

(`Notation.Deterministic` transitively imports `Notation` to guarantee
its specialization fires before the basic single-index handler — see
the comment at the top of [`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean).)

This compiles for the same reason the `IPFunctor.FreeM₂` version does —
the post-state of each step is uniquely determined by the
`DeterministicTransitions` instance, and the elaborator builds
`IPFunctor.FreeM.bindLiftA` calls that thread the concrete next state
through the continuation.

### Flavor 3: basic `Notation.lean` — what you *can* do without DT or `IPFunctor.FreeM₂`

The basic single-index notation only handles `do`-block *tails* that
are polymorphic in the fresh post-state. In practice that means tails
made of `pure` / `return` / control flow over pure arms — anything
state-specific gets the *state mismatch* diagnostic.

```lean
import PolyFun.IPFunctor.Notation
set_option backward.do.legacy false

example : IPFunctor.FreeM proto Phase.opn Unit := do
  let _ ← init
  pure ()              -- polymorphic tail, OK

example : IPFunctor.FreeM proto Phase.opn Nat := do
  let _ ← init
  let a ← tick         -- ERROR: tick is at Phase.counting; the bind continuation
  pure a               -- must be state-polymorphic.
```

The second example fails with the custom diagnostic explaining that
`tick`'s pre-state `Phase.counting` doesn't unify with the fresh `s'` that
`IPFunctor.FreeM.bind`'s continuation quantifies over.

## `IPFunctor.FreeM.erase` interop (`Unique I` case)

When the state type is `Unique`, `IPFunctor.FreeM.erase` collapses
`do`-block trees to plain `PFunctor.FreeM`. Both the `@[simp]` lemmas
`erase_punit_pure` / `erase_punit_roll` (in
[`Free/Basic.lean`](../../PolyFun/IPFunctor/Free/Basic.lean)) and the
`toFreeM_*` lemmas fire on do-block-elaborated trees by `rfl`. The
existing test files include positive examples confirming this; see the
"`IPFunctor.FreeM.erase` interop" sections in
[`Notation.lean`](../../PolyFun/IPFunctor/Notation.lean),
[`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean),
and
[`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean).

## Choosing between flavors

A short decision tree:

* Need every leaf of every step at the same state? →
  `IPFunctor.FreeM₂` notation.
* Stuck on single-index `IPFunctor.FreeM` (e.g. for compatibility with
  existing APIs), and `P.st s a b` is independent of `b`? →
  `Notation/Deterministic.lean`, after adding a
  `DeterministicTransitions P` instance.
* Only need `do { pure … }` / `do { let _ ← op; pure … }` shapes? →
  basic `Notation.lean` suffices.

The forgetful map `IPFunctor.FreeM₂.toFreeM` lets you author in the
indexed variant and convert when downstream code expects single-index
`IPFunctor.FreeM`.
