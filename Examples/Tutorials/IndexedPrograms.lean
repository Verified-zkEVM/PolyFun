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
# Indexed programs for a two-phase protocol

The initial request enters the counting phase. Further requests return natural numbers
without leaving that phase. The same program uses either explicit start/end indices or
response-independent transitions; erasing its indices retains the state-tagged requests.

See the [indexed-program tutorial](../../docs/tutorials/indexed-programs.md).
-/

@[expose] public section

namespace PolyFunExamples.IndexedPrograms

/-! ## Two-phase protocol -/

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
def proto : IPFunctor.Endo Phase where
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
[`Notation/Deterministic.lean`](../../PolyFun/IPFunctor/Notation/Deterministic.lean) `do`-elaborator
specialize `lift`-style steps to a concrete post-state. -/
instance : IPFunctor.DeterministicTransitions proto where
  next
    | .opn, _      => .counting
    | .counting, _ => .counting
  spec s _ _ := by cases s <;> rfl

/-! ## Explicit start and end indices

The two-index variant tracks pre- and post-state in the type, so chains
compose without restriction and the `IndexedMonad` instance from
[`Free/Indexed.lean`](../../PolyFun/IPFunctor/Free/Indexed.lean) drives `do`-notation through
[`Notation/Indexed.lean`](../../PolyFun/IPFunctor/Notation/Indexed.lean). -/

namespace TwoIndex

/-- `init` as a `FreeM₂` step: pre-state `opn`, post-state `counting`. -/
def init : IPFunctor.FreeM₂ proto .opn .counting Unit :=
  IPFunctor.FreeM₂.liftBind () (fun _ => IPFunctor.FreeM₂.pure ())

/-- `tick` as a `FreeM₂` step: stays at `counting`, returns a `Nat`. -/
def tick : IPFunctor.FreeM₂ proto .counting .counting Nat :=
  IPFunctor.FreeM₂.liftBind () (fun n => IPFunctor.FreeM₂.pure n)

/-- A three-step protocol run: one `init` then two `tick`s, summing the
responses. The intermediate post-state after `init` is `counting`, which
becomes the pre-state of the first `tick`; both `tick`s land at
`counting`, matching the do-block's overall post-state. -/
def run : IPFunctor.FreeM₂ proto .opn .counting Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)

/-- Sequencing preserves the initial request and the two dependent counting steps. -/
example :
    run = IPFunctor.FreeM₂.liftBind () (fun _ =>
      IPFunctor.FreeM₂.liftBind () (fun a : Nat =>
        IPFunctor.FreeM₂.liftBind () (fun b : Nat =>
          IPFunctor.FreeM₂.pure (a + b)))) := rfl

end TwoIndex

/-! ## Response-independent transitions

When the next phase does not depend on the response, single-index `IPFunctor.FreeM`
can also sequence these operations. The deterministic notation threads the known post-state
through each `lift` step; this assumption does not hold for every indexed protocol. -/

namespace Deterministic

/-- The initial step exposes its underlying `lift` to the deterministic notation. -/
@[reducible] def init : IPFunctor.FreeM proto Phase.opn Unit :=
  IPFunctor.FreeM.lift Phase.opn ()

/-- `tick` as a `FreeM` `lift`-style step. -/
@[reducible] def tick : IPFunctor.FreeM proto Phase.counting Nat :=
  IPFunctor.FreeM.lift Phase.counting ()

/-- The same three-step protocol run, this time as a single-index `FreeM`.
With `DeterministicTransitions proto` in scope, each step's post-state is
known to the elaborator, so the chain composes without the universal-
quantification restriction. -/
def run : IPFunctor.FreeM proto .opn Nat := do
  let _ ← init
  let a ← tick
  let b ← tick
  pure (a + b)

/-- The single-index program has the same three requests as the two-index program. -/
example :
    run = IPFunctor.FreeM.liftBind Phase.opn () (fun _ : Unit =>
      IPFunctor.FreeM.liftBind Phase.counting () (fun a : Nat =>
        IPFunctor.FreeM.liftBind Phase.counting () (fun b : Nat =>
          IPFunctor.FreeM.pure Phase.counting (a + b)))) := rfl

end Deterministic

/-! ## Forgetting indices while retaining request tags

`IPFunctor.FreeM.toSigmaFreeM` produces an ordinary polynomial free program by recording
the originating phase in each request. The result uses `proto.sigmaPFunctor`: forgetting
the index does not discard the phase tags needed to interpret the requests. -/

example :
    IPFunctor.FreeM.toSigmaFreeM proto TwoIndex.run.toFreeM
    = PFunctor.FreeM.liftBind
        (P := proto.sigmaPFunctor) ⟨.opn, ()⟩ (fun _ =>
      PFunctor.FreeM.liftBind ⟨.counting, ()⟩ (fun a : Nat =>
        PFunctor.FreeM.liftBind ⟨.counting, ()⟩ (fun b : Nat =>
          PFunctor.FreeM.pure (a + b)))) := rfl

end PolyFunExamples.IndexedPrograms
