/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.StateChain

/-!
# Continuation-style chains (`Spec.Chain`)

A `Chain n` is a self-contained recipe for an `n`-round protocol:
at each level it carries the current round's `Spec` and a transcript-indexed
continuation to the next level. There is **no external state type**, no
`Stage : Nat → Type`, and no round index family.

Converting to a `Spec` via `Chain.toSpec` uses only `PFunctor.FreeM.append`.
State-machine constructions are *derived*: `Chain.ofStateMachine`
builds a chain from `(σ, step, next, s₀)` and then forgets `σ`.

## Main definitions

* `Spec.Chain` — depth-indexed telescope: round spec + continuation.
* `Spec.Chain.toSpec` — convert a chain into a concrete `Spec`.
* `Chain.replicate` — constant rounds (recovers `Spec.replicate`).
* `Chain.ofStateMachine` — build from a state machine (recovers `Spec.stateChain`).

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Spec.replicate` | No | No | Uniform rounds (same spec, independent) |
| `Spec.stateChain` | Yes (`Stage i`) | Yes | State machine with explicit state type |
| `Spec.Chain` | No (baked in) | Yes | Continuation-style, no external state |

`Chain` is the most fundamental: it requires no external state type, yet
supports full transcript dependence. `stateChain` is a specialization
(recovered by `Chain.ofStateMachine`), and `replicate` is a further
specialization (recovered by `Chain.replicate`).

## Toy examples

The `GrowingMessages` section builds a protocol whose message type grows
at each step (`Fin 1`, `Fin 2`, …) without mentioning any state type.
-/

universe u

namespace Interaction
namespace Spec

/-- A self-contained recipe for an `n`-round protocol. At each level,
carries the current round's `Spec` and, for each possible transcript,
the recipe for the remaining rounds. No external state type. -/
def Chain : Nat → Type (u + 1)
  | 0 => PUnit
  | n + 1 => (spec : Spec) × (Transcript spec → Chain n)

namespace Chain

/-- Convert a chain into a concrete `Spec` via iterated `append`. -/
def toSpec : (n : Nat) → Chain n → Spec
  | 0, _ => .done
  | n + 1, ⟨spec, cont⟩ => spec.append (fun tr => toSpec n (cont tr))

@[simp, grind =]
theorem toSpec_zero (c : Chain 0) : toSpec 0 c = Spec.done := rfl

theorem toSpec_succ {n : Nat} (spec : Spec)
    (cont : Transcript spec → Chain n) :
    toSpec (n + 1) ⟨spec, cont⟩ =
      spec.append (fun tr => toSpec n (cont tr)) := rfl

/-! ## Constructors -/

/-- Constant rounds: same spec every round, continuation ignores the
transcript. -/
def replicate (spec : Spec) : (n : Nat) → Chain n
  | 0 => ⟨⟩
  | n + 1 => ⟨spec, fun _ => replicate spec n⟩

/-- Build a chain from a state machine — exactly a coalgebra `(step, next)` of
the undecorated step polynomial `Spec.stepPoly` (a `PFunctor.DynSystem σ
Spec.stepPoly` unpacked on its states). The state `σ` is consumed
during construction and does not appear in the resulting `Chain`. -/
def ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) : (n : Nat) → σ → Chain n
  | 0, _ => ⟨⟩
  | n + 1, s => ⟨step s, fun tr => ofStateMachine step next n (next s tr)⟩

/-! ## Bridge to existing API -/

/-- Converting a `replicate` chain recovers `Spec.replicate`. -/
theorem toSpec_replicate (spec : Spec) :
    (n : Nat) → toSpec n (Chain.replicate spec n) = spec.replicate n
  | 0 => rfl
  | n + 1 => by
      simp only [Chain.replicate, toSpec, PFunctor.FreeM.replicate]
      congr 1; funext _; exact toSpec_replicate spec n

/-- Converting a state-machine chain recovers `Spec.stateChain` with
constant stage family and round index erased. -/
theorem toSpec_ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) :
    (n : Nat) → (i : Nat) → (s : σ) →
    toSpec n (Chain.ofStateMachine step next n s) =
      PFunctor.FreeM.stateChain PUnit.unit (fun _ => σ) (fun _ => step) (fun _ => next) n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Chain.ofStateMachine, toSpec, PFunctor.FreeM.stateChain]
      congr 1; funext tr
      exact toSpec_ofStateMachine step next n (i + 1) (next s tr)

/-! ## Transcript operations -/

/-- Split a transcript of an `(n+1)`-round chain into the first round's
transcript and the remainder. -/
def splitTranscript (n : Nat) (c : Chain (n + 1)) :
    Transcript (toSpec (n + 1) c) →
    (tr₁ : Transcript c.1) × Transcript (toSpec n (c.2 tr₁)) :=
  PFunctor.FreeM.Path.split c.1 (fun tr => toSpec n (c.2 tr))

/-- Combine a first-round transcript with a remainder. -/
def appendTranscript (n : Nat) (c : Chain (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2 tr₁))) :
    Transcript (toSpec (n + 1) c) :=
  PFunctor.FreeM.Path.append c.1 (fun tr => toSpec n (c.2 tr)) tr₁ tr₂

@[simp, grind =]
theorem splitTranscript_appendTranscript (n : Nat) (c : Chain (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2 tr₁))) :
    splitTranscript n c (appendTranscript n c tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  PFunctor.FreeM.Path.split_append _ _ _ _

/-! ## Strategy composition -/

/-- Output family for strategy composition along a chain. This is the intrinsic analog of
`Transcript.stateChainFamily`: a family on the remaining chain is lifted to a family on
transcripts of the flattened `Spec`. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type u) :
    (n : Nat) → (c : Chain n) → Transcript (toSpec n c) → Type u
  | 0, c, _ => Family c
  | n + 1, ⟨spec, cont⟩, tr =>
      PFunctor.FreeM.Path.liftAppend spec (fun tr₁ => toSpec n (cont tr₁))
        (fun tr₁ tr₂ => outputFamily Family n (cont tr₁) tr₂)
        tr

/-- Compose strategies along a chain with a transcript-dependent output family. The step
function sees the current round spec packaged as the remaining chain, and returns the next
family member indexed by the transcript of that round. -/
def strategyComp {m : Type u → Type u} [Monad m]
    {Family : {n : Nat} → Chain n → Type u}
    (step : {n : Nat} → (c : Chain (n + 1)) → Family c →
      m (Strategy.Plain m c.1 (fun tr => Family (c.2 tr)))) :
    (n : Nat) → (c : Chain n) → Family c →
    m (Strategy.Plain m (toSpec n c) (outputFamily Family n c))
  | 0, _, a => pure a
  | n + 1, ⟨spec, cont⟩, a => do
      let strat ← step ⟨spec, cont⟩ a
      Strategy.comp spec (fun tr => toSpec n (cont tr))
        strat (fun tr mid => strategyComp step n (cont tr) mid)

end Chain

end Spec
end Interaction
