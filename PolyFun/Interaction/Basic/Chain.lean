/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.StateChain

/-!
# Finite final-sequence approximants (`Spec.Chain`)

A `Chain n` presents the `n`-th finite approximant obtained by iterating the
undecorated step polynomial on the terminal object:

```
Chain n ≃ (Spec.stepPoly.Obj)^[n] PUnit.
```

Concretely, each successor level carries the current `Spec` and a
transcript-indexed continuation to the next level. Thus `Chain` is a
sigma-friendly presentation of the finite final sequence of `Spec.stepPoly`;
it is not a separate protocol language.

Converting to a `Spec` via `Chain.toSpec` iterates the multiplication of
`Spec.substMonoid` (definitionally `PFunctor.FreeM.append`). State-machine
constructions are finite coalgebra unfolds: `Chain.ofStateChain` handles a
stage-indexed state family, and `Chain.ofStateMachine` is its homogeneous
specialization.

## Main definitions

* `Spec.Chain` — finite final-sequence approximant of `Spec.stepPoly`.
* `Spec.Chain.toSpec` — flatten via the substitution-monoid structure.
* `Chain.replicate` — constant rounds (recovers `Spec.replicate`).
* `Chain.ofStateChain` — finite unfold of a stage-indexed coalgebra.
* `Chain.ofStateMachine` — homogeneous-state specialization.

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Spec.replicate` | No | No | Uniform rounds (same spec, independent) |
| `Spec.stateChain` | Yes (`Stage i`) | Yes | State machine with explicit state type |
| `Spec.Chain` | No (baked in) | Yes | Continuation-style, no external state |

These are three views of the same polynomial iteration. `Chain` is the
state-erased finite approximant, `stateChain` is its clocked coalgebra unfold
already flattened to a `Spec`, and `replicate` is the constant-coalgebra case.

## Toy examples

The `GrowingMessages` section builds a protocol whose message type grows
at each step (`Fin 1`, `Fin 2`, …) without mentioning any state type.
-/

universe u

namespace Interaction
namespace Spec

/-- The `n`-th finite final-sequence approximant of `Spec.stepPoly`, starting
from the terminal object `PUnit`.

At a successor level this reduces definitionally to a current `Spec` paired
with one remaining chain for each of its transcripts. `succEquiv` identifies
that presentation with `Spec.stepPoly.Obj (Chain n)`. -/
def Chain : Nat → Type (u + 1)
  | 0 => PUnit
  | n + 1 => (spec : Spec) × (Transcript spec → Chain n)

namespace Chain

/-- Canonical equivalence between the sigma-friendly successor presentation
and the extension of `Spec.stepPoly` applied to the preceding approximant. -/
def succEquiv (n : Nat) :
    Chain (Nat.succ n) ≃ Spec.stepPoly.Obj (Chain n) where
  toFun c := ⟨c.1, c.2⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

/-- Flatten a finite approximant into a concrete `Spec` by iterating the
multiplication of `Spec.substMonoid`. This multiplication is definitionally
dependent `PFunctor.FreeM.append`. -/
def toSpec : (n : Nat) → Chain n → Spec
  | 0, _ => .done
  | n + 1, ⟨spec, cont⟩ =>
      Spec.substMonoid.mult.toFunA ⟨spec, fun tr => toSpec n (cont tr)⟩

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

/-- Finite unfold of a stage-indexed `Spec.stepPoly` coalgebra into the final
sequence. The stage state is erased from the resulting `Chain`. -/
def ofStateChain (Stage : Nat → Type u)
    (step : (i : Nat) → Stage i → Spec)
    (next : (i : Nat) → (s : Stage i) → Transcript (step i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → Chain n
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      ⟨step i s, fun tr => ofStateChain Stage step next n (i + 1) (next i s tr)⟩

/-- Homogeneous-state specialization of `ofStateChain`. This is the finite
unfold of a coalgebra `σ → Spec.stepPoly.Obj σ`. -/
def ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) (n : Nat) (s : σ) : Chain n :=
  ofStateChain (fun _ => σ) (fun _ => step) (fun _ => next) n 0 s

/-! ## Bridge to existing API -/

/-- Converting a `replicate` chain recovers `Spec.replicate`. -/
theorem toSpec_replicate (spec : Spec) :
    (n : Nat) → toSpec n (Chain.replicate spec n) = spec.replicate n
  | 0 => rfl
  | n + 1 => by
      simp only [Chain.replicate, toSpec, Spec.substMonoid_mult_toFunA,
        PFunctor.FreeM.replicate]
      congr 1; funext _; exact toSpec_replicate spec n

/-- Flattening the finite unfold of a stage-indexed coalgebra recovers the
existing `Spec.stateChain` construction. -/
theorem toSpec_ofStateChain (Stage : Nat → Type u)
    (step : (i : Nat) → Stage i → Spec)
    (next : (i : Nat) → (s : Stage i) → Transcript (step i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    toSpec n (Chain.ofStateChain Stage step next n i s) =
      PFunctor.FreeM.stateChain PUnit.unit Stage step next n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Chain.ofStateChain, toSpec, Spec.substMonoid_mult_toFunA,
        PFunctor.FreeM.stateChain]
      congr 1
      funext tr
      exact toSpec_ofStateChain Stage step next n (i + 1) (next i s tr)

/-- For a homogeneous coalgebra, the clock carried by `ofStateChain` is
observationally irrelevant already at the unflattened `Chain` level. -/
theorem ofStateChain_const_index {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) :
    (n i j : Nat) → (s : σ) →
    Chain.ofStateChain (fun _ => σ) (fun _ => step) (fun _ => next) n i s =
      Chain.ofStateChain (fun _ => σ) (fun _ => step) (fun _ => next) n j s
  | 0, _, _, _ => rfl
  | n + 1, i, j, s => by
      simp only [Chain.ofStateChain]
      congr 1
      funext tr
      exact ofStateChain_const_index step next n (i + 1) (j + 1) (next s tr)

/-- Converting a state-machine chain recovers `Spec.stateChain` with
constant stage family and round index erased. -/
theorem toSpec_ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) :
    (n : Nat) → (i : Nat) → (s : σ) →
    toSpec n (Chain.ofStateMachine step next n s) =
      PFunctor.FreeM.stateChain PUnit.unit (fun _ => σ) (fun _ => step) (fun _ => next) n i s
  | n, i, s => by
      rw [ofStateMachine,
        ofStateChain_const_index step next n 0 i s]
      exact toSpec_ofStateChain (fun _ => σ) (fun _ => step) (fun _ => next) n i s

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
