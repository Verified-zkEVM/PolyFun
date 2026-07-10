/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Chain

/-!
# Worked examples for continuation-style chains (`Spec.Chain`)

Toy protocols that exercise the `Spec.Chain` API from
[`PolyFun.Interaction.Basic.Chain`](../../../PolyFun/Interaction/Basic/Chain.lean)
and double as regression tests: a chain whose per-round message type grows with
the round index, a chain with genuine transcript-prefix dependence, and
dependent strategy composition (`replay`) over the prefix-dependent example.
-/

universe u

namespace Interaction

namespace Spec

/-! ## Toy example: growing message types -/

section GrowingMessages

/-- A protocol where round `k` exchanges a value from `Fin (k + 1)`.
No state type — the dependency is baked directly into the chain. -/
private def growingChain : (n : Nat) → (k : Nat) → Chain.{0} n
  | 0, _ => ⟨⟩
  | n + 1, k => ⟨.node (Fin (k + 1)) fun _ => .done,
                  fun _ => growingChain n (k + 1)⟩

/-- Two rounds from position `0`: `Fin 1` then `Fin 2`. -/
example : Chain.toSpec 2 (growingChain 2 0) =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ => .done := rfl

/-- Three rounds: `Fin 1`, `Fin 2`, `Fin 3`. -/
example : Chain.toSpec 3 (growingChain 3 0) =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ =>
      .node (Fin 3) fun _ => .done := rfl

/-- The transcript type reflects the growing message sizes. -/
example : Transcript (Chain.toSpec 2 (growingChain 2 0)) =
    ((_ : Fin 1) × (_ : Fin 2) × PUnit) := rfl

/-- A fully literal 3-round protocol — no parameters, no recursion,
no state. Just data. -/
private def threeRoundsLiteral : Chain.{0} 3 :=
  ⟨.node (Fin 1) fun _ => .done, fun _ =>
    ⟨.node (Fin 2) fun _ => .done, fun _ =>
      ⟨.node (Fin 3) fun _ => .done, fun _ => ⟨⟩⟩⟩⟩

example : Chain.toSpec 3 threeRoundsLiteral =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ =>
      .node (Fin 3) fun _ => .done := rfl

end GrowingMessages

/-! ## Toy example: genuine transcript-prefix dependence -/

section PrefixDependent

/-- First round branches and exposes branch-specific data to later rounds. -/
private def branchingRound : Spec :=
  .node Bool fun b =>
    if b then
      .node Nat fun _ => .done
    else
      .node (Fin 2) fun _ => .done

/-- The second round depends on the full first-round transcript. -/
private def secondRound : Transcript branchingRound → Spec
  | ⟨true, ⟨(n : Nat), ⟨⟩⟩⟩ => .node (Fin (n + 1)) fun _ => .done
  | ⟨false, ⟨i, ⟨⟩⟩⟩ => .node (Fin (i.val + 2)) fun _ => .done

/-- The third round depends on the full two-round transcript prefix. -/
private def thirdRound :
    (tr₁ : Transcript branchingRound) → Transcript (secondRound tr₁) → Spec
  | ⟨true, ⟨(n : Nat), ⟨⟩⟩⟩, ⟨k, ⟨⟩⟩ => .node (Fin (n + k.val + 1)) fun _ => .done
  | ⟨false, ⟨i, ⟨⟩⟩⟩, ⟨k, ⟨⟩⟩ => .node (Fin (i.val + k.val + 2)) fun _ => .done

/-- A three-round chain whose final move type genuinely depends on the prefix transcript. -/
private def prefixDependent : Chain.{0} 3 :=
  ⟨branchingRound, fun tr₁ =>
    ⟨secondRound tr₁, fun tr₂ =>
      ⟨thirdRound tr₁ tr₂, fun _ => ⟨⟩⟩⟩⟩

/-- Flattening the chain is just iterated `PFunctor.FreeM.append` over transcript-indexed tails. -/
example : Chain.toSpec 3 prefixDependent =
    branchingRound.append (fun tr₁ =>
      (secondRound tr₁).append (fun tr₂ =>
        (thirdRound tr₁ tr₂).append (fun _ => Spec.done))) := rfl

/-- After a `true` prefix, the remainder remembers the earlier `Nat` choice. -/
example (n : Nat) :
    Chain.toSpec 2 (prefixDependent.2 ⟨true, ⟨n, ⟨⟩⟩⟩) =
      .node (Fin (n + 1)) fun k =>
        .node (Fin (n + k.val + 1)) fun _ => .done := rfl

/-- After a `false` prefix, the remainder remembers the earlier `Fin 2` choice. -/
example (i : Fin 2) :
    Chain.toSpec 2 (prefixDependent.2 ⟨false, ⟨i, ⟨⟩⟩⟩) =
      .node (Fin (i.val + 2)) fun k =>
        .node (Fin (i.val + k.val + 2)) fun _ => .done := rfl

/-- The transcript type itself is dependent: the third move type varies with the second. -/
example (n : Nat) :
    Transcript (Chain.toSpec 2 (prefixDependent.2 ⟨true, ⟨n, ⟨⟩⟩⟩)) =
      ((k : Fin (n + 1)) × ((_ : Fin (n + k.val + 1)) × PUnit)) := rfl

/-- The other branch has a different dependent transcript shape. -/
example (i : Fin 2) :
    Transcript (Chain.toSpec 2 (prefixDependent.2 ⟨false, ⟨i, ⟨⟩⟩⟩)) =
      ((k : Fin (i.val + 2)) × ((_ : Fin (i.val + k.val + 2)) × PUnit)) := rfl

/-! ## Dependent strategy composition over the prefix-dependent example -/

/-- Pure strategy that follows a prescribed transcript and returns a chosen leaf output. -/
private def scriptStrategy :
    (spec : Spec) → (tr : Transcript spec) → {Output : Transcript spec → Type u} →
    Output tr → Strategy.Plain Id spec Output
  | .done, _, _, out => out
  | .node _ rest, ⟨x, trRest⟩, _, out => ⟨x, scriptStrategy (rest x) trRest out⟩

/-- Carry the flattened transcript of the remaining chain as the dependent state. -/
private abbrev ReplayState {n : Nat} (c : Chain.{0} n) : Type :=
  Transcript (Chain.toSpec n c)

/-- One dependent step: split the remaining flattened transcript into this round and the tail,
play the current round verbatim, and return the tail transcript. -/
private def replayStep {n : Nat} (c : Chain.{0} (n + 1))
    (tr : ReplayState c) :
    Id (Strategy.Plain Id c.1 (fun tr₁ => ReplayState (c.2 tr₁))) :=
  let ⟨tr₁, trRest⟩ := Chain.splitTranscript n c tr
  scriptStrategy c.1 tr₁ trRest

/-- Replay a full flattened transcript using the intrinsic dependent strategy combinator. -/
private def replayStrategy (n : Nat) (c : Chain.{0} n) (tr : ReplayState c) :
    Strategy.Plain Id (Chain.toSpec n c)
      (Chain.outputFamily (Family := fun {_} c => ReplayState c) n c) :=
  Chain.strategyComp (Family := fun {_} c => ReplayState c) replayStep n c tr

/-- A concrete `true`-branch transcript for the prefix-dependent chain. -/
private def trueReplayTranscript (n : Nat) (k : Fin (n + 1)) (j : Fin (n + k.val + 1)) :
    Transcript (Chain.toSpec 3 prefixDependent) := by
  let tr₁ : Transcript branchingRound := ⟨true, ⟨n, ⟨⟩⟩⟩
  let c₂ := prefixDependent.2 tr₁
  let tr₂ : Transcript c₂.1 := ⟨k, ⟨⟩⟩
  let c₃ := c₂.2 tr₂
  let tr₃ : Transcript c₃.1 := ⟨j, ⟨⟩⟩
  exact Chain.appendTranscript 2 prefixDependent tr₁
    (Chain.appendTranscript 1 c₂ tr₂
      (Chain.appendTranscript 0 c₃ tr₃ ⟨⟩))

/-- A concrete `false`-branch transcript for the prefix-dependent chain. -/
private def falseReplayTranscript (i : Fin 2) (k : Fin (i.val + 2))
    (j : Fin (i.val + k.val + 2)) :
    Transcript (Chain.toSpec 3 prefixDependent) := by
  let tr₁ : Transcript branchingRound := ⟨false, ⟨i, ⟨⟩⟩⟩
  let c₂ := prefixDependent.2 tr₁
  let tr₂ : Transcript c₂.1 := ⟨k, ⟨⟩⟩
  let c₃ := c₂.2 tr₂
  let tr₃ : Transcript c₃.1 := ⟨j, ⟨⟩⟩
  exact Chain.appendTranscript 2 prefixDependent tr₁
    (Chain.appendTranscript 1 c₂ tr₂
      (Chain.appendTranscript 0 c₃ tr₃ ⟨⟩))

/-- Replaying a concrete `true`-branch transcript reproduces that exact transcript. -/
example :
    (Strategy.run (spec := Chain.toSpec 3 prefixDependent)
      (replayStrategy 3 prefixDependent (trueReplayTranscript 1 0 0))).1 =
        trueReplayTranscript 1 0 0 := rfl

/-- Replaying a concrete `false`-branch transcript reproduces that exact transcript. -/
example :
    (Strategy.run (spec := Chain.toSpec 3 prefixDependent)
      (replayStrategy 3 prefixDependent (falseReplayTranscript 1 0 0))).1 =
        falseReplayTranscript 1 0 0 := rfl

end PrefixDependent

end Spec
end Interaction
