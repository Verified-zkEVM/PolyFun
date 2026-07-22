/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Chain.Append

/-!
# Dependent chain-concatenation regression tests

The three one-round stages below model a genuinely dependent three-stage
pipeline. The middle move type depends on the prefix path, and the final move
type depends on both the prefix and middle paths. The examples exercise raw
and flattened units, boundary path and output-family transport, strategy
composition, and typed three-stage reassociation.
-/

namespace Interaction
namespace TypeTree
namespace ChainAppendExamples

private def prefixTree : TypeTree :=
  .node Bool fun _ => .done

private def prefixChain : Chain 1 :=
  ⟨prefixTree, fun _ => ⟨⟩⟩

private def middleTree (path : Path (Chain.toTypeTree 1 prefixChain)) : TypeTree :=
  .node (Fin (bif path.1 then 2 else 3)) fun _ => .done

private def middle (path : Path (Chain.toTypeTree 1 prefixChain)) : Chain 1 :=
  ⟨middleTree path, fun _ => ⟨⟩⟩

private def finalArity
    (path : Path (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))) : Nat :=
  let pieces := Chain.splitThenPath prefixChain middle path
  (bif pieces.1.1 then 10 else 20) + pieces.2.1.val + 1

private def finalTree
    (path : Path (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))) : TypeTree :=
  .node (Fin (finalArity path)) fun _ => .done

private def final
    (path : Path (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))) : Chain 1 :=
  ⟨finalTree path, fun _ => ⟨⟩⟩

private def prefixPath : Path (Chain.toTypeTree 1 prefixChain) :=
  ⟨true, ⟨⟩⟩

private def middlePath : Path (Chain.toTypeTree 1 (middle prefixPath)) :=
  ⟨(1 : Fin 2), ⟨⟩⟩

private def combinedPath :
    Path (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle)) :=
  Chain.appendThenPath prefixChain middle prefixPath middlePath

private def otherPrefixPath : Path (Chain.toTypeTree 1 prefixChain) :=
  ⟨false, ⟨⟩⟩

private def otherMiddlePath : Path (Chain.toTypeTree 1 (middle otherPrefixPath)) :=
  ⟨(2 : Fin 3), ⟨⟩⟩

private def otherCombinedPath :
    Path (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle)) :=
  Chain.appendThenPath prefixChain middle otherPrefixPath otherMiddlePath

example : Chain.splitThenPath prefixChain middle combinedPath =
    ⟨prefixPath, middlePath⟩ := by
  simp [combinedPath]

example : Chain.splitThenPath prefixChain middle otherCombinedPath =
    ⟨otherPrefixPath, otherMiddlePath⟩ := by
  simp [otherCombinedPath]

example : finalArity combinedPath = 12 := rfl

example : finalArity otherCombinedPath = 23 := rfl

example : Chain.appendThenPath prefixChain middle
      (Chain.splitThenPath prefixChain middle combinedPath).1
      (Chain.splitThenPath prefixChain middle combinedPath).2 = combinedPath :=
  Chain.appendThenPath_splitThenPath prefixChain middle combinedPath

/-! ## Strategy composition across the chain boundary -/

private def boundaryFamily
    (path : Path (Chain.toTypeTree 1 prefixChain))
    (suffix : Path (Chain.toTypeTree 1 (middle path))) : Type :=
  Fin ((bif path.1 then 10 else 20) + suffix.1.val + 1)

private def prefixStrategy :
    Strategy.Plain Id (Chain.toTypeTree 1 prefixChain) (fun _ => PUnit) :=
  ⟨true, ⟨⟩⟩

private def suffixStrategy :
    (path : Path (Chain.toTypeTree 1 prefixChain)) → PUnit →
      Id (Strategy.Plain Id (Chain.toTypeTree 1 (middle path))
        (boundaryFamily path))
  | ⟨true, ⟨⟩⟩, _ => ⟨(1 : Fin 2), (0 : Fin 12)⟩
  | ⟨false, ⟨⟩⟩, _ => ⟨(2 : Fin 3), (0 : Fin 23)⟩

private def composedStrategy :
    Strategy.Plain Id
      (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))
      (Chain.liftThen prefixChain middle boundaryFamily) :=
  Chain.strategyCompThen prefixChain middle prefixStrategy suffixStrategy

/-- The chain-specific strategy combinator preserves the dependent prefix and
suffix choices in the path returned by execution. -/
example :
    (Strategy.run
      (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))
      composedStrategy).1 = combinedPath :=
  rfl

/-- The dependent output type computes through the joined boundary path. -/
example :
    (Strategy.run
      (Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle))
      composedStrategy).2 = (0 : Fin 12) :=
  rfl

example :
    Chain.liftThen prefixChain middle boundaryFamily combinedPath = Fin 12 := by
  rw [show combinedPath =
    Chain.appendThenPath prefixChain middle prefixPath middlePath from rfl]
  simp [boundaryFamily, prefixPath, middlePath]

example
    (Family : {rounds : Nat} → Chain rounds → Type) :
    Chain.outputFamily Family (1 + 1) (Chain.then prefixChain middle)
        combinedPath =
      Chain.outputFamily Family 1 (middle prefixPath) middlePath := by
  rw [Chain.outputFamily_then]
  change Chain.outputFamily Family 1
      (middle (Chain.splitThenPath prefixChain middle combinedPath).1)
      (Chain.splitThenPath prefixChain middle combinedPath).2 = _
  rw [show combinedPath =
    Chain.appendThenPath prefixChain middle prefixPath middlePath from rfl]
  rw [Chain.splitThenPath_appendThenPath]

example : Chain.toTypeTree (1 + 1) (Chain.then prefixChain middle) =
    (Chain.toTypeTree 1 prefixChain).append
      (fun path => Chain.toTypeTree 1 (middle path)) :=
  Chain.toTypeTree_then prefixChain middle

example : Chain.toTypeTree (0 + 1)
      (Chain.then (⟨⟩ : Chain 0) (fun _ => prefixChain)) =
    Chain.toTypeTree 1 prefixChain :=
  Chain.toTypeTree_then_zero_left (⟨⟩ : Chain 0) (fun _ => prefixChain)

example : Chain.castRounds (Nat.zero_add 1)
      (Chain.then (⟨⟩ : Chain 0) (fun _ => prefixChain)) = prefixChain :=
  Chain.then_zero_left (⟨⟩ : Chain 0) (fun _ => prefixChain)

example : Chain.toTypeTree (1 + 0)
      (Chain.then prefixChain (fun _ => (⟨⟩ : Chain 0))) =
    Chain.toTypeTree 1 prefixChain :=
  Chain.toTypeTree_then_zero_right prefixChain (fun _ => (⟨⟩ : Chain 0))

example : Chain.then (n := 0) prefixChain (fun _ => (⟨⟩ : Chain 0)) = prefixChain :=
  Chain.then_zero_right prefixChain (fun _ => (⟨⟩ : Chain 0))

example :
    Chain.toTypeTree (1 + (1 + 1))
        (Chain.reassoc (Chain.then (Chain.then prefixChain middle) final)) =
      Chain.toTypeTree (1 + (1 + 1))
        (Chain.then prefixChain (fun path =>
          Chain.then (middle path) (fun suffix =>
            final (Chain.appendThenPath prefixChain middle path suffix)))) :=
  Chain.toTypeTree_then_assoc prefixChain middle final

end ChainAppendExamples
end TypeTree
end Interaction
