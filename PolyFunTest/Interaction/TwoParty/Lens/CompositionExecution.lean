/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Iterate
public import PolyFun.Interaction.TwoParty.Lens.Swap

/-!
# Composition and ordered effects

The identity lens retains every challenge branch. The three composition seams use a state
monad to record boundary slots, terminal actions, and effectful suffix construction.
-/

@[expose] public section

namespace Interaction.TwoParty.Lens.CompositionExecutionTest
open PFunctor
open FreeM (Path PathAlong projectPathAlong)

abbrev L := PFunctor.Lens.id rolePoly.{0}
abbrev Trace := StateM (List String)
abbrev done : FreeM rolePoly.{0} PUnit.{1} := .pure ⟨⟩
abbrev receive : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.receiver, Bool) (fun _ => done)
abbrev send : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.sender, Bool) (fun _ => done)

/-- Record an effect in execution order. -/
def note (event : String) : Trace Unit := modify (· ++ [event])

abbrev pLeaf : Trace Nat := do note "prefix leaf"; pure 7
abbrev suffixP (memory : Nat) : Focal L Trace receive (fun _ => Nat) := do
  note "suffix focal slot"
  pure (fun b => do note "suffix focal leaf"; pure (memory + if (show Bool from b) then 1 else 0))
abbrev suffixC : Counterpart L Trace receive (fun _ => Nat) := do
  note "suffix challenge"
  pure ⟨true, do note "suffix counterpart leaf"; pure 9⟩

abbrev buildSuffix (_ : PathAlong L done) (memory : Nat) :
    Trace (Focal L Trace receive (fun _ => Nat)) := do
  note "build suffix"
  pure (suffixP memory)

abbrev emptyComposed := run (l := L) (done.append (fun _ => receive))
  (Focal.compFlat (l := L) (m := Trace) (s₁ := done)
    (Mid := fun _ => Nat) (Out := fun _ => Nat) pLeaf buildSuffix)
  (Counterpart.appendFlat (l := L) (m := Trace) (s₁ := done)
    (s₂ := fun _ => receive) (Mid := fun _ => Unit) (Out := fun _ => Nat) ()
    (fun _ _ => suffixC))
abbrev emptySequential := do
  let ⟨tr, memory, _⟩ ← run (l := L) (m := Trace) done (OutP := fun _ => Nat)
    (OutC := fun _ => Unit) pLeaf (pure ())
  let next ← buildSuffix tr memory
  let ⟨tail, op, oc⟩ ← run receive next suffixC
  pure (⟨PathAlong.append L done (fun _ => receive) tr tail, op, oc⟩ :
    (_tr : PathAlong L (done.append (fun _ => receive))) × Nat × Nat)

example : emptyComposed = emptySequential :=
  run_compFlat_appendFlat (l := L) (m := Trace) (s₁ := done)
    (s₂ := fun _ => receive) (OutP := fun _ => Nat) (OutC := fun _ => Nat)
    (MidP := fun _ => Nat) (MidC := fun _ => Unit) pLeaf buildSuffix () (fun _ _ => suffixC)

example : (emptyComposed.run []).2 =
    ["prefix leaf", "build suffix", "suffix focal slot", "suffix challenge",
      "suffix focal leaf", "suffix counterpart leaf"] := by
  simp only [emptyComposed, run_compFlat_appendFlat, done, FreeM.pure_eq_pure, run_done,
    PureEnd.toStrategy,
    PureEnd.mapOutput, run_node]
  rfl

abbrev sendP : Focal L Trace send (fun _ => Nat) := do
  note "send focal slot"; pure ⟨true, pLeaf⟩
abbrev sendC : PureEnd L Trace .counterpart send (fun _ => Unit) := do
  note "send counterpart slot"; pure (fun _ => ())
abbrev receiveP : Focal L Trace receive (fun _ => Nat) := do
  note "receive focal slot"; pure (fun _ => pLeaf)
abbrev receiveC : PureEnd L Trace .counterpart receive (fun _ => Unit) := do
  note "receive counterpart slot"; pure ⟨false, ()⟩

abbrev composed (s : FreeM rolePoly.{0} PUnit.{1})
    (p : Focal L Trace s (fun _ => Nat))
    (c : PureEnd L Trace .counterpart s (fun _ => Unit)) :=
  run (l := L) (s.append (fun _ => receive))
    (Focal.compFlat (Out := fun _ => Nat) p (fun _ memory => do
      note "build suffix"; pure (suffixP memory)))
    (Counterpart.appendFlat (Out := fun _ => Nat) c (fun _ _ => suffixC))

abbrev sequential (s : FreeM rolePoly.{0} PUnit.{1})
    (p : Focal L Trace s (fun _ => Nat))
    (c : PureEnd L Trace .counterpart s (fun _ => Unit)) := do
  let ⟨tr, memory, _⟩ ← run s p c.toStrategy
  note "build suffix"
  let ⟨tail, op, oc⟩ ← run receive (suffixP memory) suffixC
  pure (⟨PathAlong.append L s (fun _ => receive) tr tail, op, oc⟩ :
    (_tr : PathAlong L (s.append (fun _ => receive))) × Nat × Nat)

example : composed send sendP sendC = sequential send sendP sendC := by
  simpa only [composed, sequential, bind_assoc, pure_bind] using
    (run_compFlat_appendFlat (s₂ := fun _ => receive)
      (OutP := fun _ => Nat) (OutC := fun _ => Nat) sendP
      (fun _ memory => do note "build suffix"; pure (suffixP memory)) sendC
      (fun _ _ => suffixC))

example : composed receive receiveP receiveC = sequential receive receiveP receiveC := by
  simpa only [composed, sequential, bind_assoc, pure_bind] using
    (run_compFlat_appendFlat (s₂ := fun _ => receive)
      (OutP := fun _ => Nat) (OutC := fun _ => Nat) receiveP
      (fun _ memory => do note "build suffix"; pure (suffixP memory)) receiveC
      (fun _ _ => suffixC))

example : (composed send sendP sendC).run [] =
    (⟨⟨true, true, ⟨⟩⟩, 8, 9⟩,
      ["send focal slot", "send counterpart slot", "prefix leaf", "build suffix",
       "suffix focal slot", "suffix challenge", "suffix focal leaf",
       "suffix counterpart leaf"]) := by
  simp only [composed, run_compFlat_appendFlat, run_node, done, FreeM.pure_eq_pure, run_done]
  rfl

example : (composed receive receiveP receiveC).run [] =
    (⟨⟨false, true, ⟨⟩⟩, 8, 9⟩,
      ["receive focal slot", "receive counterpart slot", "prefix leaf", "build suffix",
       "suffix focal slot", "suffix challenge", "suffix focal leaf",
       "suffix counterpart leaf"]) := by
  simp only [composed, run_compFlat_appendFlat, run_node, done, FreeM.pure_eq_pure, run_done]
  rfl

abbrev roundP (n : Nat) : Focal L Id receive (fun _ => Nat) := fun _ => n + 1
abbrev roundC (n : Nat) : PureEnd L Id .counterpart receive (fun _ => Nat) := ⟨true, n + 2⟩

example : run (FreeM.replicate PUnit.unit receive 0)
    (Focal.iterate receive roundP 0 10) (Counterpart.iterate receive roundC 0 20) =
    ⟨⟨⟩, 10, 20⟩ := run_iterate_zero receive roundP roundC 10 20

example : run (FreeM.replicate PUnit.unit receive 3)
    (Focal.iterate receive roundP 3 10) (Counterpart.iterate receive roundC 3 20) =
    ⟨⟨true, true, true, ⟨⟩⟩, 13, 26⟩ := by
  simp only [run_iterate_succ, run_iterate_zero, run_node, done, FreeM.pure_eq_pure, run_done]
  rfl

example : run (l := swapLens L) send (Strategy.swap sendC.toStrategy)
    (Strategy.swap sendP) = (do
      let ⟨tr, op, oc⟩ ← runWith .counterpartFirst send sendP sendC.toStrategy
      pure ⟨tr, oc, op⟩) := run_swap send sendP sendC.toStrategy

/-- The empty prefix also preserves both suffix outputs. -/
example : (emptyComposed.run []).1.2 = (8, 9) := by
  simp only [emptyComposed, run_compFlat_appendFlat, done, FreeM.pure_eq_pure, run_done,
    PureEnd.toStrategy,
    PureEnd.mapOutput, run_node]
  rfl

/-- Swapped execution exchanges outputs and executes the old counterpart slot first. -/
example : (run (l := swapLens L) send (Strategy.swap sendC.toStrategy)
    (Strategy.swap sendP)).run [] =
    (⟨⟨true, ⟨⟩⟩, (), 7⟩, ["send counterpart slot", "send focal slot", "prefix leaf"]) := by
  rw [run_swap]
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  rfl

/-- A fully branching receiver chooses whether the suffix includes a preamble. -/
abbrev messageTree : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.sender, Nat) (fun _ => receive)
abbrev suffixTree : Path receive → FreeM rolePoly.{0} PUnit.{1}
  | ⟨false, _⟩ => messageTree
  | ⟨true, _⟩ => .liftBind (.receiver, Unit) (fun _ => messageTree)

abbrev messageProver (memory : Nat) : Focal L Trace messageTree (fun _ => Nat) := do
  note "second message"
  pure ⟨memory, (pure (fun (challenge : Bool) => do
    note "after second challenge"
    pure (if challenge then memory + 1 else memory)) : Trace (Bool → Trace Nat))⟩

abbrev wholeProver : Focal L Trace (receive.append suffixTree) (fun _ => Nat) := by
  change Trace ((b : Bool) → Focal L Trace (suffixTree ⟨b, ⟨⟩⟩) (fun _ => Nat))
  exact pure (fun challenge => match challenge with
    | false => do note "after first challenge"; messageProver 7
    | true => do
      note "after first challenge"
      pure (fun (_ : Unit) => do note "after preamble"; messageProver 11))

abbrev firstVerifier (challenge : Bool) :
    PureEnd L Trace .counterpart receive (fun _ => Unit) := do
  note "first challenge"; pure ⟨challenge, ()⟩

abbrev messageVerifier : Counterpart L Trace messageTree (fun _ => Nat) := by
  change Trace (Nat → Trace ((b : Bool) × Trace Nat))
  exact pure (fun message => do
    note "message received"
    note "second challenge"
    pure ⟨true, pure message⟩)

abbrev suffixVerifier : (tr : PathAlong L receive) → Unit →
    Counterpart L Trace (suffixTree (projectPathAlong L receive tr)) (fun _ => Nat)
  | ⟨false, _⟩, _ => messageVerifier
  | ⟨true, _⟩, _ => do note "suffix preamble"; pure ⟨(), messageVerifier⟩

abbrev outputs (challenge : Bool) : Trace (Nat × Nat) := do
  let result ← run (receive.append suffixTree) wholeProver
    (Counterpart.appendFlat (Out := fun _ => Nat) (firstVerifier challenge) suffixVerifier)
  pure result.2

example : (outputs false).run [] = ((8, 7),
    ["first challenge", "after first challenge", "second message", "message received",
      "second challenge", "after second challenge"]) := by
  simp only [outputs, receive, FreeM.append_liftBind, run_node]
  change (let r := (run (l := L) (m := Trace) messageTree
    (OutP := fun _ => Nat) (OutC := fun _ => Nat)
    (do note "after first challenge"; messageProver 7) messageVerifier).run ["first challenge"]
    (r.1.2, r.2)) = _
  simp only [run_node, done, FreeM.pure_eq_pure, run_done]
  rfl

example : (outputs true).run [] = ((12, 11),
    ["first challenge", "after first challenge", "suffix preamble", "after preamble",
      "second message", "message received", "second challenge", "after second challenge"]) := by
  simp only [outputs, receive, FreeM.append_liftBind, run_node]
  change (let r := (run (l := L) (m := Trace) (.liftBind (.receiver, Unit) (fun _ => messageTree))
    (OutP := fun _ => Nat) (OutC := fun _ => Nat)
    (do note "after first challenge"
        pure (fun (_ : Unit) => do note "after preamble"; messageProver 11))
    (do note "suffix preamble"; pure ⟨(), messageVerifier⟩)).run ["first challenge"]
    (r.1.2, r.2)) = _
  simp only [run_node, done, FreeM.pure_eq_pure, run_done]
  rfl

/-- Prefix decomposition retains the whole strategy's private continuation. -/
example (challenge : Bool) :
    run (receive.append suffixTree) wholeProver
      (Counterpart.appendFlat (Out := fun _ => Nat) (firstVerifier challenge) suffixVerifier) =
    (do
      let ⟨tr, next, oc⟩ ← run receive (Focal.splitPrefix wholeProver)
        (firstVerifier challenge).toStrategy
      let ⟨tail, op, outC⟩ ← run (suffixTree (projectPathAlong L receive tr)) next
        (suffixVerifier tr oc)
      pure ⟨PathAlong.append L receive suffixTree tr tail, op, outC⟩) :=
  run_appendFlat_splitPrefix (OutC := fun _ => Nat) wholeProver
    (firstVerifier challenge) suffixVerifier

/-! ## Owners of the suffix chosen by the receiver's move -/

/-- Owners of the nodes visited by a transcript, in execution order. -/
def owners : (s : FreeM rolePoly.{0} PUnit.{1}) → PathAlong L s → List Role
  | .pure _, _ => []
  | .liftBind a rest, tr =>
    owner L a :: owners (rest (L.toFunB a (PathAlong.head L a rest tr)))
      (PathAlong.tail L a rest tr)

/-- Owners of the first node of a tree, if any. -/
def rootOwner : FreeM rolePoly.{0} PUnit.{1} → Option Role
  | .pure _ => none
  | .liftBind a _ => some (owner L a)

/-- Owners along an appended transcript are the prefix owners followed by the suffix owners. -/
theorem owners_append :
    (s₁ : FreeM rolePoly.{0} PUnit.{1}) → (s₂ : Path s₁ → FreeM rolePoly.{0} PUnit.{1}) →
    (tr : PathAlong L s₁) → (tail : PathAlong L (s₂ (projectPathAlong L s₁ tr))) →
    owners (s₁.append s₂) (PathAlong.append L s₁ s₂ tr tail) =
      owners s₁ tr ++ owners (s₂ (projectPathAlong L s₁ tr)) tail
  | .pure _, _, _, _ => rfl
  | .liftBind a rest, s₂, tr, tail => by
    simp only [FreeM.append_liftBind, owners, List.cons_append]
    exact congrArg _ (owners_append (rest (L.toFunB a (PathAlong.head L a rest tr)))
      (fun t => s₂ ⟨L.toFunB a (PathAlong.head L a rest tr), t⟩)
      (PathAlong.tail L a rest tr) tail)

/-- The two suffixes begin with a focal (sender) and a counterpart (receiver) move. -/
example : rootOwner (suffixTree ⟨false, ⟨⟩⟩) = some .sender := rfl
example : rootOwner (suffixTree ⟨true, ⟨⟩⟩) = some .receiver := rfl

/-- The receiver's challenge selects the suffix, and the suffixes have different root owners. -/
example : rootOwner (suffixTree ⟨false, ⟨⟩⟩) ≠ rootOwner (suffixTree ⟨true, ⟨⟩⟩) := by
  intro h; cases h

/-- Owner sequence of the transcript produced by the composite run, in the state monad. -/
def runOwners (challenge : Bool) : List Role :=
  (((fun r => owners (receive.append suffixTree) r.1) <$>
    run (receive.append suffixTree) wholeProver
      (Counterpart.appendFlat (Out := fun _ => Nat) (firstVerifier challenge)
        suffixVerifier) : Trace (List Role)).run []).1

/-- Running the composite equals running the prefix and then the suffix selected by the prefix
transcript, and the owners of the resulting transcript are the prefix owners followed by the
selected suffix owners. -/
theorem runOwners_eq (challenge : Bool) :
    runOwners challenge = ((do
      let ⟨tr, next, oc⟩ ← run receive (Focal.splitPrefix wholeProver)
        (firstVerifier challenge).toStrategy
      let ⟨tail, _, _⟩ ← run (suffixTree (projectPathAlong L receive tr)) next
        (suffixVerifier tr oc)
      pure (owners receive tr ++ owners (suffixTree (projectPathAlong L receive tr)) tail) :
        Trace (List Role)).run []).1 := by
  unfold runOwners
  rw [run_appendFlat_splitPrefix (OutC := fun _ => Nat) wholeProver
    (firstVerifier challenge) suffixVerifier]
  simp only [map_bind, owners_append, map_pure]

/-- The `false` suffix starts with the sender: receiver, sender, receiver. -/
theorem runOwners_false : runOwners false = [.receiver, .sender, .receiver] := by
  rw [runOwners_eq]
  simp only [receive, run_node]
  rfl

/-- The `true` suffix starts with a receiver preamble: receiver, receiver, sender, receiver. -/
theorem runOwners_true : runOwners true = [.receiver, .receiver, .sender, .receiver] := by
  rw [runOwners_eq]
  simp only [receive, run_node]
  rfl

/-- The owner sequence of the produced transcript depends on the receiver's move. -/
example : runOwners false ≠ runOwners true := by
  rw [runOwners_false, runOwners_true]
  intro h
  cases h

end Interaction.TwoParty.Lens.CompositionExecutionTest
