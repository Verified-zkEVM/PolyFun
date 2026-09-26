/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Examples.Parliament.Scenarios
public import PolyFunTest.Examples.Parliament.Edges
public import Examples.Parliament.App.Memory
meta import PolyFunTest.Examples.Parliament.Scenarios
meta import PolyFunTest.Examples.Parliament.Edges
meta import Examples.Parliament.App.Memory

/-! # The actual application machine under deterministic and failing IO backends -/

@[expose] public section

open Parliament Parliament.App
open PFunctor.DynSystem (DynComputation)

namespace ParliamentTest.Application

/-- Configuration matching the existing regression scenarios, with text that needs escaping. -/
def config : Configuration := {
  rules, members := roster, chair := 0, calendar, committees := [7],
  metadata := {
    organization := "Assembly α & β", title := "Budget *review*\n# not a heading",
    clerk := some "A. Clerk" } }

/-- Run a supplied backend script with enough interaction fuel for the scenario. -/
def execute (memory : Memory) (fuel : Nat := 4096) :
    Except String (DynComputation.Chunk (State config) (Exit config) × Memory) := do
  let journal ← config.start
  let computation :=
    DynComputation.runChunk (application config) (memoryHandler config) fuel (.ready journal)
  pure (computation.run memory)

/-- Compare actual state-machine execution, replay, minutes, persistence, and wire round trips. -/
def scenario (name : String) (program : Scenario Unit) : IO Unit := do
  let .ok (_, run) := program.run {} | throw (IO.userError s!"{name}: original scenario failed")
  let memory : Memory := { actions := run.commands.map Action.command }
  let .ok (.done result, final) := execute memory | throw (IO.userError s!"{name}: runtime paused")
  unless result.code == 0 && result.journal.state == run.state &&
      result.journal.history.events == run.events do
    throw (IO.userError s!"{name}: runtime differs from direct execution")
  unless final.persistCount == run.commands.length && final.publishCount == 1 do
    throw (IO.userError s!"{name}: duplicated or omitted effects")
  let wire := snapshot config result.journal
  let .ok decoded := decodeJson (α := WireJournal) (encodeJson wire)
    | throw (IO.userError s!"{name}: journal codec failed")
  unless decoded == wire do throw (IO.userError s!"{name}: codec lost command data")
  let .ok reconstructed := wire.restore | throw (IO.userError s!"{name}: replay rejected")
  unless reconstructed.history.entries == result.journal.history.entries do
    throw (IO.userError s!"{name}: incremental and reconstructed minutes differ")
  let expected := artifacts config.metadata result.journal
  let [output] := final.exports | throw (IO.userError s!"{name}: wrong publication count")
  unless output.markdown == expected.markdown && output.json == expected.json do
    throw (IO.userError s!"{name}: wrong publication payload")
/-- All existing accepted meeting journals are exercised through the real application protocol. -/
def allScenarios : IO Unit := do
  for (name, program) in [
    ("basic", basic), ("amendment", amendment), ("missing second", missingSecond),
    ("debate closure", debateClosure), ("consent objection", consentObjection),
    ("appeal", appeal), ("appeal tie", appealTie), ("interruption", interruption),
    ("stale judgment", staleJudgment), ("quorum loss", quorumLoss),
    ("table restore", tableRestore), ("committee report", committeeReport),
    ("postponement", postponement), ("withdrawal", withdrawal), ("chair vote", chairVote),
    ("session expiry", sessionExpiration), ("empty poll", Edges.emptyPoll),
    ("speech clock", Edges.speechClock), ("decision quorum", Edges.quorumAtDecision),
    ("scoped closure", Edges.scopedClosure), ("failed closure", Edges.failedClosure),
    ("appeal continuation", Edges.appealContinuation), ("unfinished", Edges.unfinishedBusiness),
    ("due precedence", Edges.duePrecedence), ("midnight recess", Edges.recessAcrossMidnight)] do
    scenario name program
  IO.println "allScenarios: ok"

/-- Failed writes never acknowledge the candidate, even when a backend may have stored it. -/
def failures : IO Unit := do
  let actions := [Action.command (.attendance 0 1 true), .command (.attendance 0 2 true)]
  for afterWrite in [false, true] do
    let .ok (.done result, memory) := execute {
      actions, failPersistAt := some 1, failAfterWrite := afterWrite }
      | throw (IO.userError "persistence fault did not stop")
    unless result.code == 1 && result.journal.state.revision == 0 &&
        memory.persistCount == 1 && memory.publishCount == 0 do
      throw (IO.userError "failed write advanced acknowledged state")
    if afterWrite then
      let some text := memory.journal | throw (IO.userError "missing ambiguous persisted payload")
      let .ok wire := decodeJson (α := WireJournal) text | throw (IO.userError "bad snapshot")
      let .ok restored := wire.restore | throw (IO.userError "ambiguous write not recoverable")
      unless restored.state.revision == 1 do throw (IO.userError "recovery lost stored command")
  for mismatch in [false, true] do
    let .ok (.done result, memory) := execute {
      actions, failPublish := !mismatch, mismatchReadback := mismatch }
      | throw (IO.userError "publication fault did not stop")
    unless result.code == 1 && result.journal.state.revision == 2 && memory.exports.isEmpty do
      throw (IO.userError "publication failure corrupted history or reported success")
  let .ok (.done result, memory) := execute {
    actions := [.invalid "malformed", .command (.unsupported "reconsider"), .quit] }
    | throw (IO.userError "rejection run did not stop")
  unless result.journal.state.revision == 0 && memory.persistCount == 0 do
    throw (IO.userError "rejected input persisted")
  IO.println "failures: ok"
/-- Chunk boundaries preserve every residual phase and do not repeat completed writes. -/
def chunks : IO Unit := do
  let .ok journal := config.start | throw (IO.userError "invalid config")
  let memory : Memory := { actions := [.command (.attendance 0 1 true), .quit] }
  let (first, intermediate) :=
    ((application config).runChunk (memoryHandler config) 2 (.ready journal)).run memory
  let .paused residual := first | throw (IO.userError "expected pending acknowledgement")
  unless intermediate.persistCount == 1 do throw (IO.userError "wrong first chunk")
  let (second, final) :=
    ((application config).runChunk (memoryHandler config) 10 residual).run intermediate
  let .done result := second | throw (IO.userError "second chunk did not finish")
  unless result.code == 0 && final.persistCount == 1 && final.publishCount == 1 do
    throw (IO.userError "resumption repeated an effect")
  IO.println "chunks: ok"
/-- Contextual recordability distinguishes a missing second, consent, and amended wording. -/
def minuteBoundaries : IO Unit := do
  let .ok (_, run) := missingSecond.run {} | throw (IO.userError "setup failed")
  let .ok journal := ({ config, commands := run.commands } : WireJournal).restore
    | throw (IO.userError "restore failed")
  unless journal.history.entries.any (fun e => match e.action with
      | .notSeconded _ => true | _ => false) do throw (IO.userError "missing second lost")
  unless !journal.history.entries.any (fun e => match e.action with
      | .decided _ _ (.counted _) => true | _ => false) do
    throw (IO.userError "missing second fabricated a counted vote")
  let .ok (_, amended) := amendment.run {} | throw (IO.userError "setup failed")
  let .ok changed := ({ config, commands := amended.commands } : WireJournal).restore
    | throw (IO.userError "restore failed")
  unless changed.history.entries.any (fun e => match e.action with
      | .decided q true _ => q.motion == .main ["fund", "the", "school"] && q.version == 1
      | _ => false) do throw (IO.userError "final wording was not recorded")
  let output := artifacts config.metadata changed
  match verifyArtifacts config.metadata changed (output.markdown ++ "tampered") output.json with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "tampered artifact accepted")
  unless escapeMarkdown "a\n# *b* & <c>" == "a\\n\\# \\*b\\* \\& \\<c\\>" do
    throw (IO.userError "Markdown escaping mismatch")
  IO.println "minuteBoundaries: ok"
/-- info: allScenarios: ok -/
#guard_msgs in
#eval allScenarios
/-- info: failures: ok -/
#guard_msgs in
#eval failures
/-- info: chunks: ok -/
#guard_msgs in
#eval chunks
/-- info: minuteBoundaries: ok -/
#guard_msgs in
#eval minuteBoundaries

end ParliamentTest.Application
