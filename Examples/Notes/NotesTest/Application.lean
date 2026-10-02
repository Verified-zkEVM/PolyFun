/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Notes.App
import Notes.Preview
import Plausible
meta import Notes.App
meta import Notes.Preview

/-! # The real Notes machine with deterministic input and persistence faults -/

open Notes PFunctor.DynSystem

public section

private structure Memory where
  actions : List Action := []
  writes : List (List Command) := []
  messages : List String := []
  failWrite : Bool := false
  failAfterWrite : Bool := false
  failAt : Option Nat := none
  console : PolyFunIO.ConsoleMemory := {}

private def handler : PFunctor.Handler (StateM Memory) Effects
  | .inl .read => do
    let m ← get
    match m.actions with
    | [] => return .ok .quit
    | a :: rest => set { m with actions := rest }; return .ok a
  | .inl (.tell message) => do
    modify fun m ↦ { m with messages := m.messages ++ [message] }
    return .ok ()
  | .inl (.preview notes) => do
    let memory ← get
    let (answer, console) := ((Preview.form notes).interpret
      PolyFunIO.consoleMemoryHandler).run memory.console
    set { memory with console }
    return .ok answer
  | .inr journal => do
    let m ← get
    let fail := m.failWrite || m.failAt == some (m.writes.length + 1)
    if !fail || m.failAfterWrite then
      set { m with writes := m.writes ++ [journal.commands] }
    return if fail then .error "injected" else .ok ()

private def initial : State := .ready ⟨Journal.empty, {}⟩

def tests : IO Unit := do
  let actions := [Action.command (.create "  raw α  "),
    .command (.edit 0 0 "replacement\nsecond line"), .command (.edit 0 0 "stale"),
    .command (.edit 9 0 "unknown"), .back, .command (.create "history write"),
    .forward, .live, .quit]
  let (.done (session, code), memory) := (application.runChunk handler 100 initial).run { actions }
    | throw (IO.userError "application did not finish")
  unless code == 0 && memory.writes.length == 2 && session.journal.commands.length == 2 do
    throw (IO.userError "rejection or history wrote a command")
  unless session.journal.notes == [⟨"replacement\nsecond line", ["  raw α  "]⟩] do
    throw (IO.userError "text or old versions were lost")
  unless memory.messages.any (·.startsWith "Stale edit") &&
      memory.messages.contains "No note has ID 9." do
    throw (IO.userError "domain errors were not reported")
  for afterWrite in [false, true] do
    let (.done (s, code), m) := (application.runChunk handler 20 initial).run {
      actions := [.command (.create "unacknowledged")], failWrite := true,
      failAfterWrite := afterWrite }
      | throw (IO.userError "failed persistence did not stop")
    unless code == 1 && s.journal.commands.isEmpty &&
        m.writes.length == (if afterWrite then 1 else 0) do
      throw (IO.userError "failed write acknowledged a candidate")
  -- Every cut, including read/save/notice boundaries, resumes without duplicating a write.
  for cut in List.range 8 do
    let (first, m) := (application.runChunk handler cut initial).run { actions }
    let (second, m) := ((application.resumeChunk 100 first).liftM handler).run m
    let .done (s, code) := second | throw (IO.userError "resumed chunk did not finish")
    unless code == 0 && m.writes.length == 2 && s.journal.notes == session.journal.notes do
      throw (IO.userError "chunk split changed execution")
  let .ok journal := Journal.empty.accept (.create "original")
    | throw (IO.userError "preview setup failed")
  for input in [[], ["0"], ["0", "0"], ["0", "0", "replacement"],
      ["0", "0", "replacement", "cancel"], ["0", "0", "replacement", "invalid"],
      ["0", "9", "stale"], ["invalid"]] do
    let (.done (s, code), memory) := (application.startChunk handler 30 ⟨journal, {}⟩).run {
      actions := [.preview, .quit], console := { input } }
      | throw (IO.userError "preview did not finish")
    unless code == 0 && memory.writes.isEmpty && s.journal.commands == journal.commands do
      throw (IO.userError "unsaved preview reached persistence")
  let (.done (saved, _), memory) := (application.startChunk handler 30 ⟨journal, {}⟩).run {
    actions := [.preview, .quit], console := { input := ["0", "0", "replacement", "save"] } }
    | throw (IO.userError "confirmed preview did not finish")
  unless memory.writes.length == 1 && saved.journal.notes == [⟨"replacement", ["original"]⟩] do
    throw (IO.userError "confirmed preview did not use the ordinary edit protocol")
  let form := commandForm "edit"
  let (result, m) := (form.interpret PolyFunIO.consoleMemoryHandler).run {
    input := ["0", "1", "  exact  "] }
  match result with
  | .ok (.command (.edit 0 1 "  exact  ")) => pure ()
  | _ => throw (IO.userError "typed form changed text")
  unless m.input.isEmpty && m.output.size == 3 do throw (IO.userError "wrong prompt count")
  let (result, _) := (form.interpret PolyFunIO.consoleMemoryHandler).run { input := ["0"] }
  match result with
  | .error .endOfInput => pure ()
  | _ => throw (IO.userError "partial form submitted a command")
  IO.println "Notes application: ok"

/-- info: Notes application: ok -/
#guard_msgs in
#eval tests

/-! The reference uses newest-first text stacks, not `step`, `replay`, or `Journal.accept`.
Plausible supplies bounded, seeded data only: it is not used to discharge a proof. -/

private def reference (versionsById : List (List String)) : Command → Option (List (List String))
  | .create text => some (versionsById ++ [[text]])
  | .edit id expected text => do
    let versions ← versionsById[id]?
    if versions.length != expected + 1 then none else some (versionsById.set id (text :: versions))

private def generated (code : Nat) : Command :=
  if code % 3 == 0 then .create s!" raw α {code} "
  else .edit ((code / 3) % 4) ((code / 13) % 4) s!"edit\n{code}"

private def sequenceOK (codes : List Nat) : Bool := Id.run do
  let commands := (codes.take 12).map generated
  let mut expected := []
  let mut accepted := 0
  let mut journal := Journal.empty
  for command in commands do
    match reference expected command, journal.accept command with
    | none, .error _ => pure ()
    | some next, .ok candidate =>
      expected := next
      journal := candidate
      accepted := accepted + 1
      if candidate.notes.map (·.versions.reverse) != expected then return false
    | _, _ => return false
  let actions := commands.map Action.command ++ [.quit]
  for cut in List.range (3 * commands.length + 3) do
    let (first, memory) := (application.startChunk handler cut ⟨Journal.empty, {}⟩).run { actions }
    let (last, memory) := (application.continueChunk handler 100 first).run memory
    let .done (result, code) := last | return false
    if code != 0 || result.journal.notes.map (·.versions.reverse) != expected ||
        memory.writes.length != accepted then return false
  for index in List.range accepted do
    for afterWrite in [false, true] do
      let (last, memory) := (application.startChunk handler 100 ⟨Journal.empty, {}⟩).run {
        actions, failAt := some (index + 1), failAfterWrite := afterWrite }
      let .done (result, code) := last | return false
      if code != 1 || result.journal.commands.length != index ||
          memory.writes.length != index + (if afterWrite then 1 else 0) then return false
  return true

/-- Fixed seeds, bounded sequences, all cuts, and failures before/after each write. -/
def generatedTests : IO Unit := do
  for seed in [20261001, 17, 8191] do
    match ← Plausible.Testable.checkIO
        (Plausible.NamedBinder "codes" (∀ codes : List Nat, sequenceOK codes = true)) {
        randomSeed := some seed, numInst := 32, maxSize := 12 } with
    | .success _ => pure ()
    | .gaveUp _ => throw (IO.userError s!"seed {seed}: generation gave up")
    | .failure _ values _ => throw (IO.userError s!"seed {seed}: {values}")
  IO.println "Seeded command sequences, cuts, and acknowledgement faults: ok"

/-- info: Seeded command sequences, cuts, and acknowledgement faults: ok -/
#guard_msgs in
#eval generatedTests
