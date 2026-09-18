/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Storage

/-! # Command-line workflows for new meetings, recovery, reconstruction, and verification -/

@[expose] public section

namespace Parliament.App

open System

/-- Versioned configuration template printed by the executable's `example-config` command. -/
def exampleConfiguration : Configuration := {
  rules := { quorum := 3 },
  members := [⟨0, true, true⟩, ⟨1, true, true⟩, ⟨2, true, true⟩, ⟨3, true, true⟩],
  chair := 0,
  calendar := { today := ⟨2026, 1, 15⟩, nextRegular := ⟨2026, 2, 15⟩ },
  committees := [7],
  metadata := { organization := "Example Assembly", title := "Regular meeting" } }

/-- Supported invocation forms; directories are explicit and existing meetings are never reset. -/
def usage : String :=
  "parliament new --config FILE --dir DIR\n" ++
  "parliament resume DIR\n" ++
  "parliament replay JOURNAL --out DIR\n" ++
  "parliament verify JOURNAL EXPORT_DIR\n" ++
  "parliament example-config\n"

/-- Execute the selected workflow; all interactive procedure is delegated to the application
machine. -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["example-config"] => Terminal.print (encodeJson exampleConfiguration); return 0
  | ["--help"] | ["help"] | [] => Terminal.print usage; return 0
  | ["new", "--config", configPath, "--dir", directory] =>
    let config : Configuration ← match decodeJson (← IO.FS.readFile configPath) with
      | .ok value => pure value
      | .error error => throw (IO.userError ("configuration parse failed: " ++ error))
    let journal ← match config.start with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let directory := (directory : FilePath).normalize
    if ← directory.pathExists then
      throw (IO.userError "meeting directory already exists; use resume")
    let directory : FilePath :=
      (directory.toString.dropEndWhile (fun c => FilePath.pathSeparators.contains c)).toString
    if let some parent := directory.parent then IO.FS.createDirAll parent
    -- Exclusive creation also prevents racing `new` processes from resetting one another.
    IO.FS.createDir directory
    withWriter directory do
      persistJournal directory (snapshot config journal)
      runTerminal config directory journal
  | ["resume", directory] =>
    let directory : FilePath := directory
    withWriter directory do
      let wire ← readJournal (directory / "journal.json")
      let journal ← restoreJournal wire
      runTerminal wire.config directory journal
  | ["replay", journalPath, "--out", directory] =>
    let wire ← readJournal journalPath
    let journal ← restoreJournal wire
    let directory : FilePath := directory
    IO.FS.createDirAll directory
    withWriter directory do
      publishArtifacts directory journal (artifacts wire.config.metadata journal)
      Terminal.print s!"Replayed {wire.commands.length} commands; \
        exported revision {journal.state.revision}.\n"
      pure 0
  | ["verify", journalPath, directory] =>
    let wire ← readJournal journalPath
    let journal ← restoreJournal wire
    checkExport directory (artifacts wire.config.metadata journal)
    Terminal.print s!"Verified draft revision {journal.state.revision}.\n"
    pure 0
  | _ => Terminal.print usage; return 2

/-- Convert backend failures to a visible diagnostic and nonzero process status. -/
def main (args : List String) : IO UInt32 := do
  try cli args
  catch error =>
    (← IO.getStderr).putStrLn ("parliament: " ++ error.toString)
    return 1

end Parliament.App
