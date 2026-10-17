/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.App
public import Notes.Walkthrough
import PolyFunIO.Storage
import PolyFun.PFunctor.Dynamical.DynComputation.IO

/-! # Console and filesystem interpretation for Notes

The notebook runner interprets the application machine using real streams and checked storage.
The representation demos use real streams with in-memory data and never open a notebook.
-/

public section

namespace Notes

open PolyFunIO

/-- Persist the command journal under a checked, single-name replacement. -/
def save (directory : System.FilePath) (journal : Journal) : IO Unit :=
  Storage.replaceChecked (directory / "journal.json") (Lean.toJson journal.wire |>.compress)

/-- Real console interpretation, with no access to a persistence directory. -/
def interactionHandler : PFunctor.Handler IO InteractionEffects
  | .read => Storage.attempt do
    match ← readForm.runIO with
    | .ok action => return action
    | .error .endOfInput => return .quit
    | .error error => return .invalid error.message
  | .tell text => Storage.attempt do (← IO.getStdout).putStrLn text
  | .preview notes => Storage.attempt (Preview.form notes).runIO

/-- Compose the interactive and storage capabilities at the application boundary. -/
def ioHandler (directory : System.FilePath) : PFunctor.Handler IO Effects :=
  PFunctor.Handler.sum interactionHandler (fun journal => Storage.attempt (save directory journal))

/-- Explicit local directories; new never resets existing notes. -/
def runNotebook (fresh : Bool) (directory : System.FilePath) : IO UInt32 := do
  if fresh then
    if ← directory.pathExists then throw (IO.userError "Directory already exists; use open.")
    if let some parent := directory.parent then IO.FS.createDirAll parent
    IO.FS.createDir directory
  Storage.withLock (directory / "notes.lock") do
    let journal ← if fresh then
        save directory Journal.empty
        pure Journal.empty
      else do
        let text ← IO.FS.readFile (directory / "journal.json")
        let wire : WireJournal ← match Lean.Json.parse text >>= Lean.fromJson? with
          | .error error => throw (IO.userError error)
          | .ok wire => pure wire
        match wire.restore with
        | .error error => throw (IO.userError error)
        | .ok journal => pure journal
    let (_, code) ← application.runIO (ioHandler directory) (.ready ⟨journal, {}⟩)
    return code

/-- IO failures remain visible and set the process status. -/
def main (fresh : Bool) (directory : System.FilePath) : IO UInt32 := do
  try runNotebook fresh directory
  catch error =>
    (← IO.getStderr).putStrLn ("notes: " ++ error.toString)
    return 1

namespace Walkthrough

/-- Real streams are just another handler of these same representation-specific programs. -/
def demo (model : String) : IO UInt32 := do
  let .ok model := Model.parse model
    | (← IO.getStderr).putStrLn "Choose free, indexed, system, machine, resumption, or tree."
      return 2
  let result ← run model (consoleIOHandler (← IO.getStdin) (← IO.getStdout))
  match result with
  | .error error => (← IO.getStderr).putStrLn error; return 2
  | .ok answer => (← IO.getStdout).putStrLn (answer.getD "EOF"); return 0

/-- A useful manual comparison: prepare and confirm an edit without writing any files. -/
def demoEdit (model : String) : IO UInt32 := do
  let .ok model := Model.parse model
    | (← IO.getStderr).putStrLn "Choose free, indexed, system, machine, resumption, or tree."
      return 2
  (← IO.getStdout).putStrLn "Demo note [0 v0]: First local note (in memory only)."
  match ← runEdit model (consoleIOHandler (← IO.getStdin) (← IO.getStdout)) with
  | .error error => (← IO.getStderr).putStrLn error; return 2
  | .ok (.error error) => (← IO.getStdout).putStrLn error.message; return 0
  | .ok (.ok none) => (← IO.getStdout).putStrLn "Cancelled; nothing saved."; return 0
  | .ok (.ok (some command)) =>
    (← IO.getStdout).putStrLn s!"Prepared {repr command}; demo does not persist."
    return 0

end Walkthrough

end Notes
