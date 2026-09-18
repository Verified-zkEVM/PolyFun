/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Terminal
public import PolyFun.PFunctor.Dynamical.DynComputation.IO

/-! # IO interpretation, verified readback, and single-writer storage -/

@[expose] public section

namespace Parliament.App

open System

/-- Convert IO exceptions into the explicit response type of application effects. -/
def attempt {α : Type} (action : IO α) : IO (Except String α) := do
  try return .ok (← action)
  catch error => return .error error.toString

/-- Write, flush, and check the exact UTF-8 payload observed through the filesystem backend. -/
def writeChecked (path : FilePath) (payload : String) : IO Unit := do
  IO.FS.withFile path .write fun handle => do
    handle.write payload.toUTF8
    handle.flush
  let actual ← IO.FS.readBinFile path
  unless actual == payload.toUTF8 do
    throw (IO.userError s!"readback mismatch: {path}")

/-- Persist a complete journal by replacing its name only after staging and readback succeed. -/
def persistJournal (directory : FilePath) (wire : WireJournal) : IO Unit := do
  let staging := directory / "journal.json.pending"
  writeChecked staging (encodeJson wire)
  IO.FS.rename staging (directory / "journal.json")

/-- Read both immutable export files and compare their exact bytes with the certified payload. -/
def checkExport {rules : Rules} {metadata : Metadata} {journal : Journal wordDomain rules}
    (directory : FilePath) (payload : Artifacts metadata journal) : IO Unit := do
  let markdown ← IO.FS.readBinFile (directory / "minutes.md")
  let json ← IO.FS.readBinFile (directory / "minutes.json")
  unless markdown == payload.markdown.toUTF8 && json == payload.json.toUTF8 do
    throw (IO.userError "export payload mismatch")

/-- Publish matching JSON and Markdown together under an immutable revision directory. -/
def publishArtifacts {rules : Rules} {metadata : Metadata} (directory : FilePath)
    (journal : Journal wordDomain rules) (payload : Artifacts metadata journal) : IO Unit := do
  let exports := directory / "exports"
  IO.FS.createDirAll exports
  let destination := exports / s!"rev-{journal.state.revision}"
  if ← destination.pathExists then
    checkExport destination payload
    return
  let staging := exports / s!".pending-{journal.state.revision}"
  IO.FS.createDirAll staging
  writeChecked (staging / "minutes.md") payload.markdown
  writeChecked (staging / "minutes.json") payload.json
  checkExport staging payload
  IO.FS.rename staging destination
  checkExport destination payload

/-- Execute the polynomial operations through real Lean IO. -/
def ioHandler (config : Configuration) (directory : FilePath) :
    PFunctor.Handler IO (Effects config) := fun effect => match effect with
  | .read state => attempt (Terminal.readAction state)
  | .judge request => attempt (Terminal.judgment request)
  | .tell text => attempt (Terminal.print (text ++ "\n"))
  | .persist journal => attempt (persistJournal directory (snapshot config journal))
  | .publish journal payload => attempt (publishArtifacts directory journal payload)

/-- Hold a separate lock inode while the journal name is atomically replaced. -/
def withWriter {α : Type} (directory : FilePath) (action : IO α) : IO α :=
  IO.FS.withFile (directory / "meeting.lock") .append fun handle => do
    unless ← handle.tryLock do throw (IO.userError "another writer holds this meeting directory")
    try action finally handle.unlock

/-- Load and parse the versioned journal; its restore operation subsequently checks every
command. -/
def readJournal (path : FilePath) : IO WireJournal := do
  match decodeJson (← IO.FS.readFile path) with
  | .ok wire => return wire
  | .error error => throw (IO.userError ("journal parse failed: " ++ error))

/-- Reconstruct a typed journal or report the illegal command location. -/
def restoreJournal (wire : WireJournal) : IO (Journal wordDomain wire.config.rules) := do
  match wire.restore with
  | .ok journal => return journal
  | .error error => throw (IO.userError error)

/-- Run the real application through the reusable resumable IO driver. -/
def runTerminal (config : Configuration) (directory : FilePath)
    (journal : Journal wordDomain config.rules) : IO UInt32 := do
  let result ← (application config).runIO (ioHandler config directory) (.ready journal)
  return result.code

end Parliament.App
