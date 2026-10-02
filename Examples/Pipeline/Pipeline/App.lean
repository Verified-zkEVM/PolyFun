/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Pipeline.Network

/-! # Read-only execution against the local filesystem

The outer IO handler converts read failures to explicit report entries. Chunking uses the
same residual-returning network runner as memory tests. No file is created or modified.
A paused invocation does not serialize a continuation; rerunning a command starts a new run.
-/

public section

namespace Pipeline

open PFunctor Interaction.Execution.ReactiveNetwork

/-- Filesystem failures remain outcomes of individual reads, not fabricated byte arrays. -/
def readIO : Handler IO Files := fun path ↦ do
  try return .ok (← IO.FS.readBinFile (System.FilePath.mk path))
  catch error => return .error error.toString

/-- Print a complete report, or explicitly report an unfinished invocation.
Exit 1 means file or protocol errors; exit 2 means the activation budget was insufficient. -/
def report (paths : List String) (fuel : Nat) (splitAt : Option Nat) : IO UInt32 := do
  let chunks := match splitAt with
    | none => [fuel]
    | some first => [min first fuel, fuel - min first fuel]
  let state ← runChunks readIO paths chunks
  match outcome (collectorId readIO paths) state with
  | some (.returned entries) =>
    for entry in entries do IO.println entry.render
    return if entries.any (fun entry ↦ !entry.result.isOk) then 1 else 0
  | some .aborted =>
    (← IO.getStderr).putStrLn "Internal protocol error: a service answered on an unexpected port."
    return 1
  | none =>
    (← IO.getStderr).putStrLn s!"Paused after {state.elapsed} activations; report incomplete. \
      No input files were changed. A new invocation starts over."
    return 2

end Pipeline
