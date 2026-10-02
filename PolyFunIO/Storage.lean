/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Init.System.IO

/-!
# Small checked filesystem operations for local examples

These helpers use Lean's IO primitives. Readback checks observed bytes; it does not
prove power-loss durability. A caller acknowledges a transaction only after success
and recovers an ambiguous failure by reading the file actually present.
-/

public section

namespace PolyFunIO.Storage

open System

/-- Turn a backend exception into an explicit handler response. -/
def attempt {α : Type} (action : IO α) : IO (Except String α) := do
  try return .ok (← action)
  catch error => return .error error.toString

/-- Write, flush, and read back the exact UTF-8 payload. -/
def writeChecked (path : FilePath) (payload : String) : IO Unit := do
  IO.FS.withFile path .write fun handle ↦ do
    handle.write payload.toUTF8
    handle.flush
  unless (← IO.FS.readBinFile path) == payload.toUTF8 do
    throw (IO.userError s!"readback mismatch: {path}")

/-- Replace a file only after writing and checking a sibling staging file. -/
def replaceChecked (path : FilePath) (payload : String) : IO Unit := do
  let staging : FilePath := path.toString ++ ".pending"
  writeChecked staging payload
  IO.FS.rename staging path

/-- Hold a separate lock inode throughout an action that may replace the data file. -/
def withLock {α : Type} (path : FilePath) (action : IO α) : IO α :=
  IO.FS.withFile path .append fun handle ↦ do
    unless ← handle.tryLock do throw (IO.userError "another writer holds this directory")
    try action finally handle.unlock

end PolyFunIO.Storage
