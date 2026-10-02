/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler
import Batteries.Lean.Except

/-! # A read-only file report

Counts refer to raw bytes and LF bytes, not Unicode characters or logical lines. A failed read
is data in the report, never an empty file. Paths are retained verbatim and may occur repeatedly.
-/

@[expose] public section

namespace Pipeline

open PFunctor

/-- Successful byte counts for one file. -/
structure Counts where
  /-- Raw byte count. -/
  bytes : Nat
  /-- Number of LF bytes, including a trailing LF when present. -/
  newlines : Nat
  deriving DecidableEq, Repr

/-- A single ordered report entry. -/
structure Entry where
  /-- The exact supplied path, not a canonicalized identity. -/
  path : String
  /-- A successful count or the read error for this occurrence. -/
  result : Except String Counts
  deriving DecidableEq, Repr

/-- The only local external effect: read a file, retaining failure explicitly. -/
abbrev Files : PFunctor where
  A := String
  B _ := Except String ByteArray

/-- Payload delivered from the loader to the analyser. -/
abbrev Loaded := String × Except String ByteArray

/-- Byte-oriented analysis, independent of filesystem and scheduling. -/
def analyse (input : Loaded) : Entry :=
  ⟨input.1, input.2.map fun bytes ↦
    ⟨bytes.size, bytes.data.toList.count 10⟩⟩

/-- Independent sequential specification; no network or component implementation is invoked. -/
def reference {m : Type → Type} [Monad m] (read : Handler m Files)
    (paths : List String) : m (List Entry) :=
  paths.mapM fun path ↦ return analyse (path, ← read path)

/-- Human-readable reports keep failures distinct from successful zero counts. -/
def Entry.render (entry : Entry) : String :=
  match entry.result with
  | .ok count => s!"{entry.path}: {count.bytes} bytes, {count.newlines} LF bytes"
  | .error error => s!"{entry.path}: ERROR: {error}"

end Pipeline
