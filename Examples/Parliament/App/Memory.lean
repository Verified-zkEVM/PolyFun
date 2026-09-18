/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Machine

/-! # In-memory effect backend with explicit failure injection -/

@[expose] public section

namespace Parliament.App

/-- Stored output at one immutable source revision. -/
structure MemoryExport where
  /-- Source revision used as the publication identity. -/
  revision : Nat
  /-- Human-readable payload. -/
  markdown : String
  /-- Structured payload. -/
  json : String
  deriving DecidableEq

/-- Deterministic backend state, with faults corresponding to observable IO failure boundaries. -/
structure Memory where
  /-- Operator actions remaining; exhaustion behaves as terminal EOF. -/
  actions : List Action := []
  /-- External ruling replies; exhaustion cancels the judgment prompt. -/
  rulings : List Ruling := []
  /-- Last stored journal bytes represented as a UTF-8 string. -/
  journal : Option String := none
  /-- Immutable published payloads. -/
  exports : List MemoryExport := []
  /-- Diagnostics issued by the state machine. -/
  messages : List String := []
  /-- Persistence attempts, including failed attempts. -/
  persistCount : Nat := 0
  /-- Publication attempts, including failed attempts. -/
  publishCount : Nat := 0
  /-- Fail this one-based persistence attempt. -/
  failPersistAt : Option Nat := none
  /-- Model a persistence failure after the backend may already have replaced the file. -/
  failAfterWrite : Bool := false
  /-- Reject publications before storing their payloads. -/
  failPublish : Bool := false
  /-- Simulate a readback mismatch; no successful publication is reported. -/
  mismatchReadback : Bool := false

/-- Interpret the same polynomial effects used by the real IO application. -/
def memoryHandler (config : Configuration) : PFunctor.Handler (StateM Memory) (Effects config) :=
  fun effect => match effect with
  | .read _ => do
      let memory ← get
      match memory.actions with
      | [] => pure (Except.ok .quit)
      | action :: rest => set { memory with actions := rest }; pure (Except.ok action)
  | .judge _ => do
      let memory ← get
      match memory.rulings with
      | [] => pure (Except.ok none)
      | answer :: rest =>
        set { memory with rulings := rest }
        pure (Except.ok (some ⟨answer⟩))
  | .tell message => do
      let memory ← get
      set { memory with messages := memory.messages ++ [message] }
      pure (Except.ok ())
  | .persist journal => do
      let memory ← get
      let count := memory.persistCount + 1
      let fail := memory.failPersistAt == some count
      set { memory with
        persistCount := count,
        journal := if !fail || memory.failAfterWrite then
          some (encodeJson (snapshot config journal))
          else memory.journal }
      if fail then pure (Except.error "injected journal failure") else pure (Except.ok ())
  | .publish journal payload => do
      let memory ← get
      let output : MemoryExport := ⟨journal.state.revision, payload.markdown, payload.json⟩
      set { memory with publishCount := memory.publishCount + 1 }
      if memory.failPublish then return Except.error "injected publication failure"
      if memory.mismatchReadback then return Except.error "injected readback mismatch"
      match memory.exports.find? (fun e => e.revision == output.revision) with
      | some previous =>
        if previous == output then pure (Except.ok ())
        else pure (Except.error "immutable export conflict")
      | none =>
        modify fun m => { m with exports := m.exports ++ [output] }
        pure (Except.ok ())

end Parliament.App
