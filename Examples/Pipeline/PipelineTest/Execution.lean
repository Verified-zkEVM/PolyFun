/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Pipeline.Network
public import Pipeline.Correctness
meta import Pipeline.Network

/-! # Network execution against an independent sequential report specification -/

public section

open Pipeline PFunctor Interaction.Execution.ReactiveNetwork

/-- Read attempts are recorded even when a file is missing. -/
def readMemory : Handler (StateM (List String)) Files := fun path ↦ do
  modify (· ++ [path])
  return match (path : String) with
    | "empty" => .ok ByteArray.empty
    | "unicode" => .ok "α\nβ\n".toUTF8
    | "missing" => .error "not found"
    | _ => .ok "one\ntwo".toUTF8

/-- The same path changes on every read, so a resumed re-read changes the report. -/
def readChanging : Handler (StateM Nat) Files := fun _ ↦ do
  let version ← get
  set (version + 1)
  return .ok (ByteArray.mk (Array.replicate version 10))

/-- Every activation split must preserve order, results, and exactly-once read effects. -/
def executionTests : IO Unit := do
  for paths in [[], ["empty"], ["unicode"], ["missing"],
      ["a", "missing", "a", "unicode", "empty"]] do
    let budget := activationBudget paths
    let (expected, expectedReads) := (reference readMemory paths).run []
    for cut in List.range (budget + 1) do
      let (state, reads) := (runChunks readMemory paths [cut, budget - cut]).run []
      unless outcome (collectorId readMemory paths) state == some (.returned expected) &&
          reads == expectedReads && state.elapsed == budget do
        throw (IO.userError s!"Pipeline split {cut}/{budget} changed report or read effects")
    let (zero, zeroReads) := (run readMemory paths 0).run []
    unless zeroReads.isEmpty && zero.elapsed == 0 do
      throw (IO.userError "A zero budget performed a read")
    if !paths.isEmpty then
      let (short, _) := (run readMemory paths (budget - 1)).run []
      unless (outcome (collectorId readMemory paths) short).isNone do
        throw (IO.userError "An unfinished prefix claimed a complete report")
  let paths := ["same", "same", "same"]
  let budget := activationBudget paths
  let (expected, expectedReads) := (reference readChanging paths).run 0
  for cut in List.range (budget + 1) do
    let (state, reads) := (runChunks readChanging paths [cut, budget - cut]).run 0
    unless outcome (collectorId readChanging paths) state == some (.returned expected) &&
        reads == expectedReads do
      throw (IO.userError s!"Changing file at split {cut}: resumed execution repeated a read")
  IO.println "Pipeline reports, failures, and every activation split: ok"

/-- info: Pipeline reports, failures, and every activation split: ok -/
#guard_msgs in
#eval executionTests

example (files : FileMap) (paths : List String) :
    ∃ value, outcome (collectorId (m := Id) files paths)
      (run (m := Id) files paths (activationBudget paths)) = some value := by
  exact (budgetCertificate files paths).runToken_terminal _ _ _ ⟨0, rfl⟩ (by rfl) rfl
