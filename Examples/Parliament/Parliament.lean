/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.App.Codec
public import Parliament.App.Dialogue
public import Parliament.App.Machine
public import Parliament.App.Main
public import Parliament.App.Memory
public import Parliament.App.Preview
public import Parliament.App.Storage
public import Parliament.App.Terminal
public import Parliament.Content
public import Parliament.Engine
public import Parliament.Foundation
public import Parliament.Interaction
public import Parliament.Invariants
public import Parliament.Minutes.Basic
public import Parliament.Minutes.Correspondence
public import Parliament.Minutes.Document
public import Parliament.Minutes.History
public import Parliament.Minutes.Render
public import Parliament.Model
public import Parliament.Procedure.Actions
public import Parliament.Procedure.Agenda
public import Parliament.Procedure.Disposition
public import Parliament.Procedure.Helpers
public import Parliament.Procedure.Minutes
public import Parliament.Replay
public import Parliament.Rulebook
public import Parliament.Walkthrough.Attendance
public import Parliament.Walkthrough.Behavior
public import Parliament.Walkthrough.Execution
public import Parliament.Walkthrough.Handlers

/-!
# Executable parliamentary procedure and certified draft minutes

A bounded RONR case study of indexed interaction, legal histories, dynamical execution,
and interchangeable IO handlers. See `Examples/Parliament/README.md` for the runnable
walkthrough and the explicit specification and physical-IO proof boundary.
-/
