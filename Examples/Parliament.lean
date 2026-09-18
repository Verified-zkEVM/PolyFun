/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Codec
public import Examples.Parliament.App.Machine
public import Examples.Parliament.App.Main
public import Examples.Parliament.App.Memory
public import Examples.Parliament.App.Storage
public import Examples.Parliament.App.Terminal
public import Examples.Parliament.Content
public import Examples.Parliament.Engine
public import Examples.Parliament.Foundation
public import Examples.Parliament.Interaction
public import Examples.Parliament.Invariants
public import Examples.Parliament.Minutes.Correspondence
public import Examples.Parliament.Minutes.Document
public import Examples.Parliament.Minutes.History
public import Examples.Parliament.Minutes.Render
public import Examples.Parliament.Model
public import Examples.Parliament.Procedure.Actions
public import Examples.Parliament.Procedure.Agenda
public import Examples.Parliament.Procedure.Disposition
public import Examples.Parliament.Procedure.Helpers
public import Examples.Parliament.Replay
public import Examples.Parliament.Rulebook

/-!
# Executable parliamentary procedure and certified draft minutes

A bounded RONR case study of indexed interaction, legal histories, dynamical execution,
and interchangeable IO handlers. See `Examples/Parliament/README.md` for the runnable
walkthrough and the explicit specification and physical-IO proof boundary.
-/
