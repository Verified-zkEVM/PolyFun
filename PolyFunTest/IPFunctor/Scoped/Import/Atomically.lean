/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.IPFunctor.Scoped.Import.Submit
public meta import PolyFun.IPFunctor.Scoped.Import.Submit
public meta import Lean.Elab.Command

/-!
# Rollback after a resource limit

`IPFunctor.Import.atomically` restores the environment when its step fails, also when a heartbeat
limit stops the step: the test adds a definition and then exceeds the limit, and the definition is
gone afterwards. A restore in an ordinary `try … catch` never runs for that exception, so the
definition would remain.
-/

public section

namespace PolyFunTest.ImportAtomically

open Lean Elab Command IPFunctor.Import

/-- Add the definition `name := 0`, then exceed a heartbeat limit of one heartbeat. -/
meta def addThenTimeout (name : Name) : MetaM Unit := do
  submitDef name (mkConst ``Nat) (mkNatLit 0) (← Budget.ambient)
  Core.checkMaxHeartbeatsCore "addThenTimeout" `maxHeartbeats 1

/-- Run `addThenTimeout` inside `atomically`. -/
elab "#atomic_timeout " name:ident : command => liftTermElabM do
  atomically (addThenTimeout ((← getCurrNamespace) ++ name.getId))

/-- Report whether a declaration of the given name exists, without resolving it. -/
elab "#declared " name:ident : command => do
  logInfo m!"{name.getId}: {(← getEnv).contains name.getId}"

/--
error: (deterministic) timeout at `addThenTimeout`, maximum number of heartbeats (0) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#atomic_timeout rolledBack

/-- info: PolyFunTest.ImportAtomically.rolledBack: false -/
#guard_msgs in
#declared PolyFunTest.ImportAtomically.rolledBack

-- The same step with its restore in `try … catch`: the handler does not run, and the definition
-- remains until the outer `withoutModifyingEnv` discards it.
/-- info: the step failed: true; the definition remains: true -/
#guard_msgs in
run_meta withoutModifyingEnv do
  let name := `PolyFunTest.ImportAtomically.kept
  let env ← getEnv
  let failed ← tryCatchRuntimeEx
    (do (try addThenTimeout name catch _ => setEnv env); pure false)
    fun _ => pure true
  logInfo m!"the step failed: {failed}; the definition remains: {(← getEnv).contains name}"

end PolyFunTest.ImportAtomically
