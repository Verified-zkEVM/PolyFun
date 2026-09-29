/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Memory
public import PolyFun.Control.Monad.Hom.Writer
public import PolyFun.PFunctor.Handler.Instrumentation

/-! # Instrumenting the same application through a WriterT handler

The extra log is an observation of requested effects, not evidence that an external
filesystem carried them out. Erasing it is a monad homomorphism, so the core driver
transports the per-effect agreement to every finite application execution.
-/

public section

namespace Parliament.Walkthrough

open PFunctor PFunctor.DynSystem Parliament.App

/-- Stable labels for the five kinds of application interaction. -/
inductive EffectTag where
  | read | judge | tell | persist | publish
  deriving DecidableEq, Repr

/-- Discard effect payloads while retaining their observable kind. -/
def effectTag {config : Configuration} : Effect config → EffectTag
  | .read _ => .read
  | .judge _ => .judge
  | .tell _ => .tell
  | .persist _ => .persist
  | .publish .. => .publish

/-- A backend log layered over the original deterministic handler state. -/
abbrev LoggedMemory := WriterT (List EffectTag) (StateM Memory)

/-- Erase only instrumentation; retain the original handler's value and state changes. -/
def forgetLog : LoggedMemory →ᵐ StateM Memory := WriterT.eraseHom [] List.append

/-- Record each requested effect while answering it with the existing memory backend. -/
def loggedHandler (config : Configuration) : Handler LoggedMemory (Effects config) :=
  (memoryHandler config).withTraceAppend (fun effect _ => [effectTag effect])

/-- Per-query erasure preserves the response and all underlying backend state. -/
theorem forget_loggedHandler (config : Configuration) :
    Handler.mapTarget (fun value => forgetLog value) (loggedHandler config) =
      memoryHandler config := by
  funext effect
  simp only [Handler.mapTarget, loggedHandler, Handler.withTraceAppend_apply,
    forgetLog, WriterT.eraseHom_apply]
  rfl

/-- The core transport theorem lifts per-query erasure to an entire application chunk. -/
theorem forget_logged_run (config : Configuration) (fuel : Nat) (state : State config) :
    forgetLog ((application config).runChunk (loggedHandler config) fuel state) =
      (application config).runChunk (memoryHandler config) fuel state := by
  have transported := (application config).runChunk_natural
    (loggedHandler config) forgetLog fuel state
  simpa only [forget_loggedHandler] using transported

end Parliament.Walkthrough
