/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Control.ULift
public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler.Instrumentation

/-!
# Handler instrumentation regression tests

Producer-level canaries for effect ordering, failure behavior,
response-dependent writer events, noncommutative trace accumulation, target
lifting across universes, and instrumentation of a multi-node `FreeM`
program.
-/

@[expose] public section

namespace PFunctor.Handler.Instrumentation.Tests

/-- Two distinguishable operations, each answered by a natural number. -/
@[reducible]
def Q : PFunctor.{0, 0} := { A := Bool, B := fun _ => Nat }

/-- Events distinguish when an operation starts, when its handler runs, and
the response observed after it returns. -/
inductive Event where
  | before (operation : Bool)
  | handled (operation : Bool) (response : Nat)
  | after (operation : Bool) (response : Nat)
  deriving DecidableEq, Repr

/-- An order-sensitive event log with concatenation as multiplication. -/
structure EventLog where
  events : List Event
  deriving DecidableEq, Repr

instance : Monoid EventLog where
  one := ⟨[]⟩
  mul left right := ⟨left.events ++ right.events⟩
  one_mul := fun ⟨_activities⟩ => rfl
  mul_one := fun ⟨activities⟩ => congrArg EventLog.mk (List.append_nil activities)
  mul_assoc := fun ⟨left⟩ ⟨middle⟩ ⟨right⟩ =>
    congrArg EventLog.mk (List.append_assoc left middle right)

/-- A writer-valued handler whose two branches have distinguishable answers. -/
def writerHandler : Handler (Writer EventLog) Q
  | true => do
      tell ⟨[Event.handled true 2]⟩
      return 2
  | false => do
      tell ⟨[Event.handled false 5]⟩
      return 5

def beforeWriter (operation : Bool) : Writer EventLog PUnit :=
  tell ⟨[Event.before operation]⟩

def afterWriter (operation : Bool) (response : Nat) :
    Writer EventLog PUnit :=
  tell ⟨[Event.after operation response]⟩

/-- Pre-insertion occurs before the underlying handler. -/
example :
    Id.run (writerHandler.preInsert beforeWriter true).run =
      (2, ⟨[Event.before true, Event.handled true 2]⟩) := by
  rw [Handler.preInsert_apply]
  change (2, (⟨[Event.before true, Event.handled true 2]⟩ : EventLog)) = _
  rfl

/-- Post-insertion observes the response and occurs after the handler. -/
example :
    Id.run (writerHandler.postInsert afterWriter false).run =
      (5, ⟨[Event.handled false 5, Event.after false 5]⟩) := by
  rw [Handler.postInsert_apply]
  change (5, (⟨[Event.handled false 5, Event.after false 5]⟩ : EventLog)) = _
  rfl

/-- A failing base handler for transformer-order canaries. -/
def failingHandler : Handler Option Q := fun _ => none

/-- `WriterT` over `Option` discards a pre-inserted log when the handler
fails, because the entire writer result is absent. -/
example :
    (failingHandler.withTraceBefore (fun operation =>
      (⟨[Event.before operation]⟩ : EventLog)) true).run = none := by
  simp [failingHandler]

/-- A post-inserted event is skipped when the underlying handler fails. -/
example :
    (failingHandler.withTrace (fun operation response =>
      (⟨[Event.after operation response]⟩ : EventLog)) false).run = none := by
  simp [failingHandler]

/-- With `OptionT` over `Writer`, the outer writer retains a pre-inserted event
even when the inner optional result fails. -/
def failingLoggedHandler : Handler (OptionT (Writer EventLog)) Q :=
  fun _ => failure

def beforeLoggedOption (operation : Bool) :
    OptionT (Writer EventLog) PUnit :=
  OptionT.lift (tell ⟨[Event.before operation]⟩)

example :
    Id.run ((failingLoggedHandler.preInsert beforeLoggedOption true).run).run =
      ((none : Option Nat), ⟨[Event.before true]⟩) := by
  rw [Handler.preInsert_apply]
  change ((none : Option Nat), (⟨[Event.before true]⟩ : EventLog)) = _
  rfl

/-- A pure handler used to test writer instrumentation over a complete free
program. -/
def answerHandler : Handler Id Q
  | true => 2
  | false => 5

/-- The first response selects a different second operation, so this is not a
constant-branch or one-node canary. -/
def twoNodeProgram : FreeM Q Nat :=
  FreeM.liftBind true fun first =>
    FreeM.liftBind (first == 5) fun second =>
      pure (10 * first + second)

def instrumentedHandler : Handler (Writer EventLog) Q :=
  (answerHandler.withTraceBefore (fun operation =>
    (⟨[Event.before operation]⟩ : EventLog))).postInsert afterWriter

lemma instrumentedHandler_true : instrumentedHandler true =
    WriterT.mk ((2, ⟨[Event.before true, Event.after true 2]⟩) :
      Id (Nat × EventLog)) := by
  unfold instrumentedHandler
  rw [Handler.postInsert_apply, Handler.withTraceBefore_apply]
  unfold answerHandler afterWriter
  rfl

lemma instrumentedHandler_false : instrumentedHandler false =
    WriterT.mk ((5, ⟨[Event.before false, Event.after false 5]⟩) :
      Id (Nat × EventLog)) := by
  unfold instrumentedHandler
  rw [Handler.postInsert_apply, Handler.withTraceBefore_apply]
  unfold answerHandler afterWriter
  rfl

def expectedInstrumentedHandler : Handler (Writer EventLog) Q
  | true => WriterT.mk ((2, ⟨[Event.before true, Event.after true 2]⟩) :
      Id (Nat × EventLog))
  | false => WriterT.mk ((5, ⟨[Event.before false, Event.after false 5]⟩) :
      Id (Nat × EventLog))

@[simp]
lemma expectedInstrumentedHandler_true : expectedInstrumentedHandler true =
    WriterT.mk ((2, ⟨[Event.before true, Event.after true 2]⟩) :
      Id (Nat × EventLog)) := rfl

@[simp]
lemma expectedInstrumentedHandler_false : expectedInstrumentedHandler false =
    WriterT.mk ((5, ⟨[Event.before false, Event.after false 5]⟩) :
      Id (Nat × EventLog)) := rfl

lemma instrumentedHandler_eq_expected :
    instrumentedHandler = expectedInstrumentedHandler := by
  funext operation
  cases operation
  · exact instrumentedHandler_false
  · exact instrumentedHandler_true

/-- Pre- and response-dependent post-events accumulate in execution order.
The list-backed event monoid is noncommutative, so reversing node or pre/post
order changes the expected result. -/
example :
    Id.run (twoNodeProgram.liftM instrumentedHandler).run =
      (25, ⟨
        [Event.before true, Event.after true 2,
          Event.before false, Event.after false 5]⟩) := by
  rw [instrumentedHandler_eq_expected]
  unfold twoNodeProgram
  change Id.run (FreeM.liftM expectedInstrumentedHandler
    (FreeM.lift true >>= fun first =>
      FreeM.lift (first == 5) >>= fun second =>
        pure (10 * first + second))).run = _
  rw [FreeM.liftM_lift_bind, expectedInstrumentedHandler_true]
  simp only [WriterT.run_bind, WriterT.run_mk, Id.run_bind, Id.run_map]
  simp only [Id.run]
  have h : (2 == 5) = false := rfl
  rw [h, FreeM.liftM_lift_bind, expectedInstrumentedHandler_false]
  simp only [WriterT.run_bind, WriterT.run_mk]
  simp_rw [FreeM.liftM_pure]
  rfl

/-! ## Target lifting and universes -/

/-- An option computation lifted into a strictly higher result universe. -/
abbrev HighOption (alpha : Type) : Type 1 := ULift.{1, 0} (Option alpha)

instance : MonadLift Option HighOption where
  monadLift computation := ULift.up computation

/-- Positions may live above directions while the target monad is lifted into
a higher result universe. -/
@[reducible]
def UniverseQ : PFunctor.{1, 0} := { A := Type 0, B := fun _ => Nat }

def universeHandler : Handler Option UniverseQ := fun _ => some 7

example : universeHandler.liftTarget Option = universeHandler := by
  simp

example : (universeHandler.liftTarget HighOption) Nat =
    ULift.up (some 7) := by
  change ULift.up (some 7) = ULift.up (some 7)
  rfl

end PFunctor.Handler.Instrumentation.Tests
