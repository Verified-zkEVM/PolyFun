/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Replay
public import PolyFun.IPFunctor.Free.Family
public import PolyFun.PFunctor.Dynamical.Basic
public import PolyFun.PFunctor.Handler

/-!
# Polynomial meeting and judgment interfaces

Every direction of `MeetingP` is a certified legal input. An interpreter chooses
directions during execution, including answers to the currently outstanding judgment.
The same source map drives both indexed scripts and the ongoing dynamical system.
-/

@[expose] public section

namespace Parliament

variable {D : MotionDomain}

/-- A response indexed by the exact judgment request it answers. -/
structure JudgmentReply (request : JudgmentRequest D) where
  /-- The external handler's ruling and recorded explanation. -/
  answer : Ruling

/-- Polynomial interface whose responses are indexed by judgment requests. -/
def JudgmentSig (D : MotionDomain) : PFunctor where
  A := JudgmentRequest D
  B := JudgmentReply

/-- A handler can be supplied by a chair interface, a test script, or another process. -/
abbrev JudgmentHandler (D : MotionDomain) (m : Type → Type) :=
  PFunctor.Handler m (JudgmentSig D)

/-- Convert a response into a command for its exact request and revision. -/
def JudgmentReply.command {request : JudgmentRequest D} (reply : JudgmentReply request)
    (chair : MemberId) : Command D :=
  .answerJudgment chair request.id request.revision reply.answer

/-- A concrete direction includes its command, output, and inference derivation. -/
structure EnabledInput (rules : Rules) (s : AssemblyState D) where
  /-- The concrete command selected by the environment. -/
  command : Command D
  /-- The certified successor state. -/
  next : AssemblyState D
  /-- The events produced by the selected command. -/
  events : List Event
  legal : LegalStep rules s command next events

/-- Validate a raw command and package its legal-step certificate. -/
def checkInput (rules : Rules) (s : AssemblyState D) (command : Command D) :
    Except RuleError (EnabledInput rules s) :=
  match h : step rules s command with
  | .error error => .error error
  | .ok (next, events) => .ok ⟨command, next, events, step_sound rules s next command events h⟩

/-- Ask an external handler for the outstanding judgment, then validate its concrete reply. -/
def answerInput {m : Type → Type} [Monad m] (rules : Rules) (s : AssemblyState D)
    (handler : JudgmentHandler D m) : m (Except RuleError (EnabledInput rules s)) := do
  match s.judgment with
  | none => pure (.error .judgmentRequired)
  | some request =>
    let reply ← handler request
    pure (checkInput rules s (reply.command s.chair))

/-- One await-input shape; the next state depends on the actual response. -/
def MeetingP (D : MotionDomain) (rules : Rules) : IPFunctor.Endo (AssemblyState D) where
  A _ := Unit
  B s _ := EnabledInput rules s
  src _ _ input := input.next

/-- A finite PolyFun indexed free computation over legal meeting inputs. -/
abbrev Script (rules : Rules) (X : AssemblyState D → Type) (s : AssemblyState D) :=
  IPFunctor.IFreeM (MeetingP D rules) X s

/-- Observe at most `fuel` inputs. Reaching the bound is not a claim of adjournment. -/
def boundedScript (rules : Rules) : (fuel : Nat) → (s : AssemblyState D) →
    Script rules (fun _ => Unit) s
  | 0, _ => .pure ()
  | fuel + 1, _ => .liftBind () (fun input => boundedScript rules fuel input.next)

/-- Interpret a finite script using PolyFun's monadic fold, retaining its final state and value. -/
def Script.interpret {m : Type → Type} [Monad m] {rules : Rules}
    {X : AssemblyState D → Type} {s : AssemblyState D} (script : Script rules X s)
    (choose : (state : AssemblyState D) → m (EnabledInput rules state)) :
    m (Sigma X) := script.mapM (fun state _ => choose state) (fun state x => pure ⟨state, x⟩)

/-- The ongoing PolyFun dynamical system driven by certified meeting inputs. -/
def meetingSystem (D : MotionDomain) (rules : Rules) :
    PFunctor.DynSystem (AssemblyState D) (MeetingP D rules).sigmaPFunctor :=
  PFunctor.DynSystem.mk' (fun s => ⟨s, ()⟩) (fun _ input => input.next)

theorem system_update_eq_src (rules : Rules) (s : AssemblyState D) (input : EnabledInput rules s) :
    (meetingSystem D rules).update s input = (MeetingP D rules).src s () input := rfl

theorem system_update_legal (rules : Rules) (s : AssemblyState D) (input : EnabledInput rules s) :
    LegalStep rules s input.command ((meetingSystem D rules).update s input) input.events :=
  input.legal

theorem system_update_wellFormed (rules : Rules) (s : AssemblyState D)
    (input : EnabledInput rules s) : ((meetingSystem D rules).update s input).WellFormed :=
  input.legal.wellFormed

/-- A finite path through the open machine, recording the chosen directions. -/
inductive MeetingPath (rules : Rules) : AssemblyState D → List (Command D) →
    AssemblyState D → List Event → Type where
  | nil (s : AssemblyState D) : MeetingPath rules s [] s []
  | cons {s last : AssemblyState D} (input : EnabledInput rules s)
      {commands : List (Command D)} {events : List Event}
      (tail : MeetingPath rules input.next commands last events) :
      MeetingPath rules s (input.command :: commands) last (input.events ++ events)

theorem MeetingPath.legalTrace {rules : Rules} {s last : AssemblyState D}
    {commands : List (Command D)} {events : List Event}
    (path : MeetingPath rules s commands last events) :
    LegalTrace rules s commands last events := by
  induction path with
  | nil s => exact .nil s
  | cons input tail ih => exact .cons input.legal ih

theorem MeetingPath.replays {rules : Rules} {s last : AssemblyState D}
    {commands : List (Command D)} {events : List Event}
    (path : MeetingPath rules s commands last events) :
    replay rules s commands = .ok (last, events) :=
  replay_complete path.legalTrace

theorem LegalTrace.hasMeetingPath {rules : Rules} {s last : AssemblyState D}
    {commands : List (Command D)} {events : List Event}
    (trace : LegalTrace rules s commands last events) :
    Nonempty (MeetingPath rules s commands last events) := by
  induction trace with
  | nil s => exact ⟨.nil s⟩
  | cons head tail ih =>
    obtain ⟨path⟩ := ih
    exact ⟨.cons ⟨_, _, _, head⟩ path⟩

theorem meetingPath_iff_legalTrace (rules : Rules) (s last : AssemblyState D)
    (commands : List (Command D)) (events : List Event) :
    Nonempty (MeetingPath rules s commands last events) ↔
      LegalTrace rules s commands last events :=
  ⟨fun ⟨path⟩ => path.legalTrace, LegalTrace.hasMeetingPath⟩

/-- The observable execution of a finite indexed script. -/
inductive ScriptRun (rules : Rules) {X : AssemblyState D → Type} :
    {s : AssemblyState D} → Script rules X s → List (Command D) →
    (last : AssemblyState D) → X last → List Event → Prop where
  | pure {s : AssemblyState D} (x : X s) : ScriptRun rules (.pure x) [] s x []
  | input {s last : AssemblyState D} (direction : EnabledInput rules s)
      (continuation : (input : EnabledInput rules s) → Script rules X input.next)
      {commands : List (Command D)} {result : X last} {events : List Event}
      (tail : ScriptRun rules (continuation direction) commands last result events) :
      ScriptRun rules (.liftBind () continuation) (direction.command :: commands)
        last result (direction.events ++ events)

theorem ScriptRun.legalTrace {rules : Rules} {X : AssemblyState D → Type}
    {s last : AssemblyState D} {script : Script rules X s} {commands : List (Command D)}
    {result : X last} {events : List Event}
    (run : ScriptRun rules script commands last result events) :
    LegalTrace rules s commands last events := by
  induction run with
  | pure _ => exact .nil _
  | input direction continuation tail ih => exact .cons direction.legal ih

theorem ScriptRun.replays {rules : Rules} {X : AssemblyState D → Type}
    {s last : AssemblyState D} {script : Script rules X s} {commands : List (Command D)}
    {result : X last} {events : List Event}
    (run : ScriptRun rules script commands last result events) :
    replay rules s commands = .ok (last, events) := replay_complete run.legalTrace

end Parliament
