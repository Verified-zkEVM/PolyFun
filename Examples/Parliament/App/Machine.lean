/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Minutes.Render
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # The terminal application's explicit persistence and publication protocol -/

@[expose] public section

namespace Parliament.App

/-- Operator actions are distinct from parliamentary commands and never imply adjournment. -/
inductive Action where
  | command (command : Command wordDomain)
  | judge
  | export
  | status
  | quit
  | invalid (message : String)

/-- Typed application effects, interpreted by a real or simulated backend. -/
inductive Effect (config : Configuration) where
  | read (state : AssemblyState wordDomain)
  | judge (request : JudgmentRequest wordDomain)
  | tell (message : String)
  | persist (journal : Journal wordDomain config.rules)
  | publish (journal : Journal wordDomain config.rules)
      (payload : Artifacts config.metadata journal)

/-- Backend failures are explicit responses, never a successful publication certificate. -/
def Effect.Response {config : Configuration} : Effect config → Type
  | .read _ => Except String Action
  | .judge request => Except String (Option (JudgmentReply request))
  | .tell _ | .persist _ | .publish .. => Except String Unit

/-- Polynomial effect signature shared by the IO executable and deterministic tests. -/
def Effects (config : Configuration) : PFunctor where
  A := Effect config
  B := Effect.Response

/-- Successful or failed application exit with its last acknowledged journal. -/
structure Exit (config : Configuration) where
  /-- Last journal acknowledged after successful persistence. -/
  journal : Journal wordDomain config.rules
  /-- Process status; zero means the requested draft export completed. -/
  code : UInt32

/-- Operational phases; a validated successor is uncommitted until persistence succeeds. -/
inductive State (config : Configuration) where
  | ready (journal : Journal wordDomain config.rules)
  | persist (journal : Journal wordDomain config.rules)
      (input : EnabledInput config.rules journal.state)
  | judge (journal : Journal wordDomain config.rules) (request : JudgmentRequest wordDomain)
  | publish (journal : Journal wordDomain config.rules) (exitAfter : Bool)
  | notice (journal : Journal wordDomain config.rules) (message : String)
      (exitCode : Option UInt32 := none)
  | done (result : Exit config)

/-- Read the last acknowledged meeting state, excluding any candidate awaiting persistence. -/
def State.committed {config : Configuration} : State config → Journal wordDomain config.rules
  | .ready journal | .persist journal _ | .judge journal _ |
    .publish journal _ | .notice journal .. => journal
  | .done result => result.journal

/-- Pure validation prepares persistence; rejection retains the current certified journal. -/
def prepare {config : Configuration} (journal : Journal wordDomain config.rules)
    (command : Command wordDomain) : State config :=
  match checkInput config.rules journal.state command with
  | .error error => .notice journal s!"Rejected: {repr error}"
  | .ok input => .persist journal input

/-- Only a successful persistence response installs the polynomial system's successor. -/
def finishPersist {config : Configuration} (journal : Journal wordDomain config.rules)
    (input : EnabledInput config.rules journal.state) (response : Except String Unit) :
    State config :=
  match response with
  | .ok () =>
    .notice (journal.accept input) s!"Accepted revision {input.next.revision}."
  | .error error =>
    .notice journal ("Journal persistence failed; stop and recover by replay. " ++ error) (some 1)

/-- Process one operator action without performing IO inside the procedural state machine. -/
def handleAction {config : Configuration} (journal : Journal wordDomain config.rules) :
    Action → State config
  | .command command => prepare journal command
  | .judge => match journal.state.judgment with
    | some request => .judge journal request
    | none => .notice journal "No judgment is outstanding."
  | .export => .publish journal false
  | .quit => .publish journal true
  | .status => .notice journal
      s!"Meeting {journal.state.calendar.meeting}, revision {journal.state.revision}; \
        phase {phaseText journal.state.phase}; {journal.state.pending.length} pending questions; \
        {journal.state.suspended.length} suspended bundles."
  | .invalid message => .notice journal ("Input error: " ++ message)

/-- A single observable application interaction or a final return. -/
def machineStep (config : Configuration) (state : State config) :
    Exit config ⊕ (Effects config).Obj (State config) :=
  match state with
  | .done result => .inl result
  | .ready journal => .inr ⟨.read journal.state, fun response => match response with
      | .ok action => handleAction journal action
      | .error error => .notice journal ("Input failed: " ++ error) (some 1)⟩
  | .persist journal input =>
    .inr ⟨.persist (journal.accept input), finishPersist journal input⟩
  | .judge journal request => .inr ⟨.judge request, fun response => match response with
      | .ok (some reply) => prepare journal (reply.command journal.state.chair)
      | .ok none => .ready journal
      | .error error => .notice journal ("Judgment input failed: " ++ error) (some 1)⟩
  | .publish journal exitAfter =>
    .inr ⟨.publish journal (artifacts config.metadata journal), fun response => match response with
      | .ok () => .notice journal s!"Published draft revision {journal.state.revision}."
          (if exitAfter then some 0 else none)
      | .error error => .notice journal ("Draft publication failed: " ++ error)
          (if exitAfter then some 1 else none)⟩
  | .notice journal message exitCode => .inr ⟨.tell message, fun response => match response with
      | .error _ => .done ⟨journal, 1⟩
      | .ok () => match exitCode with
        | some code => .done ⟨journal, code⟩
        | none => .ready journal⟩

/-- An executable returning dynamical system; the generic IO driver interprets its exposed
effects. -/
def application (config : Configuration) :
    PFunctor.DynSystem.DynComputation (Effects config)
      (Journal wordDomain config.rules) (Exit config) :=
  PFunctor.DynSystem.DynComputation.ofStep (machineStep config) .ready

theorem prepare_preserves_committed {config : Configuration}
    (journal : Journal wordDomain config.rules) (command : Command wordDomain) :
    (prepare journal command).committed = journal := by
  unfold prepare
  split <;> rfl

theorem failed_persistence_preserves {config : Configuration}
    (journal : Journal wordDomain config.rules) (input : EnabledInput config.rules journal.state)
    (error : String) : (finishPersist journal input (.error error)).committed = journal := rfl

theorem successful_persistence_extends {config : Configuration}
    (journal : Journal wordDomain config.rules) (input : EnabledInput config.rules journal.state) :
    (finishPersist journal input (.ok ())).committed.history.commands =
      journal.history.commands ++ [input.command] := rfl

theorem successful_persistence_legal {config : Configuration}
    (journal : Journal wordDomain config.rules) (input : EnabledInput config.rules journal.state) :
    LegalStep config.rules journal.state input.command
      (finishPersist journal input (.ok ())).committed.state input.events := input.legal

theorem committed_wellFormed {config : Configuration} (state : State config) :
    state.committed.state.WellFormed := state.committed.wellFormed

/-- The only possible changes to acknowledged history are stuttering or one certified extension. -/
inductive CommitStep {config : Configuration} (before : Journal wordDomain config.rules) :
    Journal wordDomain config.rules → Prop where
  | unchanged : CommitStep before before
  | accepted (input : EnabledInput config.rules before.state) :
      CommitStep before (before.accept input)

theorem handleAction_preserves_committed {config : Configuration}
    (journal : Journal wordDomain config.rules) (action : Action) :
    (handleAction journal action).committed = journal := by
  cases action with
  | command command => exact prepare_preserves_committed journal command
  | judge => simp only [handleAction]; cases journal.state.judgment <;> rfl
  | «export» => rfl
  | status => rfl
  | quit => rfl
  | invalid message => rfl

/-- Every response to every exposed query preserves history or adds exactly one legal step. -/
theorem machineStep_safe (config : Configuration) (state : State config) :
    match machineStep config state with
    | .inl _ => True
    | .inr ⟨_, next⟩ =>
      ∀ response, CommitStep state.committed (next response).committed := by
  cases state with
  | done result => trivial
  | ready journal =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok action =>
      change CommitStep journal (handleAction journal action).committed
      rw [handleAction_preserves_committed]
      exact .unchanged
  | persist journal input =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok response => cases response; exact .accepted input
  | judge journal request =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok answer =>
      cases answer with
      | none => exact .unchanged
      | some reply =>
        change CommitStep journal (prepare journal (reply.command journal.state.chair)).committed
        rw [prepare_preserves_committed]
        exact .unchanged
  | publish journal exitAfter =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok response => cases response; exact .unchanged
  | notice journal message exitCode =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok response => cases response; cases exitCode <;> exact .unchanged

/-- Publication positions carry their own exact payload guarantee, for any backend whatsoever. -/
theorem publish_payload {config : Configuration} (journal : Journal wordDomain config.rules)
    (payload : Artifacts config.metadata journal) :
    payload.markdown = renderMarkdown config.metadata journal ∧
      payload.json = renderJson config.metadata journal := payload.faithful

end Parliament.App
