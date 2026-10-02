/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.App.Preview
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # The terminal application's explicit persistence and publication protocol -/

@[expose] public section

namespace Parliament.App

/-- Operator actions are distinct from parliamentary commands and never imply adjournment. -/
inductive Action where
  | command (command : Command wordDomain)
  | judge
  | compareRuling
  | export
  | status
  | inspect (revision : Nat)
  | back | forward | live
  | quit
  | invalid (message : String)

/-- Typed application effects, interpreted by a real or simulated backend. -/
inductive InteractionEffect where
  | read (state : AssemblyState wordDomain) (cursor : Option Nat)
  | judge (request : JudgmentRequest wordDomain)
  | tell (message : String)

/-- Persistence and publication are separate from interactive and speculative operations. -/
inductive StorageEffect (config : Configuration) where
  | persist (journal : Journal wordDomain config.rules)
  | publish (journal : Journal wordDomain config.rules)
      (payload : Artifacts config.metadata journal)

/-- Backend failures are explicit responses, never a successful publication certificate. -/
def InteractionEffects : PFunctor where
  A := InteractionEffect
  B
    | .read .. => Except String Action
    | .judge request => Except String (Option (JudgmentReply request))
    | .tell _ => Except String Unit

/-- Storage acknowledgements never manufacture an application input or ruling. -/
def StorageEffects (config : Configuration) : PFunctor :=
  ⟨StorageEffect config, fun _ => Except String Unit⟩

/-- Polynomial effect signature shared by the IO executable and deterministic tests. -/
abbrev Effects (config : Configuration) := InteractionEffects + StorageEffects config

/-- Successful or failed application exit with its last acknowledged journal. -/
structure Exit (config : Configuration) where
  /-- Last journal acknowledged after successful persistence. -/
  journal : Journal wordDomain config.rules
  /-- Process status; zero means the requested draft export completed. -/
  code : UInt32

/-- Operational phases; a validated successor is uncommitted until persistence succeeds. -/
inductive State (config : Configuration) where
  | ready (journal : Journal wordDomain config.rules) (cursor : Option Nat := none)
  | persist (journal : Journal wordDomain config.rules)
      (input : EnabledInput config.rules journal.state)
  | judge (journal : Journal wordDomain config.rules) (request : JudgmentRequest wordDomain)
  | publish (journal : Journal wordDomain config.rules) (exitAfter : Bool)
      (cursor : Option Nat := none)
  | notice (journal : Journal wordDomain config.rules) (message : String)
      (exitCode : Option UInt32 := none) (cursor : Option Nat := none)
  | done (result : Exit config)

/-- Read the last acknowledged meeting state, excluding any candidate awaiting persistence. -/
def State.committed {config : Configuration} : State config → Journal wordDomain config.rules
  | .ready journal _ | .persist journal _ | .judge journal _ |
    .publish journal .. | .notice journal .. => journal
  | .done result => result.journal

/-- Pure validation prepares persistence; rejection retains the current certified journal. -/
def prepare {config : Configuration} (journal : Journal wordDomain config.rules)
    (command : Command wordDomain) : State config :=
  match checkInput config.rules journal.state command with
  | .error error => .notice journal ("Rejected: " ++ error.message)
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

/-- History is ephemeral session state, outside the certified assembly and serialized journal. -/
def handleHistory {config : Configuration} (journal : Journal wordDomain config.rules)
    (revision : Nat) : State config :=
  let initial : Journal wordDomain config.rules :=
    ⟨journal.initial, journal.initialValid, journal.initial, .nil⟩
  let revision := min revision journal.state.revision
  match initial.replay (journal.history.commands.take revision) with
  | .error (index, error) => .notice journal s!"History replay failed at {index}: {repr error}"
  | .ok historical => .notice journal ("READ-ONLY HISTORY\n" ++
      renderMarkdown config.metadata historical) none (some revision)

theorem handleHistory_committed {config : Configuration}
    (journal : Journal wordDomain config.rules) (revision : Nat) :
    (handleHistory journal revision).committed = journal := by
  unfold handleHistory
  dsimp only
  split <;> rfl

/-- Process one operator action without performing IO inside the procedural state machine. -/
def handleAction {config : Configuration} (journal : Journal wordDomain config.rules) :
    Action → State config
  | .command command => prepare journal command
  | .judge => match journal.state.judgment with
    | some request => .judge journal request
    | none => .notice journal "No judgment is outstanding."
  | .compareRuling => .notice journal (Preview.compare config journal)
  | .export => .publish journal false
  | .quit => .publish journal true
  | .status => .notice journal
      s!"Meeting {journal.state.calendar.meeting}, revision {journal.state.revision}; \
        phase {phaseText journal.state.phase}; {journal.state.pending.length} pending questions; \
        {journal.state.suspended.length} suspended bundles."
  | .inspect revision => handleHistory journal revision
  | .back => handleHistory journal (journal.state.revision - 1)
  | .forward => handleHistory journal journal.state.revision
  | .live => .notice journal "Live view."
  | .invalid message => .notice journal ("Input error: " ++ message)

/-- Enforce read-only navigation at the application boundary, independently of the backend. -/
def handleSession {config : Configuration} (journal : Journal wordDomain config.rules)
    (cursor : Option Nat) (action : Action) : State config :=
  match cursor with
  | none => handleAction journal action
  | some revision => match action with
    | .command _ | .judge =>
      .notice journal "History is read-only; enter live before a command or judgment." none cursor
    | .back => handleHistory journal (revision - 1)
    | .forward => handleHistory journal (revision + 1)
    | .status => handleHistory journal revision
    | .compareRuling => .notice journal (Preview.compare config journal) none cursor
    | .invalid message => .notice journal ("Input error: " ++ message) none cursor
    | .export => .publish journal false cursor
    | _ => handleAction journal action

/-- A single observable application interaction or a final return. -/
def machineStep (config : Configuration) (state : State config) :
    Exit config ⊕ (Effects config).Obj (State config) :=
  match state with
  | .done result => .inl result
  | .ready journal cursor => .inr ⟨.inl (.read journal.state cursor), fun response =>
    match response with
      | .ok action => handleSession journal cursor action
      | .error error => .notice journal ("Input failed: " ++ error) (some 1)⟩
  | .persist journal input =>
    .inr ⟨.inr (.persist (journal.accept input)), finishPersist journal input⟩
  | .judge journal request => .inr ⟨.inl (.judge request), fun response => match response with
      | .ok (some reply) => prepare journal (reply.command journal.state.chair)
      | .ok none => .ready journal
      | .error error => .notice journal ("Judgment input failed: " ++ error) (some 1)⟩
  | .publish journal exitAfter cursor =>
    .inr ⟨.inr (.publish journal (artifacts config.metadata journal)), fun response =>
      match response with
      | .ok () => .notice journal s!"Published draft revision {journal.state.revision}."
          (if exitAfter then some 0 else none) cursor
      | .error error => .notice journal ("Draft publication failed: " ++ error)
          (if exitAfter then some 1 else none) cursor⟩
  | .notice journal message exitCode cursor => .inr ⟨.inl (.tell message), fun response =>
    match response with
      | .error _ => .done ⟨journal, 1⟩
      | .ok () => match exitCode with
        | some code => .done ⟨journal, code⟩
        | none => .ready journal cursor⟩

/-- An executable returning dynamical system; the generic IO driver interprets its exposed
effects. -/
def application (config : Configuration) :
    PFunctor.DynSystem.DynComputation (Effects config)
      (Journal wordDomain config.rules) (Exit config) :=
  PFunctor.DynSystem.DynComputation.ofStep (machineStep config) (fun journal => .ready journal)

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
  | compareRuling => rfl
  | «export» => rfl
  | status => rfl
  | inspect revision => exact handleHistory_committed journal revision
  | back => exact handleHistory_committed journal _
  | forward => exact handleHistory_committed journal _
  | live => rfl
  | quit => rfl
  | invalid message => rfl

theorem handleSession_committed {config : Configuration}
    (journal : Journal wordDomain config.rules) (cursor : Option Nat) (action : Action) :
    (handleSession journal cursor action).committed = journal := by
  cases cursor with
  | none => exact handleAction_preserves_committed journal action
  | some revision =>
    cases action <;> simp only [handleSession]
    all_goals first | rfl | exact handleHistory_committed journal _

/-- Every response to every exposed query preserves history or adds exactly one legal step. -/
theorem machineStep_safe (config : Configuration) (state : State config) :
    match machineStep config state with
    | .inl _ => True
    | .inr ⟨_, next⟩ =>
      ∀ response, CommitStep state.committed (next response).committed := by
  cases state with
  | done result => trivial
  | ready journal cursor =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok action =>
      change CommitStep journal (handleSession journal cursor action).committed
      rw [handleSession_committed]
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
  | publish journal exitAfter cursor =>
    intro response
    cases response with
    | error error => exact .unchanged
    | ok response => cases response; exact .unchanged
  | notice journal message exitCode cursor =>
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
