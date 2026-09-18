/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament

/-! # Ordinary public-import smoke test from an independent Lake package -/

public section

open Parliament

example (rules : Rules) (s : AssemblyState wordDomain) (input : EnabledInput rules s) :
    LegalStep rules s input.command ((meetingSystem wordDomain rules).update s input)
      input.events := system_update_legal rules s input

example (rules : Rules) (s last : AssemblyState wordDomain)
    (commands : List (Command wordDomain)) (events : List Event) :
    replay rules s commands = .ok (last, events) ↔ LegalTrace rules s commands last events :=
  replay_iff rules s commands last events

example : WordEdit.apply ["fund", "library"] ⟨1, 1, ["museum"]⟩ =
    some ["fund", "museum"] := by decide

example (rules : Rules) (s : AssemblyState wordDomain) :
    boundedScript rules 0 s = IPFunctor.IFreeM.pure () := rfl

example (rules : Rules) (s : AssemblyState wordDomain)
    (choose : (state : AssemblyState wordDomain) → Except RuleError (EnabledInput rules state)) :
    (boundedScript rules 0 s).interpret choose = .ok ⟨s, ()⟩ := rfl

example (config : App.Configuration) (journal : Journal wordDomain config.rules)
    (input : EnabledInput config.rules journal.state) :
    (App.finishPersist journal input (.ok ())).committed.history.commands =
      journal.history.commands ++ [input.command] :=
  App.successful_persistence_extends journal input

example (rules : Rules) (journal : Journal wordDomain rules) (metadata : App.Metadata)
    (payload : App.Artifacts metadata journal) :
    payload.markdown = App.renderMarkdown metadata journal ∧
      payload.json = App.renderJson metadata journal := payload.faithful

example (rules : Rules) (first second : Journal wordDomain rules)
    (initial : first.initial = second.initial)
    (commands : first.history.commands = second.history.commands) (meeting : Nat) :
    (draftMinutes first meeting).entries = (draftMinutes second meeting).entries :=
  draftMinutes_reconstruction first second initial commands meeting

example {rules : Rules} {s last : AssemblyState wordDomain}
    {commands : List (Command wordDomain)} {events : List Event}
    (path : MeetingPath rules s commands last events) :
    (Walkthrough.toPrefix path).last = last ∧
      (Walkthrough.toPrefix path).events Walkthrough.commandLabel = commands :=
  ⟨Walkthrough.toPrefix_last path, Walkthrough.toPrefix_commands path⟩

example (config : App.Configuration) (state : App.State config) :
    ITree.TauFree (Walkthrough.behaviorTree config state) :=
  Walkthrough.behaviorTree_tauFree config state

example (config : App.Configuration) (fuel : Nat) (state : App.State config) :
    Walkthrough.forgetLog ((App.application config).runChunk
      (Walkthrough.loggedHandler config) fuel state) =
      (App.application config).runChunk (App.memoryHandler config) fuel state :=
  Walkthrough.forget_logged_run config fuel state

example (rules : Rules) (initial : AssemblyState wordDomain) (valid : initial.WellFormed) :
    (Walkthrough.meetingSafety rules initial).init initial := ⟨rfl, valid⟩
