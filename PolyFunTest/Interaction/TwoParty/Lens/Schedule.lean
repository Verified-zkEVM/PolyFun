/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Compose

/-!
# Schedule exchange with ordered state effects

An effectful observer changes the order of the trace. Pure observers preserve the complete
execution, including the trace, while owners and the focal terminal action may have effects.
-/

@[expose] public section

namespace Interaction.TwoParty.Lens.ScheduleTest
open PFunctor
open FreeM (PathAlong)

abbrev L := PFunctor.Lens.id rolePoly.{0}
abbrev Trace := StateM (List String)
abbrev done : FreeM rolePoly.{0} PUnit.{1} := .pure ⟨⟩
abbrev send : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.sender, Bool) (fun _ => done)
abbrev receive : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.receiver, Bool) (fun _ => done)

/-- Record an action in execution order. -/
def note (event : String) : Trace Unit := modify (· ++ [event])

abbrev focalEnd : Trace Nat := do note "focal end"; pure 7
abbrev sender : Focal L Trace send (fun _ => Nat) := do
  note "send"; pure ⟨true, focalEnd⟩
abbrev effectfulObserver : Counterpart L Trace send (fun _ => Unit) := do
  note "observe"; pure (fun _ => (pure () : Trace Unit))
abbrev pureObserver : Counterpart L Trace send (fun _ => Unit) := by
  change Trace (Bool → Trace Unit)
  exact pure (fun _ => pure ())

example : (runWith .focalFirst send sender effectfulObserver).run [] =
    (⟨⟨true, ⟨⟩⟩, 7, ()⟩, ["send", "observe", "focal end"]) := by
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  rfl

example : (runWith .counterpartFirst send sender effectfulObserver).run [] =
    (⟨⟨true, ⟨⟩⟩, 7, ()⟩, ["observe", "send", "focal end"]) := by
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  rfl

example : ((runWith .focalFirst send sender effectfulObserver).run []).2 ≠
    ((runWith .counterpartFirst send sender effectfulObserver).run []).2 := by
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  change ["send", "observe", "focal end"] ≠ ["observe", "send", "focal end"]
  decide

theorem sender_pureObservers : PureObservers (m := Trace) send sender pureObserver := by
  refine ⟨(b : Bool) × Trace Nat, Unit, sender, pure (), id,
    (fun _ _ => (pure () : Trace Unit)), ?_, ?_, ?_, ?_⟩
  · exact (id_map (f := Trace) sender).symm
  · rfl
  · exact ⟨(), rfl⟩
  · intro i j
    exact ⟨(), rfl⟩

example : runWith .focalFirst send sender pureObserver =
    runWith .counterpartFirst send sender pureObserver :=
  runWith_eq_of_pureObservers send sender pureObserver sender_pureObservers

example : (runWith .counterpartFirst send sender pureObserver).run [] =
    (⟨⟨true, ⟨⟩⟩, 7, ()⟩, ["send", "focal end"]) := by
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  rfl

abbrev focalObserver : Focal L Trace receive (fun _ => Nat) := by
  change Trace (Bool → Trace Nat)
  exact pure (fun _ => focalEnd)
abbrev sample : Trace Bool := do note "challenge"; pure false
abbrev receiver : Counterpart L Trace receive (fun _ => Unit) :=
  (fun b => ⟨b, (pure () : Trace Unit)⟩) <$> sample

theorem receiver_pureObservers : PureObservers (m := Trace) receive focalObserver receiver := by
  refine ⟨Unit, Bool, pure (), sample, (fun _ _ => focalEnd),
    (fun b => ⟨b, pure ()⟩), ?_, rfl, ?_, ?_⟩
  · rfl
  · exact ⟨(), rfl⟩
  · intro i j
    exact ⟨(), rfl⟩

example : runWith .focalFirst receive focalObserver receiver =
    runWith .counterpartFirst receive focalObserver receiver :=
  runWith_eq_of_pureObservers receive focalObserver receiver receiver_pureObservers

example : (runWith .focalFirst receive focalObserver receiver).run [] =
    (⟨⟨false, ⟨⟩⟩, 7, ()⟩, ["challenge", "focal end"]) := by
  simp only [runWith_node, done, FreeM.pure_eq_pure, runWith_done]
  rfl

/-- The counterpart leaf is effectful, but the suffix's first focal slot is pure. -/
abbrev counterpartEnd : Trace Unit := do note "counterpart end"; pure ()
abbrev build (_ : PathAlong L done) (_ : Unit) :
    Trace (Focal L Trace receive (fun _ => Nat)) := pure focalObserver

theorem effectfulSeam : SeamCommutes (l := L) (m := Trace) (s₁ := done) (s₂ := fun _ => receive)
    (MidP := fun _ => Unit) (MidC := fun _ => Unit) (OutP := fun _ => Nat)
    counterpartEnd build := by
  intro mid
  have h : (build ⟨⟩ mid >>= Strategy.splitSlot) = pure focalObserver := by
    simp only [build, Strategy.splitSlot, focalObserver, pure_bind]
    rfl
  rw [h]
  exact ActionsCommute.pure_left _ _

example : run (done.append (fun _ => receive))
    (Focal.compFlat (l := L) (s₁ := done) (Mid := fun _ => Unit)
      (Out := fun _ => Nat) (pure ()) build)
    (Counterpart.appendFlatM (l := L) (s₁ := done) (Mid := fun _ => Unit)
      (Out := fun _ => Unit) counterpartEnd (fun _ _ => receiver)) = (do
      let ⟨tr, op, _⟩ ← run (l := L) done (OutP := fun _ => Unit)
        (OutC := fun _ => Unit) (pure ()) counterpartEnd
      let next ← build tr op
      let ⟨tail, outP, outC⟩ ← run receive next receiver
      pure ⟨FreeM.PathAlong.append L done (fun _ => receive) tr tail, outP, outC⟩) :=
  run_compFlat_appendFlatM (l := L) (s₁ := done) (s₂ := fun _ => receive)
    (MidP := fun _ => Unit) (MidC := fun _ => Unit)
    (OutP := fun _ => Nat) (OutC := fun _ => Unit)
    (pure ()) build counterpartEnd (fun _ _ => receiver) effectfulSeam

end Interaction.TwoParty.Lens.ScheduleTest
