/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Bisimulation

/-!
# Examples for labelled-transition bisimulation

These examples exercise the semantic distinction between one-step, delay, and
weak matching, as well as the separate state-level and whole-system APIs.
-/

@[expose] public section

universe uObs uState₁ uMove₁ uState₂ uMove₂ uState₃ uMove₃

namespace Control.BisimulationExamples

/-- Simulation composition permits all three systems to use independent state
and move universes. -/
example {Obs : Type uObs}
    {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsWeakSimulation L₁ L₂ r₁₂)
    (h₂₃ : IsWeakSimulation L₂ L₃ r₂₃) :
    IsWeakSimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) :=
  h₁₂.comp h₂₃

/-- Three phases used to distinguish pre- and post-visible silent closure. -/
inductive Phase where
  | start
  | middle
  | done
  deriving DecidableEq

/-- A silent transition followed by a visible transition. -/
def preSilentLTS : LTS Bool where
  State := Phase
  Move
    | .start | .middle => Unit
    | .done => Empty
  next
    | .start, _ => .middle
    | .middle, _ => .done
    | .done, move => move.elim
  label
    | .start, _ => none
    | .middle, _ => some true
    | .done, move => move.elim

/-- A visible transition followed by a silent transition. -/
def postSilentLTS : LTS Bool where
  State := Phase
  Move
    | .start | .middle => Unit
    | .done => Empty
  next
    | .start, _ => .middle
    | .middle, _ => .done
    | .done, move => move.elim
  label
    | .start, _ => some true
    | .middle, _ => none
    | .done, move => move.elim

/-- Delay closure can absorb a silent prefix that strong matching cannot. -/
example : preSilentLTS.DelayStep .start (some true) .done :=
  ⟨.middle, .single ⟨(), rfl, rfl⟩, ⟨(), rfl, rfl⟩⟩

example : ¬ preSilentLTS.Step .start (some true) .done := by
  rintro ⟨move, hlabel, _⟩
  cases move
  contradiction

/-- Weak closure can absorb a silent suffix that delay matching cannot. -/
example : postSilentLTS.WeakStep .start (some true) .done :=
  ⟨.start, .middle, .refl, ⟨(), rfl, rfl⟩,
    .single ⟨(), rfl, rfl⟩⟩

private theorem post_silentSteps_start {s : Phase}
    (h : postSilentLTS.SilentSteps .start s) : s = .start := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
      subst ih
      obtain ⟨move, hlabel, _⟩ := hlast
      cases move
      contradiction

example : ¬ postSilentLTS.DelayStep .start (some true) .done := by
  rintro ⟨mid, hsilent, hvis⟩
  have : mid = .start := post_silentSteps_start hsilent
  subst mid
  obtain ⟨move, _, hnext⟩ := hvis
  cases move
  contradiction

/-- A one-state system with a silent idle loop and a visible tick. -/
def idleLTS : LTS Bool where
  State := Unit
  Move _ := Bool
  next _ _ := ()
  label _ idle := if idle then some true else none

/-- The same visible tick without the silent idle loop. -/
def plainLTS : LTS Bool where
  State := Unit
  Move _ := Unit
  next _ _ := ()
  label _ _ := some true

/-- The silent idle move can be stuttered by delay matching. -/
theorem idle_delay_plain : DelayBisimulationEquivalent idleLTS plainLTS := by
  refine ⟨fun _ _ => True, ⟨?_, ?_⟩, fun _ => ⟨(), trivial⟩,
    fun _ => ⟨(), trivial⟩⟩
  · rintro _ _ _ label _ ⟨move, hlabel, _⟩
    cases move with
    | false =>
        change none = label at hlabel
        subst label
        exact ⟨(), Relation.ReflTransGen.refl, trivial⟩
    | true =>
        change some true = label at hlabel
        subst label
        exact ⟨(), ⟨(), Relation.ReflTransGen.refl,
          ⟨(), by simp [plainLTS], rfl⟩⟩, trivial⟩
  · rintro _ _ _ label _ ⟨move, hlabel, _⟩
    change some true = label at hlabel
    subst label
    exact ⟨(), ⟨(), Relation.ReflTransGen.refl,
      ⟨true, by simp [idleLTS], rfl⟩⟩, trivial⟩

/-- The spectrum inclusions are available at whole-system level. -/
example : WeakBisimulationEquivalent idleLTS plainLTS := idle_delay_plain.toWeak

/-- Whole-system equivalences participate in the standard relation tactics. -/
example : StrongBisimulationEquivalent plainLTS plainLTS := by rfl

example (h : DelayBisimulationEquivalent idleLTS plainLTS) :
    DelayBisimulationEquivalent plainLTS idleLTS := by
  symm
  exact h

/-- State-level bisimilarity has the three equivalence laws independently of
whether a witness relation covers either whole state space. -/
example : WeakBisimilar idleLTS idleLTS () () := WeakBisimilar.refl _ _

/-- The relation attributes are usable by the standard relation tactics. -/
example : WeakBisimilar idleLTS idleLTS () () := by rfl

example (h : WeakBisimilar idleLTS plainLTS () ()) :
    WeakBisimilar plainLTS idleLTS () () := by
  symm
  exact h

/-- The whole-system witness also supplies the expected initial-state fact. -/
theorem idle_weak_plain_state : WeakBisimilar idleLTS plainLTS () () := by
  obtain ⟨rel, hb, hleft, _⟩ := idle_delay_plain
  obtain ⟨state, hrel⟩ := hleft ()
  cases state
  exact ⟨rel, hb.toWeak, hrel⟩

example : WeakBisimilar plainLTS idleLTS () () := idle_weak_plain_state.symm

example : WeakBisimilar idleLTS idleLTS () () := by
  apply WeakBisimilar.trans
    idle_weak_plain_state
  exact idle_weak_plain_state.symm

/-- A visible one-step match embeds into both coarser transition notions. -/
example : plainLTS.Step () (some true) () := ⟨(), rfl, rfl⟩

example : plainLTS.DelayStep () (some true) () :=
  (show plainLTS.Step () (some true) () from ⟨(), rfl, rfl⟩).delay

example : plainLTS.WeakStep () (some true) () :=
  ((show plainLTS.Step () (some true) () from ⟨(), rfl, rfl⟩).delay).weak

end Control.BisimulationExamples
