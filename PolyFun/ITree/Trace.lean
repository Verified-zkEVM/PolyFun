/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.LTS.Trace
public import PolyFun.ITree.Bisim.Bind

/-! # Finite observations of interaction trees

This module gives `ITree F α` a labelled transition system and reuses
`Control.LTS.WeakTrace` as its finite trace semantics.

A visible observation is either:

* `Observation.event a reply`, recording a complete visible interaction—the
  event position and the environment reply that selects its continuation; or
* `Observation.ret r`, recording terminal return value `r`.

Silent `ITree.step` nodes are unlabelled. The LTS state is
`Option (ITree F α)`: `none` is the terminal state reached after observing a
return. This explicit policy means finite traces observe replies and returns,
but not the number of silent steps.
-/

@[expose] public section

universe uFA uFB uα

namespace ITree

variable {F : PFunctor.{uFA, uFB}} {α : Type uα}

/-- A visible ITree observation: a completed event/reply interaction or a
terminal return. -/
inductive Observation (F : PFunctor.{uFA, uFB}) (α : Type uα) :
    Type (max uFA uFB uα) where
  | event (a : F.A) (reply : F.B a) : Observation F α
  | ret (result : α) : Observation F α

/-- Proof-relevant moves of the ITree transition system. The shape equality
records which destructor case supplies the move. -/
inductive LTSMove (F : PFunctor.{uFA, uFB}) (α : Type uα) :
    Option (ITree F α) → Type (max uFA uFB uα) where
  | step (t : ITree F α) (c : PUnit.{uFB + 1} → ITree F α)
      (head : shape' t = ⟨.step, c⟩) : LTSMove F α (some t)
  | event (t : ITree F α) (a : F.A) (c : F.B a → ITree F α)
      (head : shape' t = ⟨.query a, c⟩) (reply : F.B a) :
      LTSMove F α (some t)
  | ret (t : ITree F α) (result : α)
      (head : shape' t = ⟨.pure result, PEmpty.elim⟩) :
      LTSMove F α (some t)

namespace LTSMove

/-- State reached by one ITree LTS move. -/
def next : {state : Option (ITree F α)} → LTSMove F α state →
    Option (ITree F α)
  | _, .step _ c _ => some (c PUnit.unit)
  | _, .event _ _ c _ reply => some (c reply)
  | _, .ret _ _ _ => none

/-- Optional label of one ITree LTS move. -/
def label : {state : Option (ITree F α)} → LTSMove F α state →
    Option (Observation F α)
  | _, .step _ _ _ => none
  | _, .event _ a _ _ reply => some (.event a reply)
  | _, .ret _ result _ => some (.ret result)

end LTSMove

/-- The labelled transition system derived from an interaction tree.
Silent steps are labelled `none`; completed event/reply interactions and
terminal returns are visible observations. -/
def toLTS (F : PFunctor.{uFA, uFB}) (α : Type uα) :
    Control.LTS (Observation F α) where
  State := Option (ITree F α)
  Move := LTSMove F α
  next := fun _ move => move.next
  label := fun _ move => move.label

@[simp] theorem LTSMove.next_step (t : ITree F α)
    (c : PUnit.{uFB + 1} → ITree F α) (head : shape' t = ⟨.step, c⟩) :
    (@LTSMove.next F α _ (.step t c head)) = some (c PUnit.unit) := rfl

@[simp] theorem LTSMove.next_event (t : ITree F α) (a : F.A)
    (c : F.B a → ITree F α) (head : shape' t = ⟨.query a, c⟩)
    (reply : F.B a) :
    (@LTSMove.next F α _ (.event t a c head reply)) = some (c reply) := rfl

@[simp] theorem LTSMove.next_ret (t : ITree F α) (result : α)
    (head : shape' t = ⟨.pure result, PEmpty.elim⟩) :
    (@LTSMove.next F α _ (.ret t result head)) = none := rfl

@[simp] theorem LTSMove.label_step (t : ITree F α)
    (c : PUnit.{uFB + 1} → ITree F α) (head : shape' t = ⟨.step, c⟩) :
    (@LTSMove.label F α _ (.step t c head)) = none := rfl

@[simp] theorem LTSMove.label_event (t : ITree F α) (a : F.A)
    (c : F.B a → ITree F α) (head : shape' t = ⟨.query a, c⟩)
    (reply : F.B a) :
    (@LTSMove.label F α _ (.event t a c head reply)) =
      some (.event a reply) := rfl

@[simp] theorem LTSMove.label_ret (t : ITree F α) (result : α)
    (head : shape' t = ⟨.pure result, PEmpty.elim⟩) :
    (@LTSMove.label F α _ (.ret t result head)) = some (.ret result) := rfl

/-! ## Primitive transitions -/

theorem toLTS_silentStep_of_step {t : ITree F α}
    (c : PUnit.{uFB + 1} → ITree F α) (head : shape' t = ⟨.step, c⟩) :
    (toLTS F α).SilentStep (some t) (some (c PUnit.unit)) :=
  ⟨.step t c head, rfl, rfl⟩

theorem toLTS_visibleStep_of_query {t : ITree F α} (a : F.A)
    (c : F.B a → ITree F α) (head : shape' t = ⟨.query a, c⟩)
    (reply : F.B a) :
    (toLTS F α).VisibleStep (some t) (.event a reply) (some (c reply)) :=
  ⟨.event t a c head reply, rfl, rfl⟩

theorem toLTS_visibleStep_of_pure {t : ITree F α} (result : α)
    (head : shape' t = ⟨.pure result, PEmpty.elim⟩) :
    (toLTS F α).VisibleStep (some t) (.ret result) none :=
  ⟨.ret t result head, rfl, rfl⟩

@[simp] theorem toLTS_silentStep_step (t : ITree F α) :
    (toLTS F α).SilentStep (some (step t)) (some t) :=
  toLTS_silentStep_of_step (fun _ => t) (shape'_step t)

@[simp] theorem toLTS_visibleStep_query (a : F.A)
    (k : F.B a → ITree F α) (reply : F.B a) :
    (toLTS F α).VisibleStep (some (query a k)) (.event a reply)
      (some (k reply)) :=
  toLTS_visibleStep_of_query a k (shape'_query a k) reply

@[simp] theorem toLTS_visibleStep_pure (result : α) :
    (toLTS F α).VisibleStep (some (pure (F := F) result)) (.ret result) none :=
  toLTS_visibleStep_of_pure result (shape'_pure result)

/-- ITree τ-stripping embeds into silent closure of the derived LTS. -/
theorem TauSteps.toLTSSilentSteps {t t' : ITree F α} (steps : TauSteps t t') :
    (toLTS F α).SilentSteps (some t) (some t') := by
  induction steps with
  | refl t => exact .refl
  | step c head _ ih =>
      exact Control.LTS.SilentSteps.trans (toLTS F α)
        (toLTS_silentStep_of_step c head).silentSteps ih

/-! ## Weak bisimulation as LTS weak bisimulation -/

/-- Lift ITree weak bisimulation to optional LTS states. -/
def LTSRel : Option (ITree F α) → Option (ITree F α) → Prop
  | none, none => True
  | some t, some s => WeakBisim t s
  | _, _ => False

namespace LTSRel

theorem symm {left right : Option (ITree F α)}
    (h : LTSRel left right) : LTSRel right left := by
  cases left with
  | none =>
      cases right <;> simp_all [LTSRel]
  | some t =>
      cases right with
      | none => simp_all [LTSRel]
      | some s => exact WeakBisim.symm h

end LTSRel

/-- ITree weak bisimulation is a weak simulation on the derived LTS. -/
theorem weakBisim_isWeakSimulation :
    Control.IsWeakSimulation (toLTS F α) (toLTS F α) LTSRel := by
  intro left right hrel label target transition
  cases left with
  | none =>
      rcases transition with ⟨move, _, _⟩
      cases move
  | some t =>
      cases right with
      | none => simp_all [LTSRel]
      | some s =>
          change WeakBisim t s at hrel
          rcases transition with ⟨move, hlabel, hnext⟩
          cases move with
          | step _ c head =>
              subst label
              subst target
              have ht : t = step (c PUnit.unit) := by
                apply PFunctor.M.eq_of_dest_eq
                exact head.trans (shape'_step (c PUnit.unit)).symm
              rw [ht] at hrel
              have hcont : WeakBisim (c PUnit.unit) s :=
                (step_weakBisim (c PUnit.unit)).symm.trans hrel
              exact ⟨some s, .refl, hcont⟩
          | ret _ result head =>
              subst label
              subst target
              obtain ⟨t', s', ht', hs', matched⟩ := WeakBisim.dest hrel
              have ht'eq : t' = t := TauSteps.rigid_of_pure result head ht'
              subst t'
              cases matched with
              | pure observed htMatch hsMatch =>
                  have heq :
                      (⟨Shape.pure observed, PEmpty.elim⟩ :
                        (Poly F α).Obj (ITree F α)) =
                      ⟨Shape.pure result, PEmpty.elim⟩ :=
                    htMatch.symm.trans head
                  have hresult : observed = result :=
                    Shape.pure.inj (Sigma.mk.inj heq).1
                  subst observed
                  exact ⟨none,
                    ⟨some s', none, hs'.toLTSSilentSteps,
                      toLTS_visibleStep_of_pure result hsMatch, .refl⟩,
                    trivial⟩
              | query _ _ _ htMatch _ _ =>
                  exfalso
                  rw [head] at htMatch
                  cases htMatch
              | tau _ _ htMatch _ _ =>
                  exfalso
                  rw [head] at htMatch
                  cases htMatch
          | event _ a c head reply =>
              subst label
              subst target
              obtain ⟨t', s', ht', hs', matched⟩ := WeakBisim.dest hrel
              have ht'eq : t' = t := TauSteps.rigid_of_query a c head ht'
              subst t'
              cases matched with
              | pure _ htMatch _ =>
                  exfalso
                  rw [head] at htMatch
                  cases htMatch
              | query observed ct cs htMatch hsMatch hcont =>
                  have heq :
                      (⟨Shape.query observed, ct⟩ :
                        (Poly F α).Obj (ITree F α)) =
                      ⟨Shape.query a, c⟩ := htMatch.symm.trans head
                  have ha : observed = a :=
                    Shape.query.inj (Sigma.mk.inj heq).1
                  subst observed
                  have hc : ct = c := eq_of_heq (Sigma.mk.inj heq).2
                  subst ct
                  exact ⟨some (cs reply),
                    ⟨some s', some (cs reply), hs'.toLTSSilentSteps,
                      toLTS_visibleStep_of_query a cs hsMatch reply, .refl⟩,
                    hcont reply⟩
              | tau _ _ htMatch _ _ =>
                  exfalso
                  rw [head] at htMatch
                  cases htMatch

/-- The lifted relation is a weak bisimulation on the derived LTS. -/
theorem weakBisim_isLTSWeakBisimulation :
    Control.IsWeakBisimulation (toLTS F α) (toLTS F α) LTSRel where
  forward := weakBisim_isWeakSimulation
  backward := by
    intro left right hrel label target transition
    obtain ⟨matched, weakStep, hmatched⟩ :=
      weakBisim_isWeakSimulation (LTSRel.symm hrel) transition
    exact ⟨matched, weakStep, LTSRel.symm hmatched⟩

/-! ## Finite trace semantics -/

/-- Finite visible traces of an ITree, inherited from its derived LTS. -/
def traces (t : ITree F α) : Set (List (Observation F α)) :=
  (toLTS F α).traces (some t)

private theorem silentSteps_from_none
    {target : Option (ITree F α)}
    (steps : (toLTS F α).SilentSteps none target) : target = none := by
  induction steps with
  | refl => rfl
  | tail _ last ih =>
      subst ih
      rcases last with ⟨move, _, _⟩
      cases move

private theorem silentSteps_from_pure (result : α)
    {target : Option (ITree F α)}
    (steps : (toLTS F α).SilentSteps (some (pure result)) target) :
    target = some (pure result) := by
  induction steps with
  | refl => rfl
  | tail _ last ih =>
      subst ih
      rcases last with ⟨move, hlabel, _⟩
      cases move with
      | step _ _ head =>
          exfalso
          rw [shape'_pure] at head
          cases head
      | event _ _ _ _ _ => cases hlabel
      | ret _ _ _ => cases hlabel

private theorem visibleStep_from_pure (result : α)
    {observation : Observation F α} {target : Option (ITree F α)}
    (step : (toLTS F α).VisibleStep (some (pure result)) observation target) :
    observation = .ret result ∧ target = none := by
  rcases step with ⟨move, hlabel, hnext⟩
  cases move with
  | step _ _ _ => cases hlabel
  | event _ _ _ head _ =>
      exfalso
      rw [shape'_pure] at head
      cases head
  | ret _ observed head =>
      rw [shape'_pure] at head
      cases head
      exact ⟨(Option.some.inj hlabel).symm, hnext.symm⟩

private theorem weakTrace_from_none_aux
    {source : Option (ITree F α)}
    {observations : List (Observation F α)}
    {target : Option (ITree F α)}
    (hsource : source = none)
    (trace : (toLTS F α).WeakTrace source observations target) :
    observations = [] ∧ target = none := by
  exact Control.LTS.WeakTrace.rec
    (motive := fun initial obs final _ =>
      initial = none → obs = [] ∧ final = none)
    (fun s hs => ⟨rfl, hs⟩)
    (fun {s middle t} {obs observations}
        (head : (toLTS F α).WeakStep s (some obs) middle)
        (_ : (toLTS F α).WeakTrace middle observations t) _ hs => by
      subst s
      rcases head with ⟨before, after, hpre, hvis, _⟩
      have : before = none := silentSteps_from_none hpre
      subst before
      rcases hvis with ⟨move, _, _⟩
      cases move)
    trace hsource

private theorem weakTrace_from_none
    {observations : List (Observation F α)}
    {target : Option (ITree F α)}
    (trace : (toLTS F α).WeakTrace none observations target) :
    observations = [] ∧ target = none :=
  weakTrace_from_none_aux rfl trace

private theorem weakTrace_from_pure_aux (result : α)
    {source : Option (ITree F α)}
    {observations : List (Observation F α)}
    {target : Option (ITree F α)}
    (hsource : source = some (pure result))
    (trace : (toLTS F α).WeakTrace source observations target) :
    observations = [] ∨ observations = [.ret result] := by
  exact Control.LTS.WeakTrace.rec
    (motive := fun initial obs _ _ =>
      initial = some (pure result) →
        obs = [] ∨ obs = [.ret result])
    (fun _ _ => Or.inl rfl)
    (fun {s middle t} {obs observations}
        (head : (toLTS F α).WeakStep s (some obs) middle)
        (tail : (toLTS F α).WeakTrace middle observations t) _ hs => by
      subst s
      rcases head with ⟨before, after, hpre, hvis, hpost⟩
      have hbefore : before = some (pure (F := F) result) :=
        silentSteps_from_pure result hpre
      subst before
      obtain ⟨hobs, hafter⟩ := visibleStep_from_pure result hvis
      subst obs
      subst after
      have hmiddle : middle = none := silentSteps_from_none hpost
      subst middle
      obtain ⟨hrest, _⟩ := weakTrace_from_none tail
      subst observations
      exact Or.inr rfl)
    trace hsource

/-- Weakly bisimilar ITrees have exactly the same finite observations. -/
theorem traces_eq_of_weakBisim {t s : ITree F α} (h : WeakBisim t s) :
    traces t = traces s :=
  Control.IsWeakBisimulation.traces_eq weakBisim_isLTSWeakBisimulation h

@[simp] theorem traces_step (t : ITree F α) : traces (step t) = traces t :=
  traces_eq_of_weakBisim (step_weakBisim t)

@[simp] theorem nil_mem_traces (t : ITree F α) : [] ∈ traces t :=
  Control.LTS.nil_mem_traces (toLTS F α) (some t)

/-- A pure return contributes its terminal return observation. -/
theorem ret_mem_traces (result : α) :
    [.ret result] ∈ traces (pure (F := F) result) := by
  refine ⟨none, .cons ?_
    (Control.LTS.WeakTrace.nil (L := toLTS F α) none)⟩
  exact ((toLTS_visibleStep_pure result).delay).weak

/-- A completed event/reply interaction can be prepended to every trace of
the selected continuation. -/
theorem event_cons_mem_traces (a : F.A) (k : F.B a → ITree F α)
    (reply : F.B a) {observations : List (Observation F α)}
    (h : observations ∈ traces (k reply)) :
    .event a reply :: observations ∈ traces (query a k) := by
  obtain ⟨target, tail⟩ := h
  exact ⟨target,
    .cons ((toLTS_visibleStep_query a k reply).delay.weak) tail⟩

/-- Exact finite traces of a pure tree: either the empty prefix or its single
terminal-return observation. -/
@[simp] theorem mem_traces_pure_iff (result : α)
    (observations : List (Observation F α)) :
    observations ∈ traces (pure (F := F) result) ↔
      observations = [] ∨ observations = [.ret result] := by
  constructor
  · rintro ⟨target, trace⟩
    exact weakTrace_from_pure_aux result rfl trace
  · rintro (rfl | rfl)
    · exact nil_mem_traces _
    · exact ret_mem_traces result

end ITree
