/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Bisimulation

/-! # Finite visible traces of labelled transition systems

`Control.LTS.WeakTrace L s observations t` records a finite sequence of
visible observations from `s` to `t`. Each visible transition is a weak
transition, so arbitrary finite silent prefixes and suffixes are ignored.

This is the trace semantics naturally preserved by `IsWeakSimulation` and
`IsWeakBisimulation`. It deliberately lives over the existing `Control.LTS`
layer rather than introducing a second transition-system representation.
-/

@[expose] public section

universe uObs uState uMove uState₁ uMove₁ uState₂ uMove₂

namespace Control.LTS

variable {Obs : Type uObs} (L : Control.LTS.{uObs, uState, uMove} Obs)

/-- A finite sequence of visible observations connected by weak transitions. -/
inductive WeakTrace : L.State → List Obs → L.State → Prop where
  /-- The empty trace leaves the state unchanged. -/
  | nil (s : L.State) : WeakTrace s [] s
  /-- Prepend one weak visible transition. -/
  | cons {s middle t : L.State} {obs : Obs} {observations : List Obs}
      (head : L.WeakStep s (some obs) middle)
      (tail : WeakTrace middle observations t) :
      WeakTrace s (obs :: observations) t

namespace WeakTrace

/-- Concatenate two finite weak traces. -/
theorem append {s middle t : L.State} {xs ys : List Obs}
    (first : L.WeakTrace s xs middle) (second : L.WeakTrace middle ys t) :
    L.WeakTrace s (xs ++ ys) t := by
  induction first with
  | nil _ => exact second
  | cons head _ ih => exact .cons head (ih second)

end WeakTrace

/-- The set of finite visible traces beginning at `s`. -/
def traces (s : L.State) : Set (List Obs) :=
  { observations | ∃ t, L.WeakTrace s observations t }

@[simp] theorem nil_mem_traces (s : L.State) : [] ∈ L.traces s :=
  ⟨s, .nil s⟩

end Control.LTS

namespace Control

variable {Obs : Type uObs}

namespace IsWeakSimulation

/-- A weak simulation transports every finite visible trace while preserving
the relation at its endpoint. -/
theorem weakTrace
    {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {rel : L₁.State → L₂.State → Prop}
    (simulation : IsWeakSimulation L₁ L₂ rel)
    {s₁ t₁ : L₁.State} {s₂ : L₂.State} {observations : List Obs}
    (hrel : rel s₁ s₂) (trace : L₁.WeakTrace s₁ observations t₁) :
    ∃ t₂, L₂.WeakTrace s₂ observations t₂ ∧ rel t₁ t₂ := by
  induction trace generalizing s₂ with
  | nil s => exact ⟨s₂, .nil s₂, hrel⟩
  | cons head _ ih =>
      obtain ⟨middle₂, head₂, hmiddle⟩ :=
        simulation.weakStep hrel head
      obtain ⟨t₂, tail₂, ht⟩ := ih hmiddle
      exact ⟨t₂, .cons head₂ tail₂, ht⟩

/-- Weak simulation implies inclusion of finite visible trace sets. -/
theorem traces_subset
    {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {rel : L₁.State → L₂.State → Prop}
    (simulation : IsWeakSimulation L₁ L₂ rel)
    {s₁ : L₁.State} {s₂ : L₂.State} (hrel : rel s₁ s₂) :
    L₁.traces s₁ ⊆ L₂.traces s₂ := by
  rintro observations ⟨t₁, trace⟩
  obtain ⟨t₂, trace₂, _⟩ := simulation.weakTrace hrel trace
  exact ⟨t₂, trace₂⟩

end IsWeakSimulation

namespace IsWeakBisimulation

/-- Weakly bisimilar states have exactly the same finite visible traces. -/
theorem traces_eq
    {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {rel : L₁.State → L₂.State → Prop}
    (bisimulation : IsWeakBisimulation L₁ L₂ rel)
    {s₁ : L₁.State} {s₂ : L₂.State} (hrel : rel s₁ s₂) :
    L₁.traces s₁ = L₂.traces s₂ := by
  ext observations
  constructor
  · intro htrace
    exact IsWeakSimulation.traces_subset bisimulation.forward hrel htrace
  · intro htrace
    exact IsWeakSimulation.traces_subset bisimulation.backward hrel htrace

end IsWeakBisimulation

end Control
