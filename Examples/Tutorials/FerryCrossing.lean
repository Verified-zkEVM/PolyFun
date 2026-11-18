/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.MinimumHint

/-!
# Which channel should the captain take?

The captain can wait or ask a ferryman to cross. The target harbor requires an explicit channel.
The public signal tells the captain enough about the tide to choose a working channel. The
examples compute the number of distinct signals required and replay the directions they encode.
-/

public section

namespace PolyFunExamples.Bargaining.Ferry

open Replay

/-- Move zero waits. The source ferryman always crosses on request; each target channel has
its own navigability table. A visible `true` means that the captain crossed. -/
@[expose] def channels {n m : Nat} (openAt : Fin n → Fin m → Bool) :
    Board (Fin n) (Fin 2) (Fin (m + 1)) Bool where
  opening _ := false
  source _ b := b == 1
  target t := Fin.cases false (openAt t)
  defaultMove := 0

/-- East is open at low tide and west is open at high tide. -/
@[expose] def twoTides : Board (Fin 2) (Fin 2) (Fin 3) Bool :=
  channels fun t c => t == c

/-- Each of the three channels is closed at its own tide. -/
@[expose] def closedOnce : Board (Fin 3) (Fin 2) (Fin 4) Bool :=
  channels fun t c => t != c

/-- Each of the three channels is open only at its own tide. -/
@[expose] def openOnce : Board (Fin 3) (Fin 2) (Fin 4) Bool :=
  channels fun t c => t == c

/-- The source can wait, always cross, or cross only at low tide. The target can wait or
always cross. For gain preservation it may always cross on the conditional request. -/
@[expose] def conditional : Board (Fin 2) (Fin 3) (Fin 2) Bool where
  opening _ := false
  source t b := b == 1 || (b == 2 && t == 0)
  target _ c := c == 1
  defaultMove := 0

/-- The source can cross, while all target channels are closed. -/
@[expose] def stranded : Board (Fin 1) (Fin 2) (Fin 2) Bool :=
  channels fun _ _ => false

/-- Both the gain-preserving optimum and the exact-replay optimum, in that order. -/
@[expose] def sizes {T B C O : Type} [FinEnum T] [FinEnum B] [FinEnum C] [DecidableEq O]
    (board : Board T B C O) : Option Nat × Option Nat :=
  ((minimumHint .gain board).size?, (minimumHint .exact board).size?)

/-- At a fixed tide both harbors offer exactly the same visible outcomes. -/
theorem twoTides_same_outcomes (t : Fin 2) (o : Bool) :
    (∃ b, twoTides.source t b = o) ↔ (∃ c, twoTides.target t c = o) := by
  decide +revert

/-- Every payoff gives the same verdict on whether the captain can improve at either harbor. -/
theorem twoTides_can_improve_iff (t : Fin 2) (u : Bool → Int) :
    (∃ b, u (twoTides.opening t) < u (twoTides.source t b)) ↔
      ∃ c, u (twoTides.opening t) < u (twoTides.target t c) := by
  constructor
  · rintro ⟨b, gain⟩
    obtain ⟨c, eq⟩ := (twoTides_same_outcomes t _).1 ⟨b, rfl⟩
    exact ⟨c, eq ▸ gain⟩
  · rintro ⟨c, gain⟩
    obtain ⟨b, eq⟩ := (twoTides_same_outcomes t _).2 ⟨c, rfl⟩
    exact ⟨b, eq ▸ gain⟩

/-- A tide signal needs two values to route the captain east or west. -/
theorem sizes_twoTides : sizes twoTides = (some 2, some 2) := by decide

/-- For any two tides there is a channel open at both. -/
theorem pair_has_channel (s t : Fin 3) :
    ∃ c : Fin 4, closedOnce.target s c = true ∧ closedOnce.target t c = true := by
  decide +revert

/-- Although every pair shares a channel, a single signal fails across all three tides. -/
theorem sizes_closedOnce : sizes closedOnce = (some 2, some 2) := by decide

/-- When each channel works at just one tide, the signal must distinguish all three. -/
theorem sizes_openOnce : sizes openOnce = (some 3, some 3) := by decide

/-- Replaying an unprofitable move exactly can require an additional signal value. -/
theorem sizes_conditional : sizes conditional = (some 1, some 2) := by decide

/-- Even a signal that reveals the tide cannot open a closed channel. -/
theorem sizes_stranded : sizes stranded = (none, none) := by decide

private def tide (t : Fin 2) := if t == 0 then "low" else "high"

private def action (b : Fin 2) := if b == 0 then "wait" else "cross"

private def channel (c : Fin 3) :=
  if c == 0 then "wait" else if c == 1 then "east" else "west"

/-- Read the synthesized hint and crossing instruction at each tide. -/
def directions : List String :=
  match minimumHint .gain twoTides with
  | .optimal _ h d .. => (List.finRange 2).map fun t =>
      s!"{tide t} tide, signal {(h t).val}: take {channel (d (h t) 1)}"
  | .impossible t b _ => [s!"{action b} cannot be translated at {tide t} tide"]

/-- Try to translate without revealing the tide and replay each failed candidate. -/
def withoutHint : List String :=
  match MinimumHint.searchHints .gain twoTides (fun _ => ()) with
  | .success d _ => [s!"cross: take {channel (d () 1)}"]
  | .failure o => (List.finRange 3).map fun c =>
      s!"{action o.move}: {channel c} fails at {tide (o.refute c)} tide"

end PolyFunExamples.Bargaining.Ferry
