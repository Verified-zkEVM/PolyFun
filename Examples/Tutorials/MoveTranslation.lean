/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Hint
public import PolyFun.PFunctor.Lens.Monomial

/-!
# Translating a move with a public hint

A hidden state determines the result of each move. A decoder receives a public hint about
that state and the name of a source move. It chooses a target move that preserves the
observation, or preserves every profitable deviation from the common opening observation.
-/

public section

namespace PolyFunExamples.Bargaining.Replay

open PFunctor

variable {T B C D O H : Type}

/-- The observation required of a translated move. -/
inductive Mode where
  /-- Preserve every strict payoff improvement over the opening. -/
  | gain
  /-- Reproduce the observation of every source move. -/
  | exact
  deriving DecidableEq, Repr

/-- Two move repertoires evaluated against a common opening in each hidden state. -/
structure Board (T B C O : Type) where
  /-- The observation at the opening in each state. -/
  opening : T → O
  /-- What each source move produces. -/
  source : T → B → O
  /-- What each target move produces. -/
  target : T → C → O
  /-- An available target move for constructing a total decoder. -/
  defaultMove : C

/-- In gain mode a move that reproduces the opening cannot yield a strict improvement. -/
@[expose] def Compatible (mode : Mode) (board : Board T B C O) (t : T) (b : B) (c : C) : Prop :=
  match mode with
  | .gain => board.source t b = board.opening t ∨ board.source t b = board.target t c
  | .exact => board.source t b = board.target t c

instance instDecidableCompatible [DecidableEq O] (mode : Mode) (board : Board T B C O)
    (t : T) (b : B) (c : C) : Decidable (Compatible mode board t b c) :=
  match mode with
  | .gain => inferInstanceAs (Decidable (_ ∨ _))
  | .exact => inferInstanceAs (Decidable (_ = _))

/-- A decoder sees only the hint and the source move. -/
@[expose] def Valid (mode : Mode) (board : Board T B C O) (h : T → H)
    (d : H → B → C) : Prop :=
  Handler.Hint.Valid (Compatible mode board) h d

private theorem test_gain (x s y : O) :
    (s = x ∨ s = y) ↔ (∀ u : O → Int, u x < u s → u x < u y) := by
  classical
  constructor
  · rintro (rfl | rfl) u hs
    · exact (lt_irrefl _ hs).elim
    · exact hs
  · intro tested
    by_cases hx : s = x
    · exact Or.inl hx
    right
    by_contra hy
    let u (o : O) : Int := if o = s then 1 else 0
    have hgain := tested u (by simp [u, Ne.symm hx])
    simp [u, Ne.symm hx, Ne.symm hy] at hgain

/-- A decoder preserves every profitable move exactly when it satisfies all integer payoff
tests, with the same payoff table applied to the source and target observations. -/
theorem valid_gain_iff (board : Board T B C O) (h : T → H) (d : H → B → C) :
    Valid .gain board h d ↔ ∀ t b (u : O → Int),
      u (board.opening t) < u (board.source t b) →
      u (board.opening t) < u (board.target t (d (h t) b)) := by
  simp only [Valid, Handler.Hint.Valid, Compatible, test_gain]

/-- Testing improvement in both directions for every payoff distinguishes every unequal
pair of observations. -/
theorem valid_exact_iff (board : Board T B C O) (h : T → H) (d : H → B → C) :
    Valid .exact board h d ↔ ∀ t b (u : O → Int),
      (u (board.opening t) < u (board.source t b) ↔
       u (board.opening t) < u (board.target t (d (h t) b))) := by
  constructor
  · intro hv t b u
    rw [show board.source t b = board.target t (d (h t) b) from hv t b]
  · intro ht t b
    have left := (test_gain _ _ _).2 fun u => (ht t b u).1
    have right := (test_gain _ _ _).2 fun u => (ht t b u).2
    rcases left with hs | hs
    · exact right.elim (fun hy => hs.trans hy.symm) Eq.symm
    · exact hs

/-- Each decoder is the backward map of a monomial lens with identity on hints. -/
def decoderLens (d : H → B → C) : Lens (H y^ C) (H y^ B) :=
  Lens.ofMonomial id d

/-- The first decoder translates a source move to an intermediate move, which the second
decoder translates using the same hint. -/
theorem decoderLens_comp (d : H → B → C) (e : H → C → D) :
    decoderLens d ∘ₗ decoderLens e = decoderLens (fun s b => e s (d s b)) := by
  simp only [decoderLens, Lens.ofMonomial_comp, id_eq]
  rfl

/-- Reusing a move with the same observation satisfies either contract. -/
theorem valid_id (mode : Mode) (x : T → O) (f : T → B → O) (b₀ : B) (h : T → H) :
    Valid mode ⟨x, f, f, b₀⟩ h (fun _ b => b) := by
  cases mode <;> simp [Valid, Handler.Hint.Valid, Compatible]

/-- Two valid decoders compose when they share a hint, an opening, and the intermediate
move observations. -/
theorem valid_comp {mode : Mode} {x : T → O} {f : T → B → O} {g : T → C → O}
    {k : T → D → O} {c₀ : C} {d₀ : D} {h : T → H} {d : H → B → C} {e : H → C → D}
    (hd : Valid mode ⟨x, f, g, c₀⟩ h d) (he : Valid mode ⟨x, g, k, d₀⟩ h e) :
    Valid mode ⟨x, f, k, d₀⟩ h (fun s b => e s (d s b)) := by
  intro t b
  cases mode with
  | exact => exact (hd t b).trans (he t (d (h t) b))
  | gain =>
    rcases hd t b with hbase | hmid
    · exact Or.inl hbase
    · exact (he t (d (h t) b)).imp hmid.trans hmid.trans

/-- For one hint and source move, every candidate target move fails in a state giving that
same public hint. The refuting state may depend on the candidate. -/
structure Obstruction (mode : Mode) (board : Board T B C O) (h : T → H) where
  /-- A representative state exhibiting the hint. -/
  hintState : T
  /-- The source move that cannot be translated. -/
  move : B
  /-- A refuting hidden state for each candidate target move. -/
  refute : C → T
  /-- Each refutation concerns the represented hint. -/
  hint_eq : ∀ c, h (refute c) = h hintState
  /-- The indicated candidate fails at its refuting state. -/
  incompatible : ∀ c, ¬ Compatible mode board (refute c) move c

/-- An obstruction refutes every decoder that receives this hint. -/
theorem Obstruction.not_valid {mode : Mode} {board : Board T B C O} {h : T → H}
    (o : Obstruction mode board h) (d : H → B → C) : ¬ Valid mode board h d := by
  intro hv
  let c := d (h o.hintState) o.move
  apply o.incompatible c
  simpa only [o.hint_eq] using hv (o.refute c) o.move

/-- Certified result of searching for a decoder with the supplied public hint. -/
inductive SearchResult (mode : Mode) (board : Board T B C O) (h : T → H) where
  /-- A valid total decoder, including its values on unused hints. -/
  | success (decode : H → B → C) (valid : Valid mode board h decode)
  /-- A source move for which every target choice has a refuting state. -/
  | failure (obstruction : Obstruction mode board h)

section Search

variable [DecidableEq H] [DecidableEq O]
variable (mode : Mode) (board : Board T B C O) (h : T → H)
variable (states : List T) (targets : List C)

/-- Find a state in the hint fiber that rejects this candidate move. -/
@[expose] def counterexample (s : H) (b : B) (c : C) : Option T :=
  states.find? fun t => decide (h t = s ∧ ¬ Compatible mode board t b c)

/-- First target move compatible in every listed state with this hint. -/
@[expose] def candidate (s : H) (b : B) : Option C :=
  targets.find? fun c => (counterexample mode board h states s b c).isNone

/-- A candidate from a complete state search works throughout its hint fiber. -/
theorem sound_candidate (allStates : ∀ t, t ∈ states) {s : H} {b : B} {c : C}
    (found : candidate mode board h states targets s b = some c)
    (t : T) (ht : h t = s) : Compatible mode board t b c := by
  have ok := List.find?_some found
  have hn : counterexample mode board h states s b c = none := by simpa using ok
  have excludes := List.find?_eq_none.mp hn t (allStates t)
  simpa [ht] using excludes

/-- A failed candidate search identifies a refuting state for each target move. -/
@[expose] def obstructionOfNone (allTargets : ∀ c, c ∈ targets) (t : T) (b : B)
    (hn : candidate mode board h states targets (h t) b = none) : Obstruction mode board h := by
  have found (c : C) : (counterexample mode board h states (h t) b c).isSome := by
    have hc := List.find?_eq_none.mp hn c (allTargets c)
    simpa only [Option.isSome_iff_ne_none] using (by simpa using hc :
      counterexample mode board h states (h t) b c ≠ none)
  let refute (c : C) := (counterexample mode board h states (h t) b c).get (found c)
  have bad (c : C) : h (refute c) = h t ∧ ¬ Compatible mode board (refute c) b c := by
    have hs : counterexample mode board h states (h t) b c = some (refute c) :=
      (Option.some_get (found c)).symm
    have hb := List.find?_some hs
    exact of_decide_eq_true hb
  exact ⟨t, b, refute, fun c => (bad c).1, fun c => (bad c).2⟩

/-- Search reachable hint/move pairs in the supplied order. Each cell tests target moves
against every state in its hint fiber. Completeness of the three lists certifies either the
returned decoder or the obstruction to every possible decoder. -/
@[expose] def search (mode : Mode) (board : Board T B C O) (h : T → H)
    (states : List T) (moves : List B) (targets : List C)
    (allStates : ∀ t, t ∈ states) (allMoves : ∀ b, b ∈ moves)
    (allTargets : ∀ c, c ∈ targets) :
    SearchResult mode board h :=
  let pairs := states.flatMap fun t => moves.map fun b => (t, b)
  let lookup := candidate mode board h states targets
  match failed : pairs.find? (fun (t, b) => (lookup (h t) b).isNone) with
  | some (t, b) => .failure <|
      obstructionOfNone mode board h states targets allTargets t b (by
        have hs := List.find?_some failed
        simpa using hs)
  | none => .success (fun s b => (lookup s b).getD board.defaultMove) (by
      intro t b
      have hmem : (t, b) ∈ pairs := by
        exact List.mem_flatMap.mpr ⟨t, allStates t, List.mem_map.mpr ⟨b, allMoves b, rfl⟩⟩
      have ok := List.find?_eq_none.mp failed (t, b) hmem
      cases found : lookup (h t) b with
      | none => simp [found] at ok
      | some c =>
        simpa only [found, Option.getD_some] using
          sound_candidate mode board h states targets allStates found t rfl)

end Search

end PolyFunExamples.Bargaining.Replay
