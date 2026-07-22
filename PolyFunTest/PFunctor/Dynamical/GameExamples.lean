/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Game
public import PolyFun.PFunctor.Lens.Composite

/-!
# Examples for responders, games, and two-phase games

Regression tests: the `game` / `closedGame` step equations and the
responder eta canaries hold by `rfl`, `stepWith` at `m := Id` is the closed
game's step, the query-conditioned `DynComputation` run law specializes to a
nontrivial responder with the answer/state pair in the intended order, a
concrete counting-responder game runs by `rfl`, the Moore win-bit game is the
`monomial Bool PUnit` instance of `game`, and a deterministic PrivK-shaped
`game₂` (challenger as a composite lens, adversary via `orderPair`) computes one
composite step by `rfl`.
-/

@[expose] public section

universe u v

namespace PFunctor

/-! ## Structural canaries -/

section Canaries

variable {S T : Type u} {q r : PFunctor.{u, u}}

/-- The game's exposed position is the committed challenger lens applied to the
adversary's position. -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) (s : S) (t : T) :
    (DynSystem.game chal adv).expose (s, t) = (chal.expose s).toFunA (adv.expose t) := rfl

/-- The game's update: the challenger hears the adversary's query with the outer
direction; the adversary hears the committed lens's pulled-back answer. -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) (s : S) (t : T)
    (d : r.B ((DynSystem.game chal adv).expose (s, t))) :
    (DynSystem.game chal adv).update (s, t) d
      = (chal.update s ⟨adv.expose t, d⟩,
          adv.update t ((chal.expose s).toFunB (adv.expose t) d)) := rfl

/-- The closed game steps by "adversary queries, responder answers". -/
example (R : Responder S q) (adv : DynSystem T q) (s : S) (t : T) :
    (DynSystem.closedGame R adv).step (s, t)
      = (R.next s (adv.expose t), adv.update t (R.answer s (adv.expose t))) := rfl

/-- The game former is the uncurried challenger (tensor–hom adjunction). -/
example (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    DynSystem.game chal adv
      = ((Lens.id (selfMonomial S) ⊗ₗ adv) ⨟ Lens.uncurry chal :
          Lens (selfMonomial S ⊗ selfMonomial T) r) := rfl

/-- Eta canary: a responder's raw lens update reads only the query component. -/
example (R : Responder S q) (s : S) (d : (q ⊸ X).B (DynSystem.expose R s)) :
    DynSystem.update R s d = R.next s d.1 := rfl

/-- Eta canaries: the Kleisli–Mealy round-trips are definitional. -/
example (R : Responder S q) : Responder.ofStateHandler R.toStateHandler = R := rfl

example (h : Handler (StateT S Id) q) :
    Responder.toStateHandler (Responder.ofStateHandler h) = h := rfl

example (R : Responder S q) :
    Responder.equivStateHandler.symm (Responder.equivStateHandler R) = R := rfl

/-- `stepWith` against a responder's stateful handler, at `m := Id`, is the
closed game's step. -/
example (R : Responder T q) (A : DynSystem S q) (p : T × S) :
    DynSystem.stepWith (m := Id) R.toStateHandler A p
      = (DynSystem.closedGame R A).step p := rfl

end Canaries

/-! ## Returning computations against responders -/

/-- One visible `true` query whose answer becomes the terminal result. -/
def responderQueryComputation :
    DynSystem.DynComputation (monomial Bool Nat) PUnit Nat where
  State := Option Nat
  toDynSystem :=
    (fun
      | none => Sum.inr true
      | some value => Sum.inl value) ⇆
    fun
      | none => fun answer => some answer
      | some _ => PEmpty.elim
  init := fun _ => none

/-- On the exposed `true` query, answer with `state + 10` and advance the
responder state by one. The two components are deliberately distinguishable. -/
def answerAndAdvanceResponder : Responder Nat (monomial Bool Nat) :=
  Responder.mk' (fun state query => Bool.rec (state + 20) (state + 10) query)
    (fun state query => Bool.rec (state + 2) (state + 1) query)

@[simp] theorem answerAndAdvanceResponder_answer_true (state : Nat) :
    answerAndAdvanceResponder.answer state true = state + 10 := rfl

@[simp] theorem answerAndAdvanceResponder_next_true (state : Nat) :
    answerAndAdvanceResponder.next state true = state + 1 := rfl

def answerAndAdvanceHandler :
    Handler (StateT Nat (Id.{0})) (monomial Bool Nat) :=
  answerAndAdvanceResponder.toStateHandler

def responderQueryRun (fuel : Nat) (state : Option Nat) :
    StateT Nat (Id.{0}) (Option Nat) :=
  responderQueryComputation.{0}.runWith answerAndAdvanceHandler fuel state

/-- The query-branch run law exposed through `Game` selects the computation's
answer-indexed continuation and threads the responder's next state. Writing the
right-hand side explicitly makes an answer/state swap fail this canary. -/
example (fuel responderState : Nat) :
    (responderQueryRun (fuel + 1) none).run responderState =
      (responderQueryRun fuel (some (responderState + 10))).run
        (responderState + 1) := by
  unfold responderQueryRun
  rw [responderQueryComputation.runWith_query_succ_stateT
    answerAndAdvanceHandler fuel none true
    (fun answer => some answer) rfl responderState]
  rw [show answerAndAdvanceHandler true responderState =
    (responderState + 10, responderState + 1) by rfl]
  change (responderQueryComputation.runWith answerAndAdvanceHandler fuel
    (some (responderState + 10))).run (responderState + 1) = _
  rfl

/-! ## A concrete closed game: counting responder vs doubling adversary -/

/-- The counting responder over `ℕ X^ ℕ`: answers every query with its running
count and increments it. -/
def countingResponder : Responder ℕ (monomial ℕ ℕ) :=
  Responder.mk' (fun s _ => s) (fun s _ => s + 1)

/-- The doubling adversary over `ℕ X^ ℕ`: queries its state, stores double the
answer it hears. -/
def doublingAdversary : DynSystem ℕ (monomial ℕ ℕ) :=
  id ⇆ fun _ (a : ℕ) => 2 * a

/-- Three closed-game steps, computed by `rfl`:
`(0, 5) ↦ (1, 0) ↦ (2, 2) ↦ (3, 4)`. -/
example : (DynSystem.closedGame countingResponder doublingAdversary).iterate (0, 5) 3
    = (3, 4) := rfl

/-! ## The Moore win-bit game: `game` at `r := monomial Bool PUnit` -/

/-- A challenger with a Moore win bit: the adversary wins when its query matches
the secret; every answer leaks the secret, and the secret never changes. -/
def secretMatchChallenger : DynSystem ℕ (monomial ℕ ℕ ⊸ monomial Bool PUnit) :=
  (fun s => (fun (qy : ℕ) => qy == s) ⇆ fun _ _ => s) ⇆ fun s _ => s

/-- The win-bit game *is* a Moore machine: `game` at `r := monomial Bool PUnit`
lands in `MooreMachine (S × T) Bool PUnit`, no scored-game structure needed. -/
def secretMatchGame : MooreMachine (ℕ × ℕ) Bool PUnit :=
  DynSystem.game secretMatchChallenger doublingAdversary

example : secretMatchGame.output (3, 3) = true := rfl

example : secretMatchGame.output (3, 4) = false := rfl

/-- Close the Moore game with trivial feedback and step it: the challenger keeps
its secret, the adversary stores double the leaked secret. -/
example : (MooreMachine.feedback (fun _ => PUnit.unit) secretMatchGame).step (3, 3)
    = (3, 6) := rfl

/-! ## A deterministic PrivK-shaped two-phase game

Commit phase `(Bool × Bool) X^ Bool`: the adversary submits a message-bit pair
and hears the "ciphertext" `m_b`. Guess phase `Bool X^ PUnit`: the adversary
submits a guess and the outer interface `Bool X^ PUnit` exposes the win bit.
The challenger is written directly as the corresponding composite lens, and
the two single-phase adversaries are ordered by `orderPair` — so the guesser
cannot see the ciphertext within the composite step, as documented there. -/

/-- The PrivK challenger, from its destructor triple: state is the secret bit
`b`; commit phase answers `m_b`; guess phase exposes `guess == b`. -/
def privKChallenger :
    DynSystem Bool ((monomial (Bool × Bool) Bool ⊸ X.{0, 0})
      ◃ (monomial Bool PUnit ⊸ monomial Bool PUnit)) :=
  (fun b =>
    ⟨sectionLens (fun mm => cond b mm.2 mm.1),
      fun _ => (fun (guess : Bool) => guess == b) ⇆ (fun _ _ => PUnit.unit)⟩) ⇆
    fun b _ => b

/-- The commit-phase adversary: submits the fixed message pair `(false, true)`. -/
def commitAdversary : DynSystem PUnit (monomial (Bool × Bool) Bool) :=
  Lens.fromX (false, true)

/-- The guess-phase adversary: guesses its own (fixed) state bit. -/
def guessAdversary : DynSystem Bool (monomial Bool PUnit) :=
  id ⇆ fun t _ => t

/-- The full PrivK-shaped game: challenger against the ordered adversary pair. -/
def privKGame : DynSystem (Bool × (PUnit × Bool)) (X.{0, 0} ◃ monomial Bool PUnit) :=
  DynSystem.game₂ privKChallenger (DynSystem.orderPair commitAdversary guessAdversary)

/-- With secret `true` and message pair `(false, true)`, guessing `true` wins:
the composite position's continuation carries the win bit. -/
example : (privKGame.expose (true, (PUnit.unit, true))).2 PUnit.unit = true := rfl

/-- Guessing `false` against secret `true` loses. -/
example : (privKGame.expose (true, (PUnit.unit, false))).2 PUnit.unit = false := rfl

/-- One composite step of the game, by `rfl`: every participant here is
stationary, so the state is unchanged. -/
example : privKGame.update (true, (PUnit.unit, true)) ⟨PUnit.unit, PUnit.unit⟩
    = (true, (PUnit.unit, true)) := rfl

end PFunctor
