/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Monomial
import Mathlib.Logic.Function.Basic

/-!
# Can a pirate’s bluff be erased?

A proposer chooses an offer `a` and a responder chooses a legal reply in `p.B a`.
The responder's pure strategy specifies a reply to every possible offer. The observation of
the two moves determines both players' payoffs. The four-coin game and the hidden-offer
example compare equilibrium verdicts with the moves that witness a profitable deviation.
-/

public section

namespace PolyFunExamples.Bargaining

open PFunctor

variable (p : PFunctor.{0, 0}) {O : Type} (obs : (b : p.A) → p.B b → O)
  (pay : O → Int × Int)

/-- Neither player can gain by replacing their own strategy while the other player's
strategy stays fixed. The responder may replace their entire contingent policy. -/
def Nash (a : p.A) (r : (b : p.A) → p.B b) : Prop :=
  (∀ b, (pay (obs b (r b))).1 ≤ (pay (obs a (r a))).1) ∧
  (∀ s : (b : p.A) → p.B b, (pay (obs a (s a))).2 ≤ (pay (obs a (r a))).2)

/-- The proposer checks every offer. A responder can realize any legal reply to the
current offer by changing their policy there. -/
theorem nash_iff_local (a : p.A) (r : (b : p.A) → p.B b) :
    Nash p obs pay a r ↔
      (∀ b, (pay (obs b (r b))).1 ≤ (pay (obs a (r a))).1) ∧
      (∀ x : p.B a, (pay (obs a x)).2 ≤ (pay (obs a (r a))).2) := by
  classical
  constructor
  · rintro ⟨offers, policies⟩
    refine ⟨offers, fun x => ?_⟩
    simpa only [Function.update_self] using policies (Function.update r a x)
  · rintro ⟨offers, replies⟩
    exact ⟨offers, fun s => replies (s a)⟩

/-- A fixed responder sends an offer forward to the public observation and sends the
proposer's share of its payoff back to the offer. -/
def responderLens (r : (b : p.A) → p.B b) : Lens (p.A y^ Int) (O y^ (Int × Int)) :=
  Lens.ofMonomial (fun b => obs b (r b)) (fun _ u => u.1)

/-- Close the responder lens with a table of terminal payoffs. Its backward signal gives
the proposer a utility at each offer, including offers the proposer did not choose. -/
def offerUtility (r : (b : p.A) → p.B b) (b : p.A) : Int :=
  let terminal : Lens (O y^ (Int × Int)) (Unit y^ Unit) :=
    Lens.ofMonomial (fun _ => ()) (fun o _ => pay o)
  (terminal ∘ₗ responderLens p obs r).toFunB b ()

/-- Pulling the payoff table back through the fixed responder evaluates its policy at
the offer being considered. -/
@[simp] theorem offerUtility_eq (r : (b : p.A) → p.B b) (b : p.A) :
    offerUtility p obs pay r b = (pay (obs b (r b))).1 := by
  simp only [offerUtility, responderLens, Lens.ofMonomial_comp, Lens.ofMonomial_toFunB]

/-- Local optimality for the proposer in the pulled-back payoff context and for the
responder at the chosen offer is equivalent to Nash equilibrium of the whole game. -/
theorem nash_iff_wired (a : p.A) (r : (b : p.A) → p.B b) :
    Nash p obs pay a r ↔
      (∀ b, offerUtility p obs pay r b ≤ offerUtility p obs pay r a) ∧
      (∀ x : p.B a, (pay (obs a x)).2 ≤ (pay (obs a (r a))).2) := by
  simpa only [offerUtility_eq] using nash_iff_local p obs pay a r

end PolyFunExamples.Bargaining

/-! ## Which observations determine equilibrium? -/

namespace PolyFunExamples.Bargaining

variable {O : Type} (p : PFunctor.{0, 0}) (obs : (a : p.A) → p.B a → O)

/-- All observations the captain can reach by changing the offer while the mate keeps strategy
`r`. -/
def captainObservations (r : (a : p.A) → p.B a) : Set O :=
  Set.range fun b => obs b (r b)

/-- An observation is reachable if some offer produces it under the given strategy. -/
@[simp] theorem mem_captainObservations (r : (a : p.A) → p.B a) (o : O) :
    o ∈ captainObservations p obs r ↔ ∃ b, obs b (r b) = o := Iff.rfl

/-- The captain wins one coin exactly on observation `target`. The mate is indifferent. -/
@[expose] def rewardObservation [DecidableEq O] (target : O) (o : O) : Int × Int :=
  (if o = target then 1 else 0, 0)

/-- Suppose the chosen offer gives the same observation under both strategies. Paying for an
observation available only under `r` then gives the captain a profitable deviation there and
makes the profile using `s` an equilibrium. -/
theorem separates_of_mem_notMem [DecidableEq O] (a : p.A) (r s : (b : p.A) → p.B b)
    (h : obs a (r a) = obs a (s a)) (o : O) (hr : o ∈ captainObservations p obs r)
    (hs : o ∉ captainObservations p obs s) :
    Nash p obs (rewardObservation o) a s ∧ ¬ Nash p obs (rewardObservation o) a r := by
  have hmiss (b : p.A) : obs b (s b) ≠ o := fun he => hs ⟨b, he⟩
  obtain ⟨b, hb⟩ := hr
  constructor
  · apply (nash_iff_local _ _ _ _ _).2
    exact ⟨fun c => by simp [rewardObservation, hmiss], fun _ => le_rfl⟩
  · intro hn
    have hc := ((nash_iff_local _ _ _ _ _).1 hn).1 b
    simp [rewardObservation, hb, h, hmiss] at hc

/-- If the offer actually made gives the same observation under both strategies, they agree on
Nash equilibrium for all observable payoffs exactly when the captain can reach the same
observations. The two replies at that offer may differ. -/
theorem nash_all_payoffs_iff_captainObservations_eq (a : p.A) (r s : (b : p.A) → p.B b)
    (h : obs a (r a) = obs a (s a)) :
    (∀ pay : O → Int × Int, Nash p obs pay a r ↔ Nash p obs pay a s) ↔
      captainObservations p obs r = captainObservations p obs s := by
  constructor
  · classical
    intro agree
    ext o
    constructor
    · intro hr
      by_contra hs
      obtain ⟨yes, no⟩ := separates_of_mem_notMem p obs a r s h o hr hs
      exact no ((agree _).2 yes)
    · intro hs
      by_contra hr
      obtain ⟨yes, no⟩ := separates_of_mem_notMem p obs a s r h.symm o hs hr
      exact no ((agree _).1 yes)
  · intro he pay
    have upper (t : (b : p.A) → p.B b) (v : Int) :
        (∀ b, (pay (obs b (t b))).1 ≤ v) ↔
          (∀ o ∈ captainObservations p obs t, (pay o).1 ≤ v) := by
      constructor
      · rintro hc _ ⟨b, rfl⟩
        exact hc b
      · intro hc b
        exact hc _ ⟨b, rfl⟩
    simp only [nash_iff_local, upper, he, h]

/-- For strategies that give the same reply to the chosen offer, observing the offer and reply
makes every off-path difference between the strategies visible to some payoff. -/
theorem nash_all_full_payoffs_iff (a : p.A) (r s : (b : p.A) → p.B b) (h : r a = s a) :
    (∀ pay : ((b : p.A) × p.B b) → Int × Int,
      Nash p (fun b x => ⟨b, x⟩) pay a r ↔ Nash p (fun b x => ⟨b, x⟩) pay a s) ↔
      ∀ b, r b = s b := by
  rw [nash_all_payoffs_iff_captainObservations_eq _ _ _ _ _ (congrArg (Sigma.mk a) h)]
  constructor
  · intro he b
    have hm : Sigma.mk b (r b) ∈
        captainObservations p (fun c x => Sigma.mk c x) r := ⟨b, rfl⟩
    rw [he] at hm
    obtain ⟨c, hc⟩ := hm
    obtain ⟨eq, heq⟩ := Sigma.mk.inj hc
    subst c
    exact (eq_of_heq heq).symm
  · intro same
    rw [funext same]

end PolyFunExamples.Bargaining

/-! ## Finding a profitable deviation -/

namespace PolyFunExamples.Bargaining

/-- A proposed unilateral change, with the player's payoff before and after the change. -/
inductive Deviation (p : PFunctor.{0, 0}) (a : p.A) where
  | offer (newOffer : p.A) (before after : Int)
  | reply (newReply : p.B a) (before after : Int)

variable (p : PFunctor.{0, 0}) {O : Type}
    (obs : (a : p.A) → p.B a → O) (pay : O → Int × Int)
    (a : p.A) (r : (b : p.A) → p.B b)

/-- Replaying the move gives the recorded payoffs and a strict gain for its player. -/
def Deviation.Valid : Deviation p a → Prop
  | .offer b before after =>
    before = (pay (obs a (r a))).1 ∧ after = (pay (obs b (r b))).1 ∧ before < after
  | .reply x before after =>
    before = (pay (obs a (r a))).2 ∧ after = (pay (obs a x)).2 ∧ before < after

/-- Search the offers in order, then the replies at the reached offer. -/
@[expose] def findDeviation (offers : List p.A) (replies : List (p.B a)) :
    Option (Deviation p a) :=
  let current := pay (obs a (r a))
  let propose b := (pay (obs b (r b))).1
  let respond x := (pay (obs a x)).2
  ((offers.find? fun b => decide (current.1 < propose b)).map
    fun b => .offer b current.1 (propose b)) <|>
  ((replies.find? fun x => decide (current.2 < respond x)).map
    fun x => .reply x current.2 (respond x))

variable (offers : List p.A) (replies : List (p.B a))

/-- Every reported deviation gives a strict gain when replayed, even with partial move lists. -/
theorem valid_of_findDeviation_eq_some {d : Deviation p a}
    (h : findDeviation p obs pay a r offers replies = some d) :
    Deviation.Valid p obs pay a r d := by
  simp only [findDeviation, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.or_eq_some_iff, Option.map_eq_some_iff] at h
  rcases h with ⟨b, found, rfl⟩ | ⟨_, x, found, rfl⟩
  · have improves := List.find?_some found
    exact ⟨rfl, rfl, of_decide_eq_true improves⟩
  · have improves := List.find?_some found
    exact ⟨rfl, rfl, of_decide_eq_true improves⟩

/-- With complete offer and reply lists, the search returns no witness exactly at a Nash profile. -/
theorem findDeviation_eq_none_iff (hOffers : ∀ b, b ∈ offers)
    (hReplies : ∀ x, x ∈ replies) :
    findDeviation p obs pay a r offers replies = none ↔ Nash p obs pay a r := by
  rw [nash_iff_local p obs pay a r]
  simp [findDeviation, hOffers, hReplies]

end PolyFunExamples.Bargaining

/-! ## Splitting four coins -/

namespace PolyFunExamples.Bargaining.FourCoins

/-- The captain offers the mate one coin or two coins out of four. -/
inductive Offer where
  | one | two
  deriving DecidableEq

/-- A response table lists what the mate would do after each offer. -/
structure Policy where
  /-- Whether the mate accepts one coin. -/
  acceptOne : Bool
  /-- Whether the mate accepts two coins. -/
  acceptTwo : Bool
  deriving DecidableEq

private def offers : List Offer := [.one, .two]
private def answers : List Bool := [false, true]

/-- Rejection pays zero to both pirates. Acceptance pays the proposed split. -/
def coins : Offer × Bool → Int × Int
  | (_, false) => (0, 0)
  | (.one, true) => (3, 1)
  | (.two, true) => (2, 2)

/-- A reply is legal after either offer. The captain and mate both see the offer and reply. -/
abbrev board : PFunctor.{0, 0} := ⟨Offer, fun _ => Bool⟩

/-- Read the response at the offer the captain is considering. -/
def Policy.reply (r : Policy) : Offer → Bool
  | .one => r.acceptOne
  | .two => r.acceptTwo

private def policies : List Policy :=
  answers.flatMap fun one => answers.map fun two => ⟨one, two⟩

/-- All eight choices of opening offer and contingent response table. -/
def profiles : List (Offer × Policy) :=
  offers.flatMap fun a => policies.map fun r => (a, r)

private theorem mem_offers (a : Offer) : a ∈ offers := by cases a <;> decide
private theorem mem_answers (x : Bool) : x ∈ answers := by cases x <;> decide

/-- Search the captain's alternative offers, then the mate's alternative answers. -/
def check (a : Offer) (r : Policy) : Option (Deviation board a) :=
  findDeviation board Prod.mk coins a r.reply offers answers

/-- An independent normal-form check tries all four replacement response tables. -/
def flatCheck (a : Offer) (r : Policy) : Bool :=
  let here := coins (a, r.reply a)
  offers.all (fun b => decide ((coins (b, r.reply b)).1 ≤ here.1)) &&
    policies.all (fun s => decide ((coins (a, s.reply a)).2 ≤ here.2))

/-- A root equilibrium is subgame-perfect if the mate also acts optimally after every offer. -/
def subgamePerfect (a : Offer) (r : Policy) : Bool :=
  (check a r).isNone && offers.all fun b =>
    answers.all fun x => decide ((coins (b, x)).2 ≤ (coins (b, r.reply b)).2)

/-- The independent normal-form search and the deviation checker agree on every profile. -/
theorem flatCheck_eq_isNone (a : Offer) (r : Policy) :
    flatCheck a r = (check a r).isNone := by
  obtain ⟨one, two⟩ := r
  cases a <;> cases one <;> cases two <;> decide

/-- The finite search covers every legal move in this game. -/
theorem check_eq_none_iff (a : Offer) (r : Policy) :
    check a r = none ↔ Nash board Prod.mk coins a r.reply :=
  findDeviation_eq_none_iff board Prod.mk coins a r.reply offers answers mem_offers mem_answers

/-- Every strategy profile is represented and no profile occurs twice. -/
theorem profiles_complete : (∀ a r, (a, r) ∈ profiles) ∧ profiles.Nodup := by
  constructor
  · rintro a ⟨one, two⟩
    cases a <;> cases one <;> cases two <;> decide
  · decide

/-- The two equilibria offering one coin differ only on the unused two-coin offer. -/
theorem nash_profiles :
    profiles.filter (fun (a, r) => (check a r).isNone) =
      [(.one, ⟨true, false⟩), (.one, ⟨true, true⟩), (.two, ⟨false, true⟩)] := by decide

/-- Accepting both offers makes offering one coin the unique subgame-perfect profile. -/
theorem subgamePerfect_profiles :
    profiles.filter (fun (a, r) => subgamePerfect a r) = [(.one, ⟨true, true⟩)] := by decide

/-- When only the fair offer would be accepted, the captain has no profitable deviation. -/
example : check .two ⟨false, true⟩ = none := rfl

/-- Accepting both offers gives the captain a one-coin gain for switching to the smaller offer. -/
example : check .two ⟨true, true⟩ = some (.offer .one 2 3) := rfl

/-- With both offers rejected, the mate can gain one coin by changing the reached reply. -/
example : check .one ⟨false, false⟩ = some (.reply true 0 1) := rfl

/-- One row for each profile, with a replayable deviation or the equilibrium verdict. -/
def report : List String := profiles.map fun (a, r) =>
  let amount : Offer → String := fun | .one => "1" | .two => "2"
  let action : Bool → String := fun x => if x then "accept" else "reject"
  let result := match check a r with
    | none => if subgamePerfect a r then "subgame-perfect Nash" else "Nash"
    | some (.offer b old new) => s!"captain switches to {amount b}, {old} to {new}"
    | some (.reply x old new) => s!"mate chooses {action x}, {old} to {new}"
  s!"offer {amount a}, replies ({action r.acceptOne}, {action r.acceptTwo}): {result}"

end PolyFunExamples.Bargaining.FourCoins

/-! ## Hiding the offer -/

namespace PolyFunExamples.Bargaining.HiddenOffers

/-- An offer gives the mate one, two, or three coins. -/
inductive Offer where | one | two | three
  deriving DecidableEq, Repr

/-- Each offer admits acceptance (`true`) or rejection (`false`). -/
@[expose] def moves : PFunctor.{0, 0} := ⟨Offer, fun _ => Bool⟩

/-- Publish the mate's answer to the payoff table. -/
@[expose] def observe (_ : Offer) (accept : Bool) := accept

/-- Reject exactly the offer of one coin. -/
@[expose] def rejectOne : Offer → Bool | .one => false | _ => true

/-- Reject exactly the offer of three coins. -/
@[expose] def rejectThree : Offer → Bool | .three => false | _ => true

/-- At two coins both profiles have the same equilibrium verdict under every observable payoff. -/
theorem nash_iff (pay : Bool → Int × Int) :
    Nash moves observe pay .two rejectOne ↔ Nash moves observe pay .two rejectThree := by
  apply (nash_all_payoffs_iff_captainObservations_eq moves observe .two
    rejectOne rejectThree rfl).2 _ pay
  apply Set.ext
  intro reply
  rw [mem_captainObservations moves observe rejectOne reply,
    mem_captainObservations moves observe rejectThree reply]
  cases reply
  · exact ⟨fun _ => ⟨.three, rfl⟩, fun _ => ⟨.one, rfl⟩⟩
  · exact ⟨fun _ => ⟨.two, rfl⟩, fun _ => ⟨.two, rfl⟩⟩

/-- Pay the captain a coin for rejection, then search both players' moves. -/
@[expose] def rejectionWitness (policy : Offer → Bool) : Option (Deviation moves .two) :=
  findDeviation moves observe (rewardObservation false) .two policy
    [.one, .two, .three] [false, true]

/-- The two policies give the captain different offers that gain one coin. -/
theorem rejectionWitness_pair :
    rejectionWitness rejectOne = some (.offer .one 0 1) ∧
    rejectionWitness rejectThree = some (.offer .three 0 1) := ⟨rfl, rfl⟩

end PolyFunExamples.Bargaining.HiddenOffers
