/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.PirateBargaining
public import Mathlib.Data.FinEnum

/-!
# Checking a game with finitely many moves

An enumeration fixes the order in which the checker tries deviations. Checking one profile
requires the offers and the replies at the chosen offer. In the entry game an incumbent can
share the market or start a price war only if a rival enters.
-/

public section

namespace PolyFunExamples.Bargaining

variable (p : PFunctor.{0, 0}) {O : Type} (obs : (b : p.A) → p.B b → O)
    (pay : O → Int × Int) (a : p.A) (r : (b : p.A) → p.B b)
    [FinEnum p.A] [FinEnum (p.B a)]

/-- Try the offers in enumeration order and then the legal replies to the chosen offer. -/
@[expose] def findDeviationEnum : Option (Deviation p a) :=
  findDeviation p obs pay a r (FinEnum.toList p.A) (FinEnum.toList (p.B a))

/-- Replaying a returned move recovers both payoffs and a strict improvement. -/
theorem valid_of_findDeviationEnum_eq_some {d : Deviation p a}
    (h : findDeviationEnum p obs pay a r = some d) : Deviation.Valid p obs pay a r d :=
  valid_of_findDeviation_eq_some p obs pay a r _ _ h

/-- The profile is a Nash equilibrium exactly when the search exhausts both enumerations. -/
theorem findDeviationEnum_eq_none_iff : findDeviationEnum p obs pay a r = none ↔
    Nash p obs pay a r :=
  findDeviation_eq_none_iff p obs pay a r _ _ FinEnum.mem_toList FinEnum.mem_toList

/-- Decide the semantic Nash predicate by running the finite search. -/
@[expose] def decidableNash : Decidable (Nash p obs pay a r) :=
  decidable_of_iff _ (findDeviationEnum_eq_none_iff p obs pay a r)

/-- Print the player's change of action and its old and new payoffs. The game supplies the
names of its players and moves. -/
@[expose] def Deviation.render {q : PFunctor.{0, 0}} {b : q.A} (d : Deviation q b)
    (offer : q.A → String) (reply : q.B b → String) : String :=
  match d with
  | .offer move old new => s!"{offer move}, {old} to {new}"
  | .reply move old new => s!"{reply move}, {old} to {new}"

namespace Entry

/-- The potential entrant chooses whether to open a cart. -/
inductive Opening where
  | out | enter
  deriving DecidableEq

/-- The incumbent's options if the rival enters. -/
inductive Response where
  | share | priceWar
  deriving DecidableEq

/-- Staying out ends the interaction. Entering lets the incumbent choose a response. -/
@[expose] def Reply : Opening → Type
  | .out => Unit
  | .enter => Response

/-- The entry game's offers and permitted replies. -/
abbrev board : PFunctor.{0, 0} := ⟨Opening, Reply⟩

/-- Search the outside option first. -/
instance instFinEnumOpening : FinEnum Opening :=
  FinEnum.ofNodupList [.out, .enter] (by intro x; cases x <;> decide) (by decide)

/-- Search sharing before a price war. -/
instance instFinEnumResponse : FinEnum Response :=
  FinEnum.ofNodupList [.share, .priceWar] (by intro x; cases x <;> decide) (by decide)

/-- Enumerate precisely the replies available after each opening. -/
instance instFinEnumReply : (a : Opening) → FinEnum (Reply a)
  | .out => inferInstanceAs (FinEnum Unit)
  | .enter => instFinEnumResponse

/-- The incumbent commits to a response on entry. There is just one reply to staying out. -/
@[expose] def policy (onEntry : Response) : (a : Opening) → Reply a
  | .out => ()
  | .enter => onEntry

/-- Payoffs for the entrant and the incumbent, respectively. -/
@[expose] def payoff : ((a : Opening) × Reply a) → Int × Int
  | ⟨.out, ()⟩ => (0, 2)
  | ⟨.enter, .share⟩ => (3, 1)
  | ⟨.enter, .priceWar⟩ => (0, 0)

/-- Check a profile, including the entrant's counterfactual payoff under the incumbent's policy. -/
@[expose] def check (a : Opening) (onEntry : Response) : Option (Deviation board a) :=
  findDeviationEnum board Sigma.mk payoff a (policy onEntry)

/-- An empty result certifies an equilibrium of the entry game. -/
theorem check_eq_none_iff (a : Opening) (onEntry : Response) :
    check a onEntry = none ↔ Nash board Sigma.mk payoff a (policy onEntry) :=
  findDeviationEnum_eq_none_iff board Sigma.mk payoff a (policy onEntry)

/-- Replaying either player's reported deviation compares the actual entry payoffs. -/
theorem valid_of_check_eq_some (a : Opening) (onEntry : Response) {d : Deviation board a}
    (h : check a onEntry = some d) :
    Deviation.Valid board Sigma.mk payoff a (policy onEntry) d :=
  valid_of_findDeviationEnum_eq_some board Sigma.mk payoff a (policy onEntry) h

/-- Show which player can improve by switching moves. -/
@[expose] def report (a : Opening) (onEntry : Response) : String :=
  let opening : Opening → String
    | .out => "entrant stays out"
    | .enter => "entrant opens a cart"
  let reply : (b : Opening) → Reply b → String
    | .out, () => "incumbent has no move"
    | .enter, .share => "incumbent shares"
    | .enter, .priceWar => "incumbent starts a price war"
  match check a onEntry with
  | none => "Nash"
  | some d => d.render opening (reply a)

end Entry

end PolyFunExamples.Bargaining
