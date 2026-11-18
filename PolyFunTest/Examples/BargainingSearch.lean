/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.BargainingSearch
meta import Examples.Tutorials.BargainingSearch

/-! # Nash verdicts, replayed moves and printed witnesses from an ordinary importer -/

namespace PolyFunTest.BargainingSearch

open PolyFunExamples.Bargaining

section Entry

open Entry

local instance (a : Opening) (act : Response) :
    Decidable (Nash board Sigma.mk payoff a (policy act)) :=
  decidableNash board Sigma.mk payoff a (policy act)

example : Nash board Sigma.mk payoff .out (policy .priceWar) := by decide
example : ¬ Nash board Sigma.mk payoff .out (policy .share) := by decide
example : ¬ Nash board Sigma.mk payoff .enter (policy .priceWar) := by decide
example : Nash board Sigma.mk payoff .enter (policy .share) := by decide

example : check .out .share = some (.offer .enter 0 3) := rfl
example : check .enter .priceWar = some (.reply .share 0 1) := rfl

/-- Omitting entry hides a profitable move, while listing entry alone gives a replayable witness. -/
example : findDeviation board Sigma.mk payoff .out (policy .share) [.out] [] = none ∧
    ¬ Nash board Sigma.mk payoff .out (policy .share) ∧
    Deviation.Valid board Sigma.mk payoff .out (policy .share) (.offer .enter 0 3) := by
  exact ⟨rfl, by decide, valid_of_findDeviation_eq_some board Sigma.mk payoff .out
    (policy .share) [.enter] [] rfl⟩

/-- The entrant gains three by entering when the incumbent shares. -/
public theorem entrant_deviation_replays :
    Deviation.Valid board Sigma.mk payoff .out (policy .share) (.offer .enter 0 3) :=
  valid_of_check_eq_some _ _ rfl
example : Deviation.Valid board Sigma.mk payoff .enter (policy .priceWar) (.reply .share 0 1) :=
  valid_of_check_eq_some _ _ rfl

/-- info: ["Nash", "entrant opens a cart, 0 to 3", "incumbent shares, 0 to 1", "Nash"] -/
#guard_msgs in
#eval [report .out .priceWar, report .out .share, report .enter .priceWar, report .enter .share]

end Entry

section Pirates

open FourCoins

local instance : FinEnum Offer :=
  FinEnum.ofNodupList [.one, .two] (by intro x; cases x <;> decide) (by decide)

local instance : FinEnum Bool :=
  FinEnum.ofNodupList [false, true] (by intro x; cases x <;> decide) (by decide)

private def orderedReport : List String := profiles.map fun (a, r) =>
  let amount : Offer → String | .one => "1" | .two => "2"
  let action (x : Bool) := if x then "accept" else "reject"
  let result := match findDeviationEnum board Prod.mk coins a r.reply with
    | none => if subgamePerfect a r then "subgame-perfect Nash" else "Nash"
    | some d => d.render (fun b => s!"captain switches to {amount b}")
        (fun x => s!"mate chooses {action x}")
  s!"offer {amount a}, replies ({action r.acceptOne}, {action r.acceptTwo}): {result}"

/--
info: offer 1, replies (reject, reject): mate chooses accept, 0 to 1
offer 1, replies (reject, accept): captain switches to 2, 0 to 2
offer 1, replies (accept, reject): Nash
offer 1, replies (accept, accept): subgame-perfect Nash
offer 2, replies (reject, reject): mate chooses accept, 0 to 2
offer 2, replies (reject, accept): Nash
offer 2, replies (accept, reject): captain switches to 1, 0 to 3
offer 2, replies (accept, accept): captain switches to 1, 2 to 3
-/
#guard_msgs in
#eval orderedReport.forM IO.println

/-- info: true -/
#guard_msgs in
#eval orderedReport == report

end Pirates

end PolyFunTest.BargainingSearch

namespace PolyFunTest.BargainingSearch.Auction

open PolyFunExamples.Bargaining

/-- Passing allows only an acknowledgement. Entering permits any natural-number bid. -/
private def BidReply : Bool → Type
  | false => Unit
  | true => Nat

local instance : FinEnum Bool := FinEnum.ofNodupList [false, true]
  (by intro b; cases b <;> decide) (by decide)

private abbrev auction : PFunctor.{0, 0} := ⟨Bool, BidReply⟩

private def bid : (a : Bool) → BidReply a
  | false => ()
  | true => (7 : Nat)

private def amount : (a : Bool) → BidReply a → Int
  | false, _ => 0
  | true, n => Int.ofNat n

local instance : FinEnum (BidReply false) := inferInstanceAs (FinEnum Unit)

example : Infinite (auction.B true) := inferInstanceAs (Infinite Nat)

/-- At the passing profile the checker replays a profitable bid without enumerating bid values. -/
example : findDeviationEnum auction amount (fun n => (n, 0)) false bid =
    some (.offer true 0 7) := rfl

example : Deviation.Valid auction amount (fun n => (n, 0)) false bid (.offer true 0 7) :=
  valid_of_findDeviationEnum_eq_some auction amount (fun n => (n, 0)) false bid rfl

end PolyFunTest.BargainingSearch.Auction
