/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Meter

/-!
# Moving charges between meters

Checks for `PolyFun.PFunctor.Handler.Meter`, with charges in the free additive monoid on the
requests, so that a law that loses the order of the charges fails:

* from a starting total, the state meter ends at the total followed by the writer's log, and adding
  the log on the left instead gives a different total;
* a passive counter beside a stateful handler ends at its starting value followed by the log, beside
  the handler's own state;
* a failure in the base monad discards the charges of every meter;
* moving a charged run along a monad lift, and mapping its log to a sum, agree with the run charged
  directly.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeMeters

/-- Requests carry a number and get no information back. -/
abbrev Req : PFunctor := ⟨ℕ, fun _ => Unit⟩

/-- Charge each request by itself, in order. -/
abbrev word : Req.A → FreeAddMonoid ℕ := FreeAddMonoid.of

/-- Two requests, `1` and then `2`. -/
def twoReqs : FreeM Req Unit := do
  FreeM.lift (P := Req) 1
  FreeM.lift (P := Req) 2

/-- Answer every request. -/
def ok : Handler Id Req := fun _ => ()

/-! ## Writer and state meters -/

/-- From the total `[99]`, the state meter ends at `[99, 1, 2]`. -/
example : ((twoReqs.liftM (ok.withCharge word)).run (.of 99)).run =
    ((), FreeAddMonoid.ofList [99, 1, 2]) := rfl

/-- The law: the state meter is the starting total followed by the writer's log. -/
example : (twoReqs.liftM (ok.withCharge word)).run (.of 99) =
    (fun p => (p.1, FreeAddMonoid.of 99 + Multiplicative.toAdd p.2)) <$>
      (twoReqs.liftM (ok.withChargeW word)).run :=
  Handler.run_liftM_withCharge ok word twoReqs _

/-- Adding the writer's log on the left of the starting total gives a different total, so the
order in `Handler.run_liftM_withCharge` is the one runs have. -/
example : ((twoReqs.liftM (ok.withCharge word)).run (.of 99)).run.2 ≠
    Multiplicative.toAdd (twoReqs.liftM (ok.withChargeW word)).run.run.2 + .of 99 := by
  intro h
  exact absurd (congrArg FreeAddMonoid.toList h) (by decide)

/-! ## A counter beside a stateful handler -/

/-- A stateful handler that adds each request to its state. -/
def summing : Handler.Stateful Id ℕ Req := fun a => StateT.mk fun s => ((), s + a)

/-- From state `5` and counter `[99]`, the extended handler ends at state `8` and counter
`[99, 1, 2]`. -/
example : ((Handler.Stateful.extend summing fun a _ _ _ total => total + word a).run twoReqs
    (5, .of 99)).run = ((), (8, FreeAddMonoid.ofList [99, 1, 2])) := rfl

/-- The law: the counter is the writer's log of the same run, beside the same state. -/
example : (Handler.Stateful.extend summing fun a _ _ _ total => total + word a).run twoReqs
      (5, .of 99) =
    (fun r => (r.1.1, (r.2, FreeAddMonoid.of 99 + Multiplicative.toAdd r.1.2))) <$>
      (twoReqs.liftM (summing.withChargeW word)).run.run 5 :=
  Handler.Stateful.run_extend_eq_withChargeW summing word twoReqs 5 _

/-- The counter keeps its order too: with the log on the left, the counter would differ. -/
example : (((Handler.Stateful.extend summing fun a _ _ _ total => total + word a).run twoReqs
    (5, .of 99)).run.2.2) ≠ FreeAddMonoid.ofList [1, 2, 99] := by
  intro h
  exact absurd (congrArg FreeAddMonoid.toList h) (by decide)

/-! ## Failure in the base monad -/

/-- Fail on request `2`. -/
def failOnTwo : Handler Option Req := fun a => if a = 2 then none else some ()

/-- A failure discards the charges already made, in the state meter and in the writer meter. -/
example : (twoReqs.liftM (failOnTwo.withCharge word)).run (.of 99) = none := rfl

example : (twoReqs.liftM (failOnTwo.withChargeW word)).run = none := rfl

/-- One request that succeeds. -/
def oneReq : FreeM Req Unit := FreeM.lift (P := Req) 1

/-! ## Naturality -/

/-- Lift into a stateful monad that leaves its state alone. -/
abbrev intoState : Option →ᵐ StateT ℕ Option := MonadHom.ofLift Option (StateT ℕ Option)

/-- Lifting a writer-charged run is the run of the lifted handler, charged the same way. -/
example : WriterT.mapHom intoState (oneReq.liftM (failOnTwo.withChargeW word)) =
    oneReq.liftM ((Handler.mapTarget (fun x => intoState x) failOnTwo).withChargeW word) :=
  Handler.mapHom_liftM_withChargeW intoState failOnTwo word oneReq

example : (WriterT.mapHom intoState (oneReq.liftM (failOnTwo.withChargeW word))).run.run 7 =
    some (((), Multiplicative.ofAdd (FreeAddMonoid.of 1)), 7) := rfl

/-- Sum a word of requests. -/
def total : FreeAddMonoid ℕ →+ ℕ := FreeAddMonoid.lift id

/-- Mapping the log to its sum is charging each request by itself as a number. -/
example : WriterT.mapOutputHom (AddMonoidHom.toMultiplicative total)
      (twoReqs.liftM (ok.withChargeW word)) =
    twoReqs.liftM (ok.withChargeW (total ∘ word)) :=
  Handler.mapOutputHom_liftM_withChargeW total ok word twoReqs

example :
    (twoReqs.liftM (ok.withChargeW (total ∘ word))).run.run = ((), Multiplicative.ofAdd 3) := by
  decide

end PolyFunTest.ChargeMeters
