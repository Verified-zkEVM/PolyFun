/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Link

/-!
# Sequential and parallel composition of stateful packages

Regression checks for `Handler.Stateful.link` and `sumMap`. Each package keeps a state with a
distinguishable update and the inner handler can fail, so swapping state components, dropping
the inner effect, or running the layers in the wrong order changes an observed result.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Handler.Stateful.Link

open _root_.PFunctor Handler.Stateful

/-- One request, answered by a number. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- One request, answered by a Boolean. -/
abbrev flag : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A package over `counter`: ask the import once, add the own offset, and raise the offset
by ten. -/
def offset : Handler.Stateful (FreeM counter) Nat counter :=
  fun _ k => FreeM.liftBind () fun n => pure (n + k, k + 10)

/-- An implementation of `counter`: answer with the count and increment it, failing at three. -/
def ticker : Handler.Stateful Option Nat counter :=
  fun _ n => if n = 3 then none else some (n, n + 1)

/-- A package over `flag`: forward the request and count how often it was asked. -/
def forwardFlag : Handler.Stateful (FreeM flag) Nat flag :=
  fun _ k => FreeM.liftBind () fun b => pure (b, k + 1)

/-- An implementation of `flag`: answer with the flag and toggle it. -/
def toggler : Handler.Stateful Option Bool flag :=
  fun _ b => some (b, !b)

/-- Ask for two answers and return both, in order. -/
def twoQueries : FreeM counter (Nat × Nat) :=
  FreeM.liftBind () fun a => FreeM.liftBind () fun b => pure (a, b)

/-! ### Sequential composition -/

/-- The outer offset and the inner count both advance, in the outer-then-inner state order. -/
example : (offset.link ticker).run twoQueries (100, 0) = some ((100, 111), (120, 2)) := rfl

/-- A failure of the inner handler is a failure of the linked package. -/
example : (offset.link ticker).run twoQueries (100, 2) = none := rfl

/-- Three layers: each offset is added once per request. -/
example : ((offset.link offset).link ticker).run twoQueries ((100, 1000), 0) =
    some ((1100, 1121), ((120, 1020), 2)) := rfl

example : (offset.link (offset.link ticker)).run twoQueries (100, (1000, 0)) =
    some ((1100, 1121), (120, (1020, 2))) := rfl

/-- The two bracketings agree up to the reassociation of the state. -/
example : (offset.link offset).link ticker =
    stateCongr (Equiv.prodAssoc Nat Nat Nat).symm (offset.link (offset.link ticker)) :=
  link_assoc offset offset ticker

/-- The run law: a linked run is the inner run of the outer run. -/
example : (offset.link ticker).run twoQueries (100, 0) =
    (fun r => (r.1.1, (r.1.2, r.2))) <$> ticker.run (offset.run twoQueries 100) 0 :=
  run_link offset ticker twoQueries 100 0

/-! ### Parallel composition and interchange -/

/-- A flag request through the linked parallel package touches only the flag components. -/
example : ((sumMap offset forwardFlag).link (sum ticker toggler) (.inr ())).run
    ((5, 7), (0, true)) = some (true, ((5, 8), (0, false))) := rfl

/-- The same request through the sum of the two linked packages, with the state components
exchanged. -/
example : ((sum (offset.link ticker) (forwardFlag.link toggler)) (.inr ())).run
    ((5, 0), (7, true)) = some (true, ((5, 0), (8, false))) := rfl

example : (sumMap offset forwardFlag).link (sum ticker toggler) =
    stateCongr (Equiv.prodProdProdComm Nat Nat Nat Bool)
      (sum (offset.link ticker) (forwardFlag.link toggler)) :=
  sumMap_link_sum offset forwardFlag ticker toggler

end PolyFunTest.PFunctor.Handler.Stateful.Link
