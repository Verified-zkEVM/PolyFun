/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Combinators

/-!
# Ordinary-import canaries for stateful handler combinators

VCVio's `StateT`-valued query implementations compose with `mapStateTBase`, `parallelStateT`,
`flattenStateT`, `piStateT`, `extendState`, and `fixSndStateT`; these are the
`Handler.Stateful` combinators. The examples check the run laws through ordinary imports on a
concrete counter interface, where a wrong state component or a dropped effect changes a result.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.StatefulCombinators

open _root_.PFunctor

/-- One request, answered by the current count. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- One request, answered by whether a flag is set. -/
abbrev flag : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Answer with the count, then increment it. -/
def tick : Handler.Stateful Id Nat counter := fun _ =>
  (modifyGet fun n : Nat => (n, n + 1) : StateT Nat Id Nat)

/-- Answer with the flag, then clear it. -/
def take : Handler.Stateful Id Bool flag := fun _ =>
  (modifyGet fun b : Bool => (b, false) : StateT Bool Id Bool)

/-- Two counter requests and one flag request against the sum interface. -/
def program : FreeM (counter + flag) (Nat × Nat × Bool) := do
  let a ← FreeM.lift (P := counter + flag) (.inl ())
  let c ← FreeM.lift (P := counter + flag) (.inr ())
  let b ← FreeM.lift (P := counter + flag) (.inl ())
  pure (a, b, c)

/-- `parallel` threads each summand's state through its own component. -/
example : Id.run ((Handler.Stateful.parallel tick take).run program (3, true)) =
    ((3, 4, true), (5, false)) := rfl

/-- `extend` records the request history in a passive auxiliary component. -/
def logged : Handler.Stateful Id (Nat × List Nat) counter :=
  Handler.Stateful.extend tick fun _ before _ _ log => before :: log

example : Id.run (logged.run (FreeM.lift (P := counter) () >>= fun _ => FreeM.lift ()) (7, [])) =
    (8, (9, [8, 7])) := rfl

/-- Forgetting the auxiliary component recovers the base run. -/
example (x : FreeM counter Nat) (s : Nat) (log : List Nat) :
    Prod.map id Prod.fst <$> logged.run x (s, log) = tick.run x s :=
  Handler.Stateful.run_extend_map_fst tick _ x s log

/-- `fixSnd` reads the auxiliary component at a fixed value and drops it. -/
example : Id.run ((Handler.Stateful.fixSnd logged []).run (FreeM.lift (P := counter) ()) 2) =
    (2, 3) := rfl

/-- `flatten` reassociates a handler over a stateful base into one product state. -/
def nested : Handler.Stateful (StateT Bool Id) Nat counter := fun _ =>
  StateT.mk fun n => (modifyGet fun b : Bool => ((n, n + 1), !b) : StateT Bool Id (Nat × Nat))

example : Id.run ((Handler.Stateful.flatten nested).run
    (FreeM.lift (P := counter) () >>= fun _ => FreeM.lift ()) (0, false)) =
    (1, (2, false)) := rfl

/-- `mapBase` interprets the base free monad through an outer handler. -/
def viaFlag : Handler.Stateful (FreeM flag) Nat counter := fun _ =>
  StateT.mk fun n => (fun b => (if b then n else 0, n + 1)) <$> FreeM.lift (P := flag) ()

example : Id.run (((Handler.Stateful.mapBase take viaFlag).run
    (FreeM.lift (P := counter) () >>= fun _ => FreeM.lift ()) 4).run true) =
    ((0, 6), false) := rfl

/-- The run through the composite is the interpreted run through the inner handler. -/
example (x : FreeM counter Nat) (s : Nat) :
    (viaFlag.run x s).liftM take = (Handler.Stateful.mapBase take viaFlag).run x s :=
  Handler.Stateful.run_mapBase take viaFlag x s

/-- The value-preserving handler over `counter` that echoes the count without changing it
returns every program's value unchanged. -/
example (x : FreeM counter Nat) (s : Nat) :
    Prod.fst <$> (Handler.Stateful.lift (S := Nat) FreeM.lift : Handler.Stateful (FreeM counter)
      Nat counter).run x s = x :=
  Handler.Stateful.map_fst_run_eq_self _ (fun a s => by simp [Handler.Stateful.lift]) x s

end PolyFunTest.ModuleAPI.StatefulCombinators
