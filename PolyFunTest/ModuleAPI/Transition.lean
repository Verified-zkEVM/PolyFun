/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Transition

/-! # Ordinary-import checks for fuel-bounded deterministic transitions -/

open Control.Transition

public section

namespace PolyFunTest.Transition

/-- Count down to zero, one transition per step. -/
def countdown : Control.Transition Nat (Except String Nat)
  | 0 => .inl (.ok 0)
  | n + 1 => .inr n

-- Zero fuel keeps the state; each call, including the terminal one, consumes one unit.
example : run countdown 0 0 = .inr 0 := rfl
example : run countdown 1 0 = .inl (.ok 0) := rfl
example : run countdown 2 5 = .inr 3 := rfl
example : run countdown 6 5 = .inl (.ok 0) := rfl
example : run (fun (_ : Nat) => .inl (Except.error "failure" : Except String Nat)) 1 0 =
    .inl (.error "failure") := rfl

-- A transition that never returns keeps its exact state at every budget.
example (n : Nat) : run (fun s : Nat => (Sum.inr s : Nat ⊕ Nat)) n 4 = .inr 4 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

example (n m state : Nat) :
    run countdown (n + m) state = continueRun countdown m (run countdown n state) :=
  run_add countdown n m state

example (fuel state : Nat) :
    (toMachine countdown).runChunk tickHandler fuel (.inr state) =
      toChunk (run countdown fuel state) := runChunk_toMachine countdown fuel state

end PolyFunTest.Transition
