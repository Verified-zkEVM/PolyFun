/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# Loops, branching, and state over free programs, through `vcgen`

The acceptance test for "broad monadic code": `let mut` accumulators over `for` loops, `if`,
`if let`, and `StateT` over the free monad, each verified by `vcgen` with an invariant through
core's `Spec.forIn_list` and PolyFun's scoped demonic interpretation.
-/

@[expose] public section

set_option mvcgen.warning false

open Std.Internal.Do PFunctor
open scoped PFunctor.FreeM.DemonicWP

/-- A single-position query interface with boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- Count the `true` responses among `n` queries. -/
def countTrue (n : Nat) : FreeM coinP Nat := do
  let mut k := 0
  for _ in List.range n do
    let b ← FreeM.lift (P := coinP) PUnit.unit
    if b then k := k + 1
  pure k

/-- Whatever the responses, the count is bounded by the number of queries. -/
theorem countTrue_le (n : Nat) : ⦃ True ⦄ countTrue n ⦃ fun r => r ≤ n ⦄ := by
  vcgen [countTrue] invariants
    · fun pref _ k => k ≤ pref.length
  all_goals simp_all
  all_goals omega

/-- `if let` over an optional query result. -/
def firstOrDefault (o : Option Bool) : FreeM coinP Bool := do
  if let some b := o then
    pure b
  else
    FreeM.lift (P := coinP) PUnit.unit

/-- The `else` branch puts an operation in tail position with the value type already
normalized to `Bool`, where `vcgen`'s structural matcher cannot apply `Spec.lift` (stated at
`P.B a`); the residual `wp` goal is finished by the judgment equations, naming the interface
explicitly because its value type no longer reads `coinP.B _`. -/
example (o : Option Bool) : ⦃ True ⦄ firstOrDefault o ⦃ fun r => r = true ∨ r = false ⦄ := by
  vcgen -errorOnMissingSpec [firstOrDefault]
  · exact Bool.eq_false_or_eq_true _
  · rw [FreeM.DemonicWP.wp_apply_eq, FreeM.allOutputs_lift (P := coinP)]
    exact fun b => Bool.eq_false_or_eq_true b

/-- With the value type syntactically `P.B a`, a tail-position operation is decomposed by
`Spec.lift` directly. -/
example {P : PFunctor.{0, 0}} (a : P.A) (q : P.B a → Prop) (h : ∀ b, q b) :
    ⦃ True ⦄ FreeM.lift (P := P) a ⦃ q ⦄ := by
  vcgen
  all_goals apply h

/-- State over the free monad: a counter advanced once per query. -/
def tick (n : Nat) : StateT Nat (FreeM coinP) Unit := do
  for _ in List.range n do
    let _ ← FreeM.lift (P := coinP) PUnit.unit
    modify (· + 1)

theorem tick_spec (n : Nat) : ⦃ fun s => s = 0 ⦄ tick n ⦃ fun _ s => s = n ⦄ := by
  vcgen [tick] invariants
    · fun pref _ _ s => s = pref.length
  all_goals simp_all
