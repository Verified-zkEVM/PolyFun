/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Data.Fin.MOfFn
meta import ToCslib.Data.Fin.MOfFn

/-!
# Compiled finite case analysis

The `#eval` checks exercise the compiler simplifications from `ToCslib.Data.Fin.Cases` at
depth 64, where repeatedly evaluating discarded induction hypotheses would be expensive.
The last entry evaluates to `63` for chains built with `Fin.cons`, `Matrix.vecCons`, and
`Fin.cases`, and to `some 63` after collecting the entries with `Fin.mOfFn` in `Option`.
-/

public section

namespace PolyFunTest.FinCases

/-- `0, 1, …, n - 1`, as `n` nested `Fin.cons`. -/
def consChain : (n : ℕ) → Fin n → ℕ
  | 0 => Fin.elim0
  | n + 1 => Fin.cons 0 fun i => consChain n i + 1

/-- `0, 1, …, n - 1`, as `n` nested `Matrix.vecCons`. -/
def vecChain : (n : ℕ) → Fin n → ℕ
  | 0 => ![]
  | n + 1 => Matrix.vecCons 0 fun i => vecChain n i + 1

/-- The value of a position, by recursion through `Fin.cases`. -/
def casesDepth : (n : ℕ) → Fin n → ℕ
  | n + 1, i => Fin.cases 0 (fun j => casesDepth n j + 1) i

/-- info: 63 -/
#guard_msgs in
#eval consChain 64 (Fin.last 63)

/-- info: 63 -/
#guard_msgs in
#eval vecChain 64 (Fin.last 63)

/-- info: 63 -/
#guard_msgs in
#eval casesDepth 64 (Fin.last 63)

/-- info: some 63 -/
#guard_msgs in
#eval (Fin.mOfFn 64 fun i => some i.val).map fun f => f (Fin.last 63)

end PolyFunTest.FinCases
