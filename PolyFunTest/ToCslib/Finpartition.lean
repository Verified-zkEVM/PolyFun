/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import ToCslib.Order.Finpartition

/-!
# Enumeration of finite partitions by their number of parts

The empty set has one partition into zero parts. For five elements we check the full
distribution and inspect the actual parts returned by the executable enumeration.
-/

namespace PolyFunTest.Finpartition

example : (Finpartition.allWithCard 0 0).map (fun p => p.parts.card) = [0] := by decide

example : Finpartition.allWithCard 0 1 = [] := by decide

example : (List.range 7).map (fun k => (Finpartition.allWithCard 5 k).length) =
    [0, 1, 15, 25, 10, 1, 0] := by decide

example : ((Finpartition.allWithCard 5 2).map (fun p => p.parts.card)).all (· == 2) := by decide

/-- Compare the returned partitions themselves with Mathlib's finite universe, independently
of the Stirling count. -/
public def agreesWithUniv (n k : Nat) : Bool :=
  (Finpartition.allWithCard n k).toFinset ==
    (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))).filter
      (fun p => p.parts.card = k)

example : (List.range 3).all (fun n => (List.range (n + 2)).all (agreesWithUniv n)) = true := by
  decide

/-- The three two-block partitions of three elements, with arbitrary block order forgotten. -/
example : ((Finpartition.allWithCard 3 2).map Finpartition.parts).toFinset =
    {{{0, 1}, {2}}, {{0, 2}, {1}}, {{0}, {1, 2}}} := by decide

end PolyFunTest.Finpartition
