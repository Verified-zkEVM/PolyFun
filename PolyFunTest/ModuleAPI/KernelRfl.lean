/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Logic.KernelRfl
import ToCslib.Data.Fin.Cases
import Mathlib.Data.List.Sort

/-!
# `kernel_rfl` through ordinary imports

The tactic is usable from a module that imports it normally. The kernel unfolds an exposed body
from another module, and fails loudly on a body that module mode hides: Mathlib's
`List.insertionSort` is not exposed, so its reduction is out of reach without `import all`,
which this repository never applies to an external library.
-/

example {n : Nat} {α : Fin (n + 1) → Type} (x : α 0) (xs : ∀ i : Fin n, α i.succ) :
    Fin.casesDirect x xs 0 = x := by kernel_rfl

example {n : Nat} {α : Fin (n + 1) → Type} (x : α 0) (xs : ∀ i : Fin n, α i.succ)
    (i : Fin n) : Fin.casesDirect x xs i.succ = xs i := by kernel_rfl

/--
error: (kernel) declaration type mismatch, '_private.PolyFunTest.ModuleAPI.KernelRfl.0._example._proof_1' has type
  List.insertionSort (fun x1 x2 ↦ x1 ≤ x2) [3, 1, 2] = List.insertionSort (fun x1 x2 ↦ x1 ≤ x2) [3, 1, 2]
but it is expected to have type
  List.insertionSort (fun x1 x2 ↦ x1 ≤ x2) [3, 1, 2] = [1, 2, 3]
-/
#guard_msgs in
example : [3, 1, 2].insertionSort (· ≤ ·) = [1, 2, 3] := by kernel_rfl
