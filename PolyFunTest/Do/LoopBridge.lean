/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.IdLoops
public import ToCslib.Control.Loop.Array
public import ToCslib.Control.Loop.While
public import Mathlib.Data.List.Basic

/-!
# Imperative loops two ways: the loop lemmas and core's `vcgen`

Three `Id.run do` programs, each proved twice: by rewriting with the loop lemmas of
`ToCslib.Control.Loop` and `PolyFun.Control.Monad.Support.IdLoops`, and by core's `vcgen` after
`Std.WP.Id.of_run_eq_wp` turns the equation about `Id.run` into a weakest precondition.

* `fillGrid` writes `i + j` at `i * n + j` of an array in two nested loops over `[0:k]` and
  `[0:n]`, and counts the writes in a cursor.
* `decodeBounded` reads `k` entries and returns `none` from inside the loop at the first entry out
  of bounds.
* `drain` is a `while` loop with a decreasing measure, written plainly and with the intrinsic
  `decreasing` and `invariant` clauses.

The proofs record what `vcgen` covers at the pinned toolchain: it steps through legacy ranges
through `Std.WP.Spec.forIn_pure`, nested loops take one invariant each, and the labelled form
`| inv2 pref cur suff h a b hinv => …` names the outer loop's variables in the inner invariant.
`Std.WP.Invariant.withEarlyReturnNewDo` handles `return` inside a loop, and `simp_all` reduces its
lattice connectives to `∧`, `∨` and `∃`. A `while` loop takes a `Std.WP.WhileInvariant` and a
`Std.WP.Variant`, the latter with its universe fixed by hand. An intrinsic `invariant` clause
whose `exit` binder is named elaborates to a `have`, and `vcgen` then fails.
-/

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace PolyFunTest.LoopBridge

/-! ## Nested loops writing an array, with a cursor -/

/-- Write `i + j` at `i * n + j` for `i < k` and `j < n`, counting the writes. -/
def fillGrid (k n : Nat) : Array Nat × Nat := Id.run do
  let mut a := Array.replicate (k * n) 0
  let mut c := 0
  for i in [0:k] do
    for j in [0:n] do
      a := a.set! (i * n + j) (i + j)
      c := c + 1
  return (a, c)

/-- The loop lemmas: `loop_norm` turns the loops into folds and splits the pair state, and the
array fill lemma finishes. -/
theorem fillGrid_eq (k n : Nat) :
    fillGrid k n = (Array.ofFn fun t : Fin (k * n) => t / n + t % n, k * n) := by
  simp only [fillGrid, loop_norm]
  refine Prod.ext ?_ ?_
  · simp only [loop_norm]
    exact Array.foldl_foldl_set!_range_eq_ofFn (fun i j => i + j) (by simp)
  · simp only [loop_norm]
    simp [Nat.mul_comm]

/-- The grid after its first `m` cells. -/
def gridUpTo (k n m : Nat) : Array Nat :=
  Array.ofFn fun t : Fin (k * n) => if t.val < m then t / n + t % n else 0

theorem gridUpTo_step {k n i j : Nat} (hi : i < k) (hj : j < n) :
    (gridUpTo k n (i * n + j)).set! (i * n + j) (i + j) = gridUpTo k n (i * n + j + 1) := by
  have hlt : i * n + j < k * n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    omega
  have hdiv : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  refine Array.ext_getElem? fun t => ?_
  simp only [gridUpTo, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.getElem?_ofFn, Array.size_ofFn]
  by_cases ht : i * n + j = t
  · subst ht
    simp [hlt, hdiv, hmod]
  · simp only [ht, ite_false]
    by_cases htk : t < k * n
    · simp only [htk, dite_true, Option.some.injEq]
      congr 1
      apply propext
      omega
    · simp [htk]

/-- `vcgen`, with one invariant per loop. The inner invariant names the outer loop's consumed
prefix through the labelled form. -/
theorem fillGrid_eq_of_vcgen (k n : Nat) :
    fillGrid k n = (Array.ofFn fun t : Fin (k * n) => t / n + t % n, k * n) := by
  unfold fillGrid
  refine Id.of_run_eq_wp
    (P := fun r : Array Nat × Nat => r = (Array.ofFn fun t : Fin (k * n) => t / n + t % n, k * n))
    rfl ?_
  vcgen invariants
    | inv1 => fun pref _ s => s = (gridUpTo k n (pref.length * n), pref.length * n)
    | inv2 opref _ _ _ _ _ _ => fun pref _ s =>
        s = (gridUpTo k n (opref.length * n + pref.length), opref.length * n + pref.length)
  case vc1 =>
    simp only [List.length_nil, Nat.zero_mul, gridUpTo, Nat.not_lt_zero, ite_false]
    congr 1
    exact Array.ext (by simp [a]) (by simp [a])
  case vc2 h =>
    simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size_mk_one, List.length_range']
      at h
    rw [h]
    congr 1
    simp only [gridUpTo, Nat.sub_zero]
    congr
    funext t
    simp [t.isLt]
  case vc3 h => simpa using h
  case vc4 h =>
    simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size_mk_one, List.length_range',
      Nat.sub_zero] at h
    simp only [h, List.length_append, List.length_singleton, Nat.succ_mul]
  case vc5 _ _ _ ho _ _ _ _ _ _ hi _ _ hs =>
    simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size_mk_one, Nat.sub_zero] at ho hi
    have hco := List.eq_add_mul_length_of_range'_eq_append_cons ho
    have hlo := List.length_lt_of_range'_eq_append_cons ho
    have hci := List.eq_add_mul_length_of_range'_eq_append_cons hi
    have hli := List.length_lt_of_range'_eq_append_cons hi
    simp only [Nat.zero_add, Nat.one_mul] at hco hci
    subst hco hci
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    simp only [a, c, gridUpTo_step hlo hli]

/-! ## A decoder with early return -/

/-- Read `k` entries, returning `none` at the first entry that is not below `bound`. -/
def decodeBounded (bound k : Nat) (bytes : Array Nat) : Option (Array Nat) := Id.run do
  let mut out := #[]
  for i in [0:k] do
    let v := bytes.getD i 0
    if v ≥ bound then
      return none
    out := out.push v
  return some out

theorem map_dite_range' (xs : Array Nat) :
    (List.range' 0 xs.size).map (fun i => if h : i < xs.size then xs[i] else 0) = xs.toList := by
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.length_map, List.length_range'] at h₁
  simp [h₁]

theorem map_getD_range (xs : Array Nat) :
    (List.range xs.size).map (xs.getD · 0) = xs.toList := by
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.length_map, List.length_range] at h₁
  simp [h₁]

/-- The loop lemmas: on valid input the body only yields, so the loop is a fold. -/
theorem decodeBounded_self (bound : Nat) (xs : Array Nat) (h : ∀ x ∈ xs, x < bound) :
    decodeBounded bound xs.size xs = some xs := by
  simp only [decodeBounded, Id.run_bind]
  rw [Id.run_forIn_eq_foldl_of_pureForIn_of_inv _ (fun s i => (none, s.2.push (xs.getD i 0)))
    (fun _ _ _ => True) ?step trivial]
  case step =>
    intro pref cur suff hsplit s _
    have hcur : cur < xs.size := by
      have : cur ∈ ForIn.toList [:xs.size] := by rw [hsplit]; simp
      simpa using this
    have hv : xs.getD cur 0 < bound := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcur, Option.getD_some]
      exact h _ (Array.getElem_mem hcur)
    exact ⟨by rw [ite_eq_right (Nat.not_le.2 hv)], trivial⟩
  simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size_mk_one, loop_norm,
    List.foldl_fixed', List.foldl_push_eq_append, map_getD_range]
  simp

/-- The loop lemmas: an entry out of bounds makes the decoder return `none`. The rule is applied
to the elaborated `do` block, so the loop body is not restated. -/
theorem decodeBounded_eq_none (bound k : Nat) (bytes : Array Nat)
    (h : ∃ i < k, bound ≤ bytes.getD i 0) : decodeBounded bound k bytes = none := by
  unfold decodeBounded
  apply Id.run_bind_forIn_earlyReturn_of_pureForIn [:k] (· = none)
    (fun pref _ _ => ∀ i ∈ pref, bytes.getD i 0 < bound) (fun r _ => r = none)
  · intro pref cur suff _ b hb
    by_cases hc : bound ≤ bytes.getD cur 0
    · simp only [ge_iff_le, hc, ite_true]
      rfl
    · simp only [ge_iff_le, hc, ite_false]
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact hb i hi
      · rw [List.mem_singleton.1 hi]
        exact Nat.lt_of_not_le hc
  · simp
  · intro r _ hr
    simp [hr]
  · intro _ hall
    obtain ⟨i, hi, hle⟩ := h
    exact absurd (hall i (by simpa using hi)) (Nat.not_lt.2 hle)

/-- `vcgen` with `Invariant.withEarlyReturnNewDo`. -/
theorem decodeBounded_self_of_vcgen (bound : Nat) (xs : Array Nat) (h : ∀ x ∈ xs, x < bound) :
    decodeBounded bound xs.size xs = some xs := by
  unfold decodeBounded
  refine Id.of_run_eq_wp (P := fun r : Option (Array Nat) => r = some xs) rfl ?_
  vcgen invariants
    · Invariant.withEarlyReturnNewDo Prop (fun pref _ out => out.toList = pref.map (xs.getD · 0))
        (fun r _ => r = some xs)
  case vc1 => simp_all; rfl
  case vc2 => simp_all
  case vc3 => simp_all [map_dite_range']
  case vc4 pref cur suff hsplit _ _ _ hge =>
    have hsplit' : List.range' 0 xs.size = pref ++ cur :: suff := by simpa using hsplit
    have hcur : cur < xs.size := by
      have := List.eq_add_mul_length_of_range'_eq_append_cons hsplit'
      have := List.length_lt_of_range'_eq_append_cons hsplit'
      omega
    have hv : v < bound := by simpa [v, hcur] using h _ (Array.getElem_mem hcur)
    exact absurd hv (Nat.not_lt.2 hge)
  case vc5 =>
    simp_all [out, v]
    split <;> simp_all

/-- `vcgen` with `Invariant.withEarlyReturnNewDo`, for an entry out of bounds. -/
theorem decodeBounded_eq_none_of_vcgen (bound k : Nat) (bytes : Array Nat)
    (h : ∃ i < k, bound ≤ bytes.getD i 0) : decodeBounded bound k bytes = none := by
  unfold decodeBounded
  refine Id.of_run_eq_wp (P := fun r : Option (Array Nat) => r = none) rfl ?_
  vcgen invariants
    · Invariant.withEarlyReturnNewDo Prop (fun pref _ _ => ∀ i ∈ pref, bytes.getD i 0 < bound)
        (fun r _ => r = none)
  case vc1 => simp_all
  case vc2 => simp_all
  case vc3 =>
    obtain ⟨i, hi, hle⟩ := h
    simp_all
    grind
  case vc4 => simp_all
  case vc5 =>
    simp_all [or_imp, v]
    split <;> simp_all

/-! ## A `while` loop with a decreasing measure -/

/-- Move `n` units from `i` to `s`, one at a time. -/
def drain (n : Nat) : Nat × Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0 do
    s := s + 1
    i := i - 1
  return (i, s)

/-- The loop lemmas: an invariant, a measure, and the postcondition of the stopping step. -/
theorem drain_eq (n : Nat) : drain n = (0, n) := by
  simp only [drain, Id.run_bind, Id.run_pure, Prod.eta]
  apply Lean.Loop.idRun_forIn_of_measure (fun s : Nat × Nat => s.2 + s.1 = n)
    (fun s : Nat × Nat => s = (0, n)) (fun s : Nat × Nat => s.1) ?_ ?_
  · simp
  intro ⟨i, s⟩ (hinv : s + i = n)
  by_cases hi : 0 < i
  · simp only [gt_iff_lt, hi, ↓reduceIte, Id.run_pure]
    exact ⟨show s + 1 + (i - 1) = n by omega, show i - 1 < i by omega⟩
  · simp only [gt_iff_lt, hi, ↓reduceIte, Id.run_pure]
    show (i, s) = (0, n)
    rw [Prod.mk.injEq]
    omega

/-- `vcgen`, with a `WhileInvariant` and a `Variant`. The variant's universe must be given: left
as a metavariable, it makes the declaration fail. -/
theorem drain_eq_of_vcgen (n : Nat) : drain n = (0, n) := by
  unfold drain
  refine Id.of_run_eq_wp (P := fun r : Nat × Nat => r = (0, n)) rfl ?_
  vcgen invariants
    | inv1 => WhileInvariant.ofInvariantAndBreak (fun s : Nat × Nat => s.2 + s.1 = n)
        (fun s => s.1 = 0)
    | inv2 => (Variant.ofMeasure (fun s : Nat × Nat => s.1) : Variant.{0, 0, 0} (Nat × Nat) Prop)
  all_goals simp_all
  all_goals omega

set_option experimental.intrinsic true

/-- `drain` with an intrinsic termination measure. -/
def drainDecreasing (n : Nat) : Nat × Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0
    decreasing i
  do
    s := s + 1
    i := i - 1
  return (i, s)

/-- `vcgen` reads the measure from the program and takes the invariant from the tactic. -/
theorem drainDecreasing_eq_of_vcgen (n : Nat) : drainDecreasing n = (0, n) := by
  unfold drainDecreasing
  refine Id.of_run_eq_wp (P := fun r : Nat × Nat => r = (0, n)) rfl ?_
  vcgen invariants
    | inv1 => WhileInvariant.ofInvariantAndBreak (fun s : Nat × Nat => s.2 + s.1 = n)
        (fun s => s.1 = 0)
  all_goals simp_all
  all_goals omega

/-- `drain` with an intrinsic invariant that reads the `exit` flag. -/
def drainInvariant (n : Nat) : Nat × Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0
    invariant exit => s + i = n ∧ (exit = true → i = 0)
    decreasing i
  do
    s := s + 1
    i := i - 1
  return (i, s)

/-- The elaborated invariant binds `exit` with a `have`, which `vcgen`'s structural matcher
rejects; the loop lemmas still apply once the annotation is unfolded. -/
theorem drainInvariant_eq (n : Nat) : drainInvariant n = (0, n) := by
  unfold drainInvariant
  refine Id.of_run_eq_wp (P := fun r : Nat × Nat => r = (0, n)) rfl ?_
  fail_if_success vcgen
  simp only [Gadget.forInLoopWithInvariantAndVariant, wp, Prod.eta]
  apply Lean.Loop.idRun_forIn_of_measure (fun s : Nat × Nat => s.2 + s.1 = n)
    (fun s : Nat × Nat => s = (0, n)) (fun s : Nat × Nat => s.1) ?_ ?_
  · simp
  intro ⟨i, s⟩ (hinv : s + i = n)
  by_cases hi : 0 < i
  · simp only [gt_iff_lt, hi, ↓reduceIte, Id.run_pure]
    exact ⟨show s + 1 + (i - 1) = n by omega, show i - 1 < i by omega⟩
  · simp only [gt_iff_lt, hi, ↓reduceIte, Id.run_pure]
    show (i, s) = (0, n)
    rw [Prod.mk.injEq]
    omega

end PolyFunTest.LoopBridge
