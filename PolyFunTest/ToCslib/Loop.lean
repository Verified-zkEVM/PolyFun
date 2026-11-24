/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Control.ForIn
public import ToCslib.Control.Loop.Array
public import ToCslib.Control.Loop.While

/-!
# Canaries for the loop-to-fold layer

Each staged lemma of `ToCslib.Control.Loop.{Basic,While,Array}` and
`ToCslib.Data.{Array,ByteArray}` is instantiated on a small `Id.run do` program or a concrete
container, and the `loop_norm` simp set is run on programs as `do` elaborates them: a range loop,
an `if` inside a loop, nested loops over a pair state, and a loop over a byte array.
-/

@[expose] public section

namespace PolyFunTest.ToCslib.Loop

/-! ## Legacy ranges as lists -/

example (a b : Nat) : [a:b].size = b - a := Std.Legacy.Range.size_mk_one a b _

example : 3 ∈ [2:5] ∧ 5 ∉ [2:5] := by simp

example (a b i : Nat) (h : i ∈ List.range' a (b - a)) : a ≤ i ∧ i < b :=
  (Std.Legacy.Range.mem_mk_one_iff _).1 (Std.Legacy.Range.mem_of_mem_range'_sub h)

example (n i : Nat) (h : i ∈ List.range n) : i < n :=
  ((Std.Legacy.Range.mem_mk_one_iff _).1 (Std.Legacy.Range.mem_of_mem_range h)).2

example (a b : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    forIn [a:b] 0 f = forIn (List.range' a (b - a)) 0 f :=
  Std.Legacy.Range.forIn_eq_forIn_range'_sub a b 0 f

example (n : Nat) (f : Nat → Nat → Option (ForInStep Nat)) :
    forIn [0:n] 0 f = forIn (List.range n) 0 f :=
  Std.Legacy.Range.forIn_eq_forIn_range n 0 f

/-- A body that reads the bound its membership proof gives. -/
def boundedBody (b : Nat) (i : Nat) (hi : i < b) (acc : Nat) : Id (ForInStep Nat) :=
  pure (.yield (acc + (⟨i, hi⟩ : Fin b).val))

example (a b : Nat) :
    forIn' [a:b] 0 (fun i h acc => boundedBody b i h.upper acc) =
      forIn' (List.range' a (b - a)) 0 fun i h acc =>
        boundedBody b i (Std.Legacy.Range.mem_of_mem_range'_sub h).upper acc :=
  Std.Legacy.Range.forIn'_eq_forIn'_range'_sub a b 0 _

example (n : Nat) :
    forIn' [0:n] 0 (fun i h acc => boundedBody n i h.upper acc) =
      forIn' (List.range n) 0 fun i h acc =>
        boundedBody n i (Std.Legacy.Range.mem_of_mem_range h).upper acc :=
  Std.Legacy.Range.forIn'_eq_forIn'_range n 0 _

/-! ## Bodies that only yield -/

/-- The sum of the list, with a body that branches on membership-irrelevant data. -/
example (xs : List Nat) :
    forIn (m := Option) xs 0 (fun a b => pure (.yield (b + a))) = pure (xs.foldl (· + ·) 0) :=
  List.forIn_eq_pure_foldl (· + ·) fun _ _ _ => rfl

/-- A body that is a yield only on the elements of the list. -/
example (xs : List Nat) (h : ∀ a ∈ xs, a < 10) :
    Id.run (forIn xs 0 fun a b => if a < 10 then pure (.yield (b + a)) else pure (.done 0)) =
      xs.foldl (· + ·) 0 :=
  List.idRun_forIn_eq_foldl (· + ·) fun a ha b => by simp [h a ha]

example (xs : List Nat) :
    forIn' (m := Option) xs 0 (fun a _ b => pure (.yield (b + a))) = pure (xs.foldl (· + ·) 0) :=
  List.forIn'_eq_pure_foldl (· + ·) fun _ _ _ => rfl

example (xs : List Nat) :
    Id.run (forIn' xs 0 fun a _ b => pure (.yield (b + a))) = xs.foldl (· + ·) 0 :=
  List.idRun_forIn'_eq_foldl (· + ·) fun _ _ _ => rfl

example (a b : Nat) :
    forIn (m := Option) [a:b] 0 (fun i acc => pure (.yield (acc + i))) =
      pure ((List.range' a (b - a)).foldl (· + ·) 0) :=
  Std.Legacy.Range.forIn_eq_pure_foldl (· + ·) fun _ _ _ _ => rfl

/-- The body divides by the index, which the range keeps positive. -/
example (n : Nat) :
    Id.run (forIn [1:n] 0 fun i acc =>
      if i = 0 then pure (.done 0) else pure (.yield (acc + n / i))) =
      (List.range' 1 (n - 1)).foldl (fun acc i => acc + n / i) 0 :=
  Std.Legacy.Range.idRun_forIn_eq_foldl _ fun i hi _ acc => by simp [Nat.pos_iff_ne_zero.1 hi]

example (xs : Array Nat) :
    forIn (m := Option) xs 0 (fun a b => pure (.yield (b + a))) =
      pure (xs.toList.foldl (· + ·) 0) := by
  rw [Std.Internal.forIn_eq_pure_foldl_toList xs (· + ·) fun _ _ _ => rfl,
    Std.Internal.ForIn.toList_array]

example (v : Vector Nat 3) :
    Id.run (forIn v 0 fun a b => pure (.yield (b + a))) = v.toList.foldl (· + ·) 0 := by
  rw [Std.Internal.idRun_forIn_eq_foldl_toList v (· + ·) fun _ _ _ => rfl,
    Std.Internal.ForIn.toList_vector]

example (xs : Array Nat) :
    forIn' (m := Option) xs 0 (fun a _ b => pure (.yield (b + a))) =
      pure (xs.toList.foldl (· + ·) 0) := by
  rw [Std.Internal.forIn'_eq_pure_foldl_toList xs (· + ·) fun _ _ _ => rfl,
    Std.Internal.ForIn.toList_array]

/-! ## Congruence -/

example (xs : List Nat) (h : ∀ a ∈ xs, a ≠ 0) :
    forIn (m := Id) xs 0 (fun a b => if a = 0 then pure (.done b) else pure (.yield (b + a))) =
      forIn xs 0 fun a b => pure (.yield (b + a)) :=
  List.forIn_congr fun a ha b => by simp [h a ha]

example (n : Nat) :
    forIn (m := Id) [0:n] 0 (fun i b => if i < n then pure (.yield (b + i)) else pure (.done b)) =
      forIn [0:n] 0 fun i b => pure (.yield (b + i)) :=
  Std.Legacy.Range.forIn_congr fun i hi b => by simp [hi.upper]

example (xs : Array Nat) (h : ∀ a ∈ xs, a ≠ 0) :
    forIn (m := Id) xs 0 (fun a b => if a = 0 then pure (.done b) else pure (.yield (b + a))) =
      forIn xs 0 fun a b => pure (.yield (b + a)) :=
  Std.Internal.forIn_congr_toList xs fun a ha b => by
    simp [h a (by simpa using ha)]

/-! ## Concatenation -/

/-- A loop over a concatenation that stops in the first part never reaches the second. -/
example : Id.run (forIn ([1, 7] ++ [100]) 0 fun a b =>
    if a > 5 then pure (.done b) else pure (.yield (b + a))) = 1 := by
  rw [List.forIn_append]; rfl

example (xs ys : List Nat) :
    forIn (m := Id) (xs ++ ys) 0 (fun a b => pure (.yield (b + a))) =
      forIn xs 0 (fun a b => pure (.yield (b + a))) >>= fun b =>
        forIn ys b fun a b => pure (.yield (b + a)) :=
  List.forIn_append_of_yield xs ys 0 (fun a b => pure (b + a)) fun _ _ _ => rfl

/-! ## Folds through a sequence of states -/

example (xs : List Nat) : xs.foldl (fun n _ => n + 1) 0 = xs.length :=
  List.foldl_eq_of_trace (fun n _ => n + 1) id xs fun _ _ => rfl

/-- A fold over `5, 8, 11, …` that keeps the next element: the state after `i` steps is
`5 + 3 * i`. -/
example (n : Nat) : (List.range' 5 n 3).foldl (fun _ x => x + 3) 5 = 5 + 3 * n :=
  List.foldl_range'_eq_of_trace _ (fun i => 5 + 3 * i) 5 n 3 fun i _ => by omega

example (s n step cur : Nat) (pref suff : List Nat)
    (h : List.range' s n step = pref ++ cur :: suff) :
    cur = s + step * pref.length ∧ pref.length < n :=
  ⟨List.eq_add_mul_length_of_range'_eq_append_cons h, List.length_lt_of_range'_eq_append_cons h⟩

/-- The components of a pair state that do not read each other split into two folds. -/
example (xs : List Nat) (p : Nat × Bool) :
    (xs.foldl (fun q a => (q.1 + a, !q.2)) p).1 = xs.foldl (· + ·) p.1 ∧
      (xs.foldl (fun q a => (q.1 + a, !q.2)) p).2 = xs.foldl (fun b _ => !b) p.2 :=
  ⟨List.fst_foldl _ xs p fun _ _ => rfl, List.snd_foldl _ xs p fun _ _ => rfl⟩

/-! ## Normalization -/

example (c : Bool) (x y : Nat) :
    (if c then pure (ForInStep.yield x) else pure (ForInStep.yield y) : Id (ForInStep Nat)) =
      pure (.yield (if c then x else y)) :=
  ite_pure_yield _ x y

example (n : Nat) :
    (if h : 0 < n then pure (ForInStep.yield (⟨0, h⟩ : Fin n).val) else pure (ForInStep.yield n) :
      Option (ForInStep Nat)) = pure (.yield (if h : 0 < n then (⟨0, h⟩ : Fin n).val else n)) :=
  dite_pure_yield _ (fun h => (⟨0, h⟩ : Fin n).val) (fun _ => n)

/-- Push the indices of a range. -/
def rangeArray (n : Nat) : Array Nat := Id.run do
  let mut a := #[]
  for i in [0:n] do
    a := a.push i
  return a

example (n : Nat) : rangeArray n = (List.range n).foldl (fun a i => a.push i) #[] := by
  simp only [rangeArray, loop_norm]

/-- Sum the even indices of a range, with an `if` in the body. -/
def sumEven (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [2:n] do
    if i % 2 = 0 then s := s + i
  return s

example (n : Nat) :
    sumEven n = (List.range' 2 (n - 2)).foldl (fun s i => if i % 2 = 0 then s + i else s) 0 := by
  simp only [sumEven, loop_norm]

/-- Two nested loops over a pair state: write into an array and count the writes. -/
def fillCount (k n : Nat) : Array Nat × Nat := Id.run do
  let mut a := Array.replicate (k * n) 0
  let mut c := 0
  for i in [0:k] do
    for j in [0:n] do
      a := a.set! (i * n + j) (i + j)
      c := c + 1
  return (a, c)

example (k n : Nat) :
    fillCount k n = (Array.ofFn fun t : Fin (k * n) => t / n + t % n, k * n) := by
  simp only [fillCount, loop_norm]
  refine Prod.ext ?_ ?_
  · simp only [loop_norm]
    exact Array.foldl_foldl_set!_range_eq_ofFn (fun i j => i + j) (by simp)
  · simp only [loop_norm]
    simp [Nat.mul_comm]

/-! ## `while` loops -/

/-- Halve until one remains, counting the steps. -/
def halvings (n : Nat) : Nat × Nat := Id.run do
  let mut x := n
  let mut k := 0
  while x > 1 do
    x := x / 2
    k := k + 1
  return (x, k)

example : halvings 8 = (1, 3) := by
  simp only [halvings, Id.run_bind, Id.run_pure, Prod.eta]
  exact congrArg Id.run (Lean.Loop.forIn_eq_of_trace (n := 3) (fun i => (8 / 2 ^ i, i))
    (fun i hi => match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl) rfl)

/-- The final value is at most one, by the measure `x`. -/
example (n : Nat) : (halvings n).1 ≤ 1 := by
  simp only [halvings, Id.run_bind, Id.run_pure]
  apply Lean.Loop.idRun_forIn_of_measure (fun _ => True) (fun s : Nat × Nat => s.1 ≤ 1)
    (fun s : Nat × Nat => s.1) trivial
  intro ⟨x, k⟩ _
  by_cases hx : 1 < x
  · simp only [gt_iff_lt, hx, ↓reduceIte]
    exact ⟨trivial, Nat.div_lt_self (by omega) (by decide)⟩
  · simp only [gt_iff_lt, hx, ↓reduceIte]
    exact Nat.le_of_not_lt hx

/-! ## Arrays -/

example (xs : Array Nat) (i j d v : Nat) :
    (xs.set! i v).getD j d = if i = j ∧ i < xs.size then v else xs.getD j d :=
  Array.getD_set!

example (xs : Array Nat) (i j d v : Nat) :
    (xs.setIfInBounds i v).getD j d = if i = j ∧ i < xs.size then v else xs.getD j d :=
  Array.getD_setIfInBounds

example (xs : Array Nat) (j d v : Nat) :
    (xs.push v).getD j d = if j = xs.size then v else xs.getD j d :=
  Array.getD_push

example (xs : Array Nat) (i j v : Nat) (h : i ≠ j) : (xs.set! i v)[j]! = xs[j]! := by simp [h]

example (xs : Array Nat) (i j v : Nat) :
    (xs.setIfInBounds i v)[j]! = if i = j ∧ i < xs.size then v else xs[j]! :=
  Array.getElem!_setIfInBounds

example (xs : Array Nat) (j v : Nat) (h : j < xs.size) : (xs.push v)[j]! = xs[j]! := by simp [h]

example (xs : Array Nat) (j v : Nat) : (xs.push v)[j]! = if j = xs.size then v else xs[j]! :=
  Array.getElem!_push

example (xs : Array Nat) (j d v : Nat) (h : j < xs.size) :
    (xs.push v)[j]? = xs[j]? ∧ (xs.push v).getD j d = xs.getD j d := by
  simp [h]

/-! ## Byte arrays -/

example (b : ByteArray) (i j : Nat) (v : UInt8) :
    (b.set! i v)[j]? = if i = j then if i < b.size then some v else none else b[j]? :=
  ByteArray.getElem?_set!

example (b : ByteArray) (i j : Nat) (v : UInt8) (hi : i < b.size) (hij : i ≠ j) :
    (b.set! i v)[i]? = some v ∧ (b.set! i v)[j]? = b[j]? := by
  simp [hi, hij]

example (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.push v)[j]? = if j = b.size then some v else b[j]? :=
  ByteArray.getElem?_push

example (b : ByteArray) (j : Nat) (v : UInt8) (h : j < b.size) :
    (b.push v)[b.size]? = some v ∧ (b.push v)[j]? = b[j]? ∧ (b.push v)[j]! = b[j]! :=
  ⟨ByteArray.getElem?_push_size, ByteArray.getElem?_push_lt h, by simp [h]⟩

example : ByteArray.toList ⟨#[1, 2, 3]⟩ = [1, 2, 3] := by
  rw [ByteArray.toList_eq_data_toList]

example (b : ByteArray) (f : UInt8 → Nat → Option (ForInStep Nat)) :
    forIn b 0 f = forIn b.data 0 f :=
  ByteArray.forIn_eq_forIn_data b 0 f

example (b : ByteArray) (f : UInt8 → Nat → Option (ForInStep Nat)) :
    forIn b 0 f = forIn b.toList 0 f :=
  ByteArray.forIn_eq_forIn_toList b 0 f

example (b : ByteArray) : ForIn.toList b = b.toList := Std.Internal.ForIn.toList_byteArray b

example : Std.Internal.PureForIn Option ByteArray UInt8 := inferInstance

/-- The loop visits the bytes in increasing order. -/
example : Id.run (forIn (⟨#[1, 2, 3]⟩ : ByteArray) [] fun x acc => pure (.yield (x :: acc))) =
    [3, 2, 1] := by
  decide

/-- Sum the bytes; `loop_norm` turns the byte loop into a fold over its list. -/
def byteSum (b : ByteArray) : Nat := Id.run do
  let mut s := 0
  for x in b do
    s := s + x.toNat
  return s

example (b : ByteArray) : byteSum b = b.toList.foldl (fun s x => s + x.toNat) 0 := by
  simp only [byteSum, loop_norm]

/-! ## Fills -/

example (l : List Nat) (a : Array Nat) :
    (l.foldl (fun a x => a.set! (2 * x) x) a).size = a.size := by
  simp

/-- Writing at even positions leaves the odd ones alone. -/
example (l : List Nat) (a : Array Nat) (j : Nat) (hj : j % 2 = 1) :
    (l.foldl (fun a x => a.set! (2 * x) x) a)[j]? = a[j]? :=
  Array.getElem?_foldl_set!_of_forall_ne _ a fun x _ hx => by omega

example (a : Array Nat) (ha : 6 ≤ a.size) :
    ([0, 1, 2].foldl (fun a x => a.set! (2 * x) (x + 10)) a)[4]? = some 12 :=
  Array.getElem?_foldl_set!_of_mem (p := fun x => 2 * x) (x := 2) (fun x => x + 10) a
    (by decide) (by simp) (by simp; omega)

example (n : Nat) :
    (List.range n).foldl (fun a i => a.set! i (i * i)) (Array.replicate n 0) =
      Array.ofFn fun i : Fin n => i.val * i.val :=
  Array.foldl_set!_range_eq_ofFn (fun i => i * i) (by simp)

example (k n : Nat) (a : Array Nat) (ha : a.size = k * n) :
    (List.range k).foldl
        (fun a i => (List.range n).foldl (fun a j => a.set! (i * n + j) (i * j)) a) a =
      Array.ofFn fun t : Fin (k * n) => t / n * (t % n) :=
  Array.foldl_foldl_set!_range_eq_ofFn (fun i j => i * j) ha

/-! ## Builders -/

example (n : Nat) : List.range' 0 n = List.range n := List.range'_zero_eq_range n

example (l : List Nat) (acc : Array Nat) :
    l.foldl (fun acc x => acc ++ (List.replicate x x).toArray) acc =
      acc ++ (l.flatMap fun x => List.replicate x x).toArray :=
  List.foldl_append_toArray_eq_append l _ acc

/-- The shape of a bit packer: for each value, push its low `w` bits. -/
example (vals : List Nat) (w : Nat) :
    vals.foldl (fun acc v => (List.range w).foldl (fun acc bit => acc.push (v / 2 ^ bit % 2)) acc)
      #[] = (vals.flatMap fun v => (List.range w).map fun bit => v / 2 ^ bit % 2).toArray := by
  rw [List.foldl_foldl_push_eq_append vals (fun _ => List.range w), Array.empty_append]

/-- The same packer as nested `for` loops over ranges. -/
def packBits (vals : Array Nat) (w : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for i in [0:vals.size] do
    let v := vals.getD i 0
    for bit in [0:w] do
      acc := acc.push ((v / 2 ^ bit) % 2)
  return acc

example (vals : Array Nat) (w : Nat) :
    packBits vals w = ((List.range vals.size).flatMap fun i =>
      (List.range w).map fun bit => vals.getD i 0 / 2 ^ bit % 2).toArray := by
  simp only [packBits, loop_norm]
  rw [List.foldl_foldl_push_eq_append (List.range vals.size) (fun _ => List.range w)
    (fun i bit => vals.getD i 0 / 2 ^ bit % 2), Array.empty_append]

example (l : List UInt8) (acc : ByteArray) :
    l.foldl (fun acc x => acc.push (x + 1)) acc = acc ++ (l.map (· + 1)).toByteArray :=
  ByteArray.foldl_push_eq_append l _ acc

example (l : List Nat) (g : Nat → ByteArray) (acc : ByteArray) :
    l.foldl (fun acc x => acc ++ g x) acc = acc ++ (l.flatMap fun x => (g x).toList).toByteArray :=
  ByteArray.foldl_append_eq_append l g acc

end PolyFunTest.ToCslib.Loop
