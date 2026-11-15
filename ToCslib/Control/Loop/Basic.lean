/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Control.Loop.Attr
public import Std.Internal.ForIn.Lemmas
public import Init.Data.Range.Lemmas

/-!
# Effect-free loops as folds

`Id.run do` code elaborates its `for` loops to `forIn` over the iterated container, with the
mutable variables as the loop state. This module relates such loops to folds over lists, so that
imperative code can be compared with a functional specification by rewriting.

* A legacy range `[a:b]` iterates over `List.range' a (b - a)`, and `[0:n]` over `List.range n`
  (`Std.Legacy.Range.forIn_eq_forIn_range'_sub`, `Std.Legacy.Range.forIn_eq_forIn_range`, and
  their `forIn'` twins). Core states the general case with `Std.Legacy.Range.size`.
* A body that only yields is a left fold: `List.forIn_eq_pure_foldl` and
  `List.idRun_forIn_eq_foldl` take the yield equation as a hypothesis on the elements of the
  list, so the body may use facts about the index. `Std.Internal.forIn_eq_pure_foldl_toList`
  extends them to every container with a `Std.Internal.PureForIn` instance (arrays, ranges,
  slices, `Option`, `Vector`, …). Core's `List.forIn_pure_yield_eq_foldl` covers the bodies that
  are syntactically `pure (.yield _)`.
* Two loops agree when their bodies agree on the iterated elements (`List.forIn_congr`,
  `Std.Internal.forIn_congr_toList`, `Std.Legacy.Range.forIn_congr`).
* A loop over `xs ++ ys` runs `ys` from where `xs` stopped (`List.forIn_append`), and from the
  state `xs` returns when `xs` never stops early (`List.forIn_append_of_yield`).
* A fold through a prescribed sequence of states ends in the last state
  (`List.foldl_eq_of_trace`, `List.foldl_range'_eq_of_trace`).
* A fold over a pair state whose components do not read each other splits into two folds
  (`List.fst_foldl`, `List.snd_foldl`); the side condition holds by `simp` for the tuples that
  `do` threads through a loop with several mutable variables.
* The verification conditions of a loop over a range decompose `List.range' s n step` as
  `pref ++ cur :: suff`; `List.eq_add_mul_length_of_range'_eq_append_cons` and
  `List.length_lt_of_range'_eq_append_cons` recover the index.

The `loop_norm` simp set collects these rewrites with core's and the monad laws that expose a
yield-only body; `simp only [loop_norm]` turns most `Id.run do` loops with yield-only bodies into
`List.foldl`.
-/

public section

universe u v u₁ w

variable {m : Type u → Type v} {α : Type u₁} {β : Type u}

/-! ## Legacy ranges as lists -/

namespace Std.Legacy.Range

/-- A range with unit step has `stop - start` elements. -/
@[loop_norm]
theorem size_mk_one (a b : Nat) (h : 0 < 1) :
    ({ start := a, stop := b, step := 1, step_pos := h } : Range).size = b - a := by
  simp only [size, Nat.add_sub_cancel, Nat.div_one]

/-- Membership in a range with unit step. -/
@[simp]
theorem mem_mk_one_iff {a b i : Nat} (h : 0 < 1) :
    i ∈ ({ start := a, stop := b, step := 1, step_pos := h } : Range) ↔ a ≤ i ∧ i < b := by
  refine ⟨fun hi => ⟨hi.lower, hi.upper⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂, Nat.mod_one _⟩⟩

theorem mem_of_mem_range'_sub {a b i : Nat} (h : i ∈ List.range' a (b - a)) : i ∈ [a:b] := by
  rw [List.mem_range'_1] at h
  exact (mem_mk_one_iff _).2 ⟨h.1, by omega⟩

theorem mem_of_mem_range {n i : Nat} (h : i ∈ List.range n) : i ∈ [0:n] :=
  (mem_mk_one_iff _).2 ⟨Nat.zero_le _, List.mem_range.1 h⟩

/-- A `for` loop over `[a:b]` is the loop over `List.range' a (b - a)`. -/
theorem forIn_eq_forIn_range'_sub [Monad m] (a b : Nat) (init : β)
    (f : Nat → β → m (ForInStep β)) :
    forIn [a:b] init f = forIn (List.range' a (b - a)) init f := by
  rw [forIn_eq_forIn_range', size_mk_one]

/-- A `for` loop over `[0:n]` is the loop over `List.range n`. -/
theorem forIn_eq_forIn_range [Monad m] (n : Nat) (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn [0:n] init f = forIn (List.range n) init f := by
  rw [forIn_eq_forIn_range'_sub, Nat.sub_zero, List.range_eq_range']

/-- The `forIn'` twin of `forIn_eq_forIn_range'_sub`. -/
theorem forIn'_eq_forIn'_range'_sub [Monad m] (a b : Nat) (init : β)
    (f : (i : Nat) → i ∈ [a:b] → β → m (ForInStep β)) :
    forIn' [a:b] init f =
      forIn' (List.range' a (b - a)) init fun i h acc => f i (mem_of_mem_range'_sub h) acc := by
  rw [forIn'_eq_forIn'_range']
  exact List.forIn'_congr (by rw [size_mk_one]) rfl fun _ _ _ => rfl

/-- The `forIn'` twin of `forIn_eq_forIn_range`. -/
theorem forIn'_eq_forIn'_range [Monad m] (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ [0:n] → β → m (ForInStep β)) :
    forIn' [0:n] init f =
      forIn' (List.range n) init fun i h acc => f i (mem_of_mem_range h) acc := by
  rw [forIn'_eq_forIn'_range'_sub]
  exact List.forIn'_congr (by rw [Nat.sub_zero, List.range_eq_range']) rfl fun _ _ _ => rfl

end Std.Legacy.Range

/-! ## Bodies that only yield -/

namespace List

/-- A loop whose body yields `g b a` on every element `a` of the list is the left fold of `g`. -/
theorem forIn_eq_pure_foldl [Monad m] [LawfulMonad m] {xs : List α} {init : β}
    {f : α → β → m (ForInStep β)} (g : β → α → β)
    (h : ∀ a ∈ xs, ∀ b, f a b = pure (.yield (g b a))) :
    forIn xs init f = pure (xs.foldl g init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [forIn_cons, h x mem_cons_self, pure_bind, foldl_cons]
    exact ih fun a ha => h a (mem_cons_of_mem x ha)

/-- `forIn_eq_pure_foldl` read through `Id.run`. -/
theorem idRun_forIn_eq_foldl {xs : List α} {init : β} {f : α → β → Id (ForInStep β)}
    (g : β → α → β) (h : ∀ a ∈ xs, ∀ b, f a b = pure (.yield (g b a))) :
    Id.run (forIn xs init f) = xs.foldl g init := by
  rw [forIn_eq_pure_foldl g h, Id.run_pure]

/-- The `forIn'` twin of `forIn_eq_pure_foldl`, for a body that does not use the membership proof
in its result. -/
theorem forIn'_eq_pure_foldl [Monad m] [LawfulMonad m] {xs : List α} {init : β}
    {f : (a : α) → a ∈ xs → β → m (ForInStep β)} (g : β → α → β)
    (h : ∀ a (ha : a ∈ xs) b, f a ha b = pure (.yield (g b a))) :
    forIn' xs init f = pure (xs.foldl g init) := by
  rw [forIn'_eq_forIn xs init f (fun a b => pure (.yield (g b a))) h]
  exact forIn_eq_pure_foldl g fun _ _ _ => rfl

/-- `forIn'_eq_pure_foldl` read through `Id.run`. -/
theorem idRun_forIn'_eq_foldl {xs : List α} {init : β}
    {f : (a : α) → a ∈ xs → β → Id (ForInStep β)} (g : β → α → β)
    (h : ∀ a (ha : a ∈ xs) b, f a ha b = pure (.yield (g b a))) :
    Id.run (forIn' xs init f) = xs.foldl g init := by
  rw [forIn'_eq_pure_foldl g h, Id.run_pure]

/-! ## Congruence -/

/-- Two loops over a list agree when their bodies agree on its elements. -/
theorem forIn_congr [Monad m] {xs : List α} {init : β} {f g : α → β → m (ForInStep β)}
    (h : ∀ a ∈ xs, ∀ b, f a b = g a b) : forIn xs init f = forIn xs init g := by
  rw [← forIn'_eq_forIn xs init (fun a _ b => f a b) f fun _ _ _ => rfl,
    ← forIn'_eq_forIn xs init (fun a _ b => g a b) g fun _ _ _ => rfl]
  exact forIn'_congr rfl rfl fun a ha b => h a ha b

/-! ## Concatenation -/

/-- A loop over `xs ++ ys` runs the loop over `xs`, as the fold of `List.forIn_eq_foldlM`, and
continues over `ys` unless that fold stopped. -/
theorem forIn_append [Monad m] [LawfulMonad m] (xs ys : List α) (init : β)
    (f : α → β → m (ForInStep β)) :
    forIn (xs ++ ys) init f = (do
      let r ← xs.foldlM (fun r a => match r with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init)
      match r with
      | .yield b => forIn ys b f
      | .done b => pure b) := by
  rw [forIn_eq_foldlM, foldlM_append, map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | yield b => exact (forIn_eq_foldlM f b).symm
  | done b =>
    dsimp only
    induction ys with
    | nil => simp
    | cons y ys ih => simpa using ih

/-- When the body only yields on `xs`, a loop over `xs ++ ys` is the loop over `ys` started from
the state the loop over `xs` returns. -/
theorem forIn_append_of_yield [Monad m] [LawfulMonad m] (xs ys : List α) (init : β)
    {f : α → β → m (ForInStep β)} (g : α → β → m β)
    (h : ∀ a ∈ xs, ∀ b, f a b = ForInStep.yield <$> g a b) :
    forIn (xs ++ ys) init f = forIn xs init f >>= fun b => forIn ys b f := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, forIn_cons, h x mem_cons_self, bind_map_left, bind_assoc]
    exact bind_congr fun b => ih b fun a ha => h a (mem_cons_of_mem x ha)

/-! ## Folds through a sequence of states -/

/-- A left fold whose `i`-th step takes the state `S i` to `S (i + 1)` ends in
`S xs.length`. -/
theorem foldl_eq_of_trace {γ : Type w} (step : γ → α → γ) (S : Nat → γ) (xs : List α)
    (h : ∀ i (hi : i < xs.length), step (S i) xs[i] = S (i + 1)) :
    xs.foldl step (S 0) = S xs.length := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    have h₀ : step (S 0) x = S 1 := h 0 (Nat.zero_lt_succ _)
    rw [foldl_cons, h₀]
    exact ih (fun i => S (i + 1)) fun i hi => h (i + 1) (Nat.succ_lt_succ hi)

/-- A left fold over `List.range' s n k` whose step at `s + k * i` takes `S i` to `S (i + 1)`
ends in `S n`. -/
theorem foldl_range'_eq_of_trace {γ : Type w} (step : γ → Nat → γ) (S : Nat → γ) (s n k : Nat)
    (h : ∀ i < n, step (S i) (s + k * i) = S (i + 1)) :
    (List.range' s n k).foldl step (S 0) = S n := by
  have := foldl_eq_of_trace step S (List.range' s n k) fun i hi => by
    rw [getElem_range']; exact h i (by simpa using hi)
  simpa using this

/-- The first component of a left fold over pairs, when the first component of each step does not
depend on the second component of the state, is the fold of the first components. -/
@[loop_norm]
theorem fst_foldl {γ : Type w} {δ : Type v} (F : γ × δ → α → γ × δ) (xs : List α) (p : γ × δ)
    (h : ∀ q a, (F q a).1 = (F (q.1, p.2) a).1) :
    (xs.foldl F p).1 = xs.foldl (fun c a => (F (c, p.2) a).1) p.1 := by
  suffices ∀ q : γ × δ, (xs.foldl F q).1 = xs.foldl (fun c a => (F (c, p.2) a).1) q.1 from this p
  induction xs with
  | nil => intro q; rfl
  | cons x xs ih => intro q; rw [foldl_cons, ih, foldl_cons, h]

/-- The second component of a left fold over pairs, when the second component of each step does
not depend on the first component of the state, is the fold of the second components. -/
@[loop_norm]
theorem snd_foldl {γ : Type w} {δ : Type v} (F : γ × δ → α → γ × δ) (xs : List α) (p : γ × δ)
    (h : ∀ q a, (F q a).2 = (F (p.1, q.2) a).2) :
    (xs.foldl F p).2 = xs.foldl (fun c a => (F (p.1, c) a).2) p.2 := by
  suffices ∀ q : γ × δ, (xs.foldl F q).2 = xs.foldl (fun c a => (F (p.1, c) a).2) q.2 from this p
  induction xs with
  | nil => intro q; rfl
  | cons x xs ih => intro q; rw [foldl_cons, ih, foldl_cons, h]

/-- The element at position `pref.length` of `List.range' s n step` is `s + step * pref.length`,
as the verification conditions of a loop over a range need. -/
theorem eq_add_mul_length_of_range'_eq_append_cons {s n step cur : Nat} {pref suff : List Nat}
    (h : range' s n step = pref ++ cur :: suff) : cur = s + step * pref.length := by
  obtain ⟨k, -, hpref, hsuff⟩ := range'_eq_append_iff.1 h
  obtain ⟨hs, -, -⟩ := range'_eq_cons_iff.1 hsuff.symm
  rw [hpref, length_range', ← hs, Nat.mul_comm]

/-- A decomposition `List.range' s n step = pref ++ cur :: suff` has `pref.length < n`. -/
theorem length_lt_of_range'_eq_append_cons {s n step cur : Nat} {pref suff : List Nat}
    (h : range' s n step = pref ++ cur :: suff) : pref.length < n := by
  have := congrArg length h
  simp only [length_range', length_append, length_cons] at this
  omega

end List

namespace Std.Legacy.Range

/-- A loop over `[a:b]` whose body yields `g acc i` at every index `a ≤ i < b` is the left fold
of `g` over `List.range' a (b - a)`. -/
theorem forIn_eq_pure_foldl [Monad m] [LawfulMonad m] {a b : Nat} {init : β}
    {f : Nat → β → m (ForInStep β)} (g : β → Nat → β)
    (h : ∀ i, a ≤ i → i < b → ∀ acc, f i acc = pure (.yield (g acc i))) :
    forIn [a:b] init f = pure ((List.range' a (b - a)).foldl g init) := by
  rw [forIn_eq_forIn_range'_sub]
  refine List.forIn_eq_pure_foldl g fun i hi acc => ?_
  rw [List.mem_range'_1] at hi
  exact h i hi.1 (by omega) acc

/-- `forIn_eq_pure_foldl` read through `Id.run`. -/
theorem idRun_forIn_eq_foldl {a b : Nat} {init : β} {f : Nat → β → Id (ForInStep β)}
    (g : β → Nat → β) (h : ∀ i, a ≤ i → i < b → ∀ acc, f i acc = pure (.yield (g acc i))) :
    Id.run (forIn [a:b] init f) = (List.range' a (b - a)).foldl g init := by
  rw [forIn_eq_pure_foldl g h, Id.run_pure]

/-- Two loops over a range agree when their bodies agree on its members. -/
theorem forIn_congr [Monad m] {r : Range} {init : β} {f g : Nat → β → m (ForInStep β)}
    (h : ∀ i ∈ r, ∀ acc, f i acc = g i acc) : forIn r init f = forIn r init g := by
  rw [forIn_eq_forIn_range', forIn_eq_forIn_range']
  exact List.forIn_congr fun i hi acc => h i (mem_of_mem_range' hi) acc

end Std.Legacy.Range

/-! ## Containers iterating over a list -/

namespace Std.Internal

variable {ρ : Type w}

/-- `List.forIn_eq_pure_foldl` for every container whose loop is the loop over
`ForIn.toList`. -/
theorem forIn_eq_pure_foldl_toList [Monad m] [LawfulMonad m] [ForIn m ρ α] [ForIn Id ρ α]
    [PureForIn m ρ α] (xs : ρ) {init : β} {f : α → β → m (ForInStep β)} (g : β → α → β)
    (h : ∀ a ∈ ForIn.toList xs, ∀ b, f a b = pure (.yield (g b a))) :
    forIn xs init f = pure ((ForIn.toList xs).foldl g init) := by
  rw [PureForIn.forIn_eq]
  exact List.forIn_eq_pure_foldl g h

/-- `forIn_eq_pure_foldl_toList` read through `Id.run`. -/
theorem idRun_forIn_eq_foldl_toList [ForIn Id.{u} ρ α] [ForIn Id.{u₁} ρ α] [PureForIn Id.{u} ρ α]
    (xs : ρ) {init : β}
    {f : α → β → Id (ForInStep β)} (g : β → α → β)
    (h : ∀ a ∈ ForIn.toList xs, ∀ b, f a b = pure (.yield (g b a))) :
    Id.run (forIn xs init f) = (ForIn.toList xs).foldl g init := by
  rw [forIn_eq_pure_foldl_toList xs g h, Id.run_pure]

/-- The `forIn'` twin of `forIn_eq_pure_foldl_toList`, for a body that does not use the
membership proof in its result. -/
theorem forIn'_eq_pure_foldl_toList [Monad m] [LawfulMonad m] {d : Membership α ρ}
    [ForIn' m ρ α d] [ForIn Id ρ α] [LawfulMemForInId ρ α] [PureForIn' m ρ α] (xs : ρ)
    {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)} (g : β → α → β)
    (h : ∀ a (ha : a ∈ xs) b, f a ha b = pure (.yield (g b a))) :
    forIn' xs init f = pure ((ForIn.toList xs).foldl g init) := by
  rw [PureForIn'.forIn'_eq]
  exact List.forIn'_eq_pure_foldl g fun a ha b => h a _ b

/-- Two loops over a container that iterates over `ForIn.toList` agree when their bodies agree on
its elements. -/
theorem forIn_congr_toList [Monad m] [ForIn m ρ α] [ForIn Id ρ α] [PureForIn m ρ α] (xs : ρ)
    {init : β} {f g : α → β → m (ForInStep β)}
    (h : ∀ a ∈ ForIn.toList xs, ∀ b, f a b = g a b) : forIn xs init f = forIn xs init g := by
  rw [PureForIn.forIn_eq (m := m) xs init f, PureForIn.forIn_eq (m := m) xs init g]
  exact List.forIn_congr h

end Std.Internal

/-! ## Normalization -/

/-- Both branches of an `if` that yield, as one yield of the `if`. -/
@[loop_norm]
theorem ite_pure_yield [Pure m] (c : Prop) [Decidable c] (x y : β) :
    (if c then pure (ForInStep.yield x) else pure (ForInStep.yield y) : m (ForInStep β)) =
      pure (.yield (if c then x else y)) := by
  split <;> rfl

/-- The dependent twin of `ite_pure_yield`. -/
@[loop_norm]
theorem dite_pure_yield [Pure m] (c : Prop) [Decidable c] (x : c → β) (y : ¬c → β) :
    (if h : c then pure (ForInStep.yield (x h)) else pure (ForInStep.yield (y h)) :
      m (ForInStep β)) = pure (.yield (if h : c then x h else y h)) := by
  split <;> rfl

attribute [loop_norm] Id.run_pure Id.run_bind Id.run_map pure_bind bind_pure bind_pure_comp
  map_pure Nat.sub_zero Prod.eta implies_true Std.Legacy.Range.forIn_eq_forIn_range'
  Std.Legacy.Range.forIn'_eq_forIn'_range' List.forIn_pure_yield_eq_foldl
  List.forIn_yield_eq_foldlM List.idRun_forIn_yield_eq_foldl List.forIn'_pure_yield_eq_foldl
  Array.forIn_pure_yield_eq_foldl Array.idRun_forIn_yield_eq_foldl
