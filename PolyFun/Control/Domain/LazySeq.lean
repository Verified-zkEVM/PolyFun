/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result
public import Mathlib.Data.ENat.Basic

/-!
# Lazy sequences of static length

A lazy language's sequence is a stream of suspended elements behind one suspension,
`LazySeq ε X = DomainResult ε (ℕ → DomainResult ε X)`. Its length is static: the language reads
it from the type, never from the stream, and it may be infinite (`n : ℕ∞`). Every operation
that builds a sequence writes bottom at and past that length (it *masks*), so the positions that
no program observes carry no information. Two masked sequences are equal exactly when their
elements below the length are.

* `LazySeq.index i` demands the spine, then element `i`.
* `LazySeq.mk n` returns a stream masked at `n`. Its spine is available before any element is
  demanded (`LazySeq.spine_mk`).
* `LazySeq.ofFn n` reads `n` elements by structural recursion, `(List.ofFn xs).getD j ⊥`, so at a
  concrete length the kernel evaluates each element at a closed index.
* `LazySeq.map` and `zipWith` demand the spines of their operands, then return a masked stream
  whose elements combine the operands' elements lazily.
* `LazySeq.reindex` and `append` return a masked stream at once. Reading one of its elements
  demands the spine of the source it reads from, then one element of that source.
* `LazySeq.encList enc xs` is a native list as a lazy sequence. On these encodings the
  operations compute the corresponding `List` operations (`map_encList`, `zipWith_encList`,
  `reindex_id_encList` for `List.take`, `reindex_add_encList` for `List.drop`, and
  `append_encList`).
* `LazySeq.decode n dec` reads a sequence of length `n` as a native family. It demands the spine,
  then the elements from left to right, and reads no position at or past `n`. It decodes above
  `encList` whenever `dec` decodes above `enc` (`DomainResult.DecodesAbove.lazySeq`).
* `LazySeq.spine` demands only the spine, and `LazySeq.forceSteps` forces a run of elements from
  left to right.

`LazySeq.below n i` decides `i < n` on `ℕ∞` by cases, so masking computes. Recursive streams and
their productivity are in `PolyFun.Control.Domain.PrefixRecursion`.
-/

public section

open OmegaCompletePartialOrder
open DomainResult (value error bindPlain)

/-- Lazy sequences: a stream of suspended elements behind one suspension. The stream does not
store a length; each operation takes the static length as an argument. -/
abbrev LazySeq (ε X : Type*) := DomainResult ε (ℕ → DomainResult ε X)

namespace LazySeq

/-! ## Positions below a length -/

/-- `i < n`, decided by cases on `ℕ∞`: every position is below `⊤`. -/
@[expose] def below : ℕ∞ → ℕ → Bool
  | none, _ => true
  | some n, i => decide (i < n)

@[simp] theorem below_natCast (n i : ℕ) : below n i = decide (i < n) := rfl

@[simp] theorem below_top (i : ℕ) : below ⊤ i = true := rfl

@[simp] theorem below_zero (i : ℕ) : below 0 i = false := rfl

@[simp] theorem below_one (i : ℕ) : below 1 i = decide (i < 1) := rfl

@[simp] theorem below_ofNat (n i : ℕ) [n.AtLeastTwo] :
    below ofNat(n) i = decide (i < OfNat.ofNat n) := rfl

/-- `below` decides the order of `ℕ∞`. -/
theorem below_eq_true_iff {n : ℕ∞} {i : ℕ} : below n i = true ↔ (i : ℕ∞) < n := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n => rw [below_natCast, decide_eq_true_iff, ENat.natCast_lt_natCast]

/-- Positions before a position below `n` are below `n`. -/
theorem below_of_lt {n : ℕ∞} {i j : ℕ} (hi : below n i) (hj : j < i) : below n j := by
  induction n using ENat.recTopCoe with
  | top => rfl
  | coe n =>
    simp only [below_natCast, decide_eq_true_eq] at hi ⊢
    omega

/-! ## Construction and indexing -/

section Continuous

variable {ε X : Type*} [OmegaCompletePartialOrder X]

/-- Read element `i`: demand the spine, then the element. -/
@[expose] noncomputable def index (i : ℕ) : LazySeq ε X →𝒄 DomainResult ε X :=
  DomainResult.bind (.ofFun fun xs : ℕ → DomainResult ε X => xs i)

@[simp] theorem index_value (i : ℕ) (xs : ℕ → DomainResult ε X) :
    index i (value xs : LazySeq ε X) = xs i := rfl

@[simp] theorem index_bot (i : ℕ) : index i (⊥ : LazySeq ε X) = ⊥ := rfl

@[simp] theorem index_error (i : ℕ) (e : ε) : index i (error e : LazySeq ε X) = error e := rfl

/-- Bottom at and past `n`. -/
@[expose] noncomputable def mask (n : ℕ∞) :
    (ℕ → DomainResult ε X) →𝒄 (ℕ → DomainResult ε X) :=
  .ofFun (fun xs i => if below n i then xs i else ⊥) (by
    apply ωScottContinuous.of_apply₂
    intro i
    cases below n i
    · exact ωScottContinuous.const
    · exact ωScottContinuous.apply i)

theorem mask_apply (n : ℕ∞) (xs : ℕ → DomainResult ε X) (i : ℕ) :
    mask n xs i = if below n i then xs i else ⊥ := rfl

/-- A stream masked at `n`, as a sequence whose spine is available at once. -/
@[expose] noncomputable def mk (n : ℕ∞) : (ℕ → DomainResult ε X) →𝒄 LazySeq ε X :=
  DomainResult.valueContinuous.comp (mask n)

theorem mk_apply (n : ℕ∞) (xs : ℕ → DomainResult ε X) :
    mk n xs = value fun i => if below n i then xs i else ⊥ := rfl

theorem index_mk (n : ℕ∞) (xs : ℕ → DomainResult ε X) (i : ℕ) :
    index i (mk n xs) = if below n i then xs i else ⊥ := rfl

@[simp] theorem index_mk_of_below {n : ℕ∞} (xs : ℕ → DomainResult ε X) {i : ℕ}
    (hi : below n i) : index i (mk n xs) = xs i := by
  simp [index_mk, hi]

@[simp] theorem index_mk_of_not_below {n : ℕ∞} (xs : ℕ → DomainResult ε X) {i : ℕ}
    (hi : below n i = false) : index i (mk n xs) = ⊥ := by
  simp [index_mk, hi]

/-- The elements of a list, then bottom. -/
@[expose] noncomputable def elems {E : Type*} [OmegaCompletePartialOrder E] [OrderBot E]
    (n : ℕ) : (Fin n → E) →𝒄 (ℕ → E) :=
  .ofFun (fun xs j => (List.ofFn xs).getD j ⊥) (by
    apply ωScottContinuous.of_apply₂
    intro j
    by_cases h : j < n
    · have : (fun xs : Fin n → E => (List.ofFn xs).getD j ⊥) = fun xs => xs ⟨j, h⟩ := by
        funext xs
        simp [h]
      rw [this]
      exact ωScottContinuous.apply _
    · have : (fun xs : Fin n → E => (List.ofFn xs).getD j ⊥) = fun _ => ⊥ := by
        funext xs
        simp [h]
      rw [this]
      exact ωScottContinuous.const)

theorem elems_apply {E : Type*} [OmegaCompletePartialOrder E] [OrderBot E] (n : ℕ)
    (xs : Fin n → E) (j : ℕ) : elems n xs j = if h : j < n then xs ⟨j, h⟩ else ⊥ := by
  by_cases h : j < n <;> simp [elems, h]

/-- `n` suspended elements as a sequence. Elements are read by structural recursion. -/
@[expose] noncomputable def ofFn (n : ℕ) : (Fin n → DomainResult ε X) →𝒄 LazySeq ε X :=
  DomainResult.valueContinuous.comp (elems n)

theorem ofFn_apply (n : ℕ) (xs : Fin n → DomainResult ε X) :
    ofFn n xs = value (elems n xs) := rfl

theorem ofFn_eq_mk (n : ℕ) (xs : Fin n → DomainResult ε X) :
    ofFn n xs = mk n (fun j => if h : j < n then xs ⟨j, h⟩ else ⊥) := by
  rw [ofFn_apply, mk_apply]
  congr 1
  funext j
  rw [elems_apply]
  by_cases h : j < n <;> simp [h]

/-- Demand a sequence's spine and nothing else. -/
@[expose] noncomputable def spine : LazySeq ε X →𝒄 DomainResult ε (DiscreteOrder Unit) :=
  DomainResult.bind (.const (value ⟨()⟩))

@[simp] theorem spine_value (xs : ℕ → DomainResult ε X) :
    spine (value xs : LazySeq ε X) = value ⟨()⟩ := rfl

/-- The spine of a masked stream is available whatever its elements are. -/
@[simp] theorem spine_mk (n : ℕ∞) (xs : ℕ → DomainResult ε X) : spine (mk n xs) = value ⟨()⟩ :=
  rfl

@[simp] theorem spine_bot : spine (⊥ : LazySeq ε X) = ⊥ := rfl

@[simp] theorem spine_error (e : ε) : spine (error e : LazySeq ε X) = error e := rfl

/-- Force `k` elements from position `i` on, from left to right, each by `f`. -/
@[expose] noncomputable def forceSteps
    (f : DomainResult ε X →𝒄 DomainResult ε (DiscreteOrder Unit)) :
    (k : ℕ) → ℕ → (ℕ → DomainResult ε X) →𝒄 DomainResult ε (DiscreteOrder Unit)
  | 0, _ => .const (value ⟨()⟩)
  | k + 1, i => .ofFun (fun xs => DomainResult.force (f (xs i)) (forceSteps f k (i + 1) xs))
      (ContinuousHom.ωScottContinuous_apply
        (DomainResult.force.ωScottContinuous.comp (f.ωScottContinuous.comp
          (ωScottContinuous.apply i)))
        (forceSteps f k (i + 1)).ωScottContinuous)

@[simp] theorem forceSteps_zero (f : DomainResult ε X →𝒄 DomainResult ε (DiscreteOrder Unit))
    (i : ℕ) (xs : ℕ → DomainResult ε X) : forceSteps f 0 i xs = value ⟨()⟩ := rfl

theorem forceSteps_succ (f : DomainResult ε X →𝒄 DomainResult ε (DiscreteOrder Unit)) (k i : ℕ)
    (xs : ℕ → DomainResult ε X) :
    forceSteps f (k + 1) i xs = DomainResult.force (f (xs i)) (forceSteps f k (i + 1) xs) := rfl

/-! ## Elementwise operations and reindexing -/

variable {Y Z : Type*} [OmegaCompletePartialOrder Y] [OmegaCompletePartialOrder Z]

/-- Apply `f` to each element below `n`, after demanding the spine. -/
@[expose] noncomputable def map (n : ℕ∞) (f : DomainResult ε X →𝒄 DomainResult ε Y) :
    LazySeq ε X →𝒄 LazySeq ε Y :=
  DomainResult.bind ((mk n).comp (.ofFun (fun xs i => f (xs i)) (by
    apply ωScottContinuous.of_apply₂
    intro i
    exact f.ωScottContinuous.comp (ωScottContinuous.apply i))))

theorem map_value (n : ℕ∞) (f : DomainResult ε X →𝒄 DomainResult ε Y)
    (xs : ℕ → DomainResult ε X) : map n f (value xs) = mk n (fun i => f (xs i)) := rfl

/-- Combine elements below `n` pairwise, after demanding the left spine, then the right one. -/
@[expose] noncomputable def zipWith (n : ℕ∞)
    (f : DomainResult ε X →𝒄 DomainResult ε Y →𝒄 DomainResult ε Z) :
    LazySeq ε X →𝒄 LazySeq ε Y →𝒄 LazySeq ε Z :=
  DomainResult.bind₂ (ContinuousHom.curry ((mk n).comp (.ofFun
    (fun (p : (ℕ → DomainResult ε X) × (ℕ → DomainResult ε Y)) (i : ℕ) => f (p.1 i) (p.2 i)) (by
      apply ωScottContinuous.of_apply₂
      intro i
      exact ContinuousHom.ωScottContinuous_apply
        (f.ωScottContinuous.comp ((ωScottContinuous.apply i).comp Prod.ωScottContinuous_fst))
        ((ωScottContinuous.apply i).comp Prod.ωScottContinuous_snd)))))

theorem zipWith_value (n : ℕ∞) (f : DomainResult ε X →𝒄 DomainResult ε Y →𝒄 DomainResult ε Z)
    (xs : ℕ → DomainResult ε X) (ys : ℕ → DomainResult ε Y) :
    zipWith n f (value xs) (value ys) = mk n (fun i => f (xs i) (ys i)) := rfl

theorem zipWith_bot_left (n : ℕ∞)
    (f : DomainResult ε X →𝒄 DomainResult ε Y →𝒄 DomainResult ε Z) (y : LazySeq ε Y) :
    zipWith n f ⊥ y = ⊥ := rfl

/-- Read element `f i` of the source at position `i`, masked at `n`. The spine is returned at
once; reading an element demands the source's spine. -/
@[expose] noncomputable def reindex (n : ℕ∞) (f : ℕ → ℕ) : LazySeq ε X →𝒄 LazySeq ε X :=
  (mk n).comp (.ofFun (fun v i => index (f i) v)
    (ωScottContinuous.of_apply₂ fun i => (index (f i)).ωScottContinuous))

theorem reindex_apply (n : ℕ∞) (f : ℕ → ℕ) (v : LazySeq ε X) :
    reindex n f v = mk n (fun i => index (f i) v) := rfl

/-- `xs ++ ys` with a front of length `front`, masked at `n`. Position `i` reads element `i` of
`xs` below `front` and element `i - front` of `ys` from there on. The spine is returned at once;
reading an element demands the spine of the operand it comes from. -/
@[expose] noncomputable def append (front : ℕ) (n : ℕ∞) :
    LazySeq ε X →𝒄 LazySeq ε X →𝒄 LazySeq ε X :=
  ContinuousHom.curry ((mk n).comp (.ofFun
    (fun (p : LazySeq ε X × LazySeq ε X) i =>
      if i < front then index i p.1 else index (i - front) p.2) (by
      apply ωScottContinuous.of_apply₂
      intro i
      by_cases h : i < front
      · simp only [h, ite_true]
        exact (index i).ωScottContinuous.comp Prod.ωScottContinuous_fst
      · simp only [h, ite_false]
        exact (index _).ωScottContinuous.comp Prod.ωScottContinuous_snd)))

theorem append_apply (front : ℕ) (n : ℕ∞) (xs ys : LazySeq ε X) :
    append front n xs ys =
      mk n (fun i => if i < front then index i xs else index (i - front) ys) := rfl

end Continuous

/-! ## Encodings of native lists -/

section Encoding

variable {ε X β γ δ : Type*}

/-- A native list as a lazy sequence: each element encoded below the length, bottom past it. -/
@[expose] noncomputable def encList (enc : β → DomainResult ε X) (xs : List β) : LazySeq ε X :=
  value fun i => if h : i < xs.length then enc xs[i] else ⊥

section Order

variable [Preorder X]

/-- An encoding lies below a returned stream exactly when each element's encoding lies below the
stream's element at its position. -/
theorem encList_le_value_iff (enc : β → DomainResult ε X) (ys : List β)
    (xs : ℕ → DomainResult ε X) :
    encList enc ys ≤ value xs ↔ ∀ i (hi : i < ys.length), enc ys[i] ≤ xs i := by
  rw [encList, DomainResult.value_le_value_iff]
  refine ⟨fun h i hi => ?_, fun h i => ?_⟩
  · simpa [hi] using h i
  · by_cases hi : i < ys.length
    · simpa [hi] using h i hi
    · simp [hi]

theorem encList_ofFn_le_value_iff {n : ℕ} (enc : β → DomainResult ε X) (ys : Fin n → β)
    (xs : ℕ → DomainResult ε X) :
    encList enc (List.ofFn ys) ≤ value xs ↔ ∀ i : Fin n, enc (ys i) ≤ xs i := by
  rw [encList_le_value_iff]
  exact ⟨fun h i => by simpa using h i (by simp),
    fun h i hi => by simpa using h ⟨i, by simpa using hi⟩⟩

end Order

variable [OmegaCompletePartialOrder X]

theorem index_encList (enc : β → DomainResult ε X) (xs : List β) (i : ℕ)
    (h : i < xs.length) : index i (encList enc xs) = enc xs[i] := by
  simp [encList, h]

theorem index_encList_of_le (enc : β → DomainResult ε X) (xs : List β) (i : ℕ)
    (h : xs.length ≤ i) : index i (encList enc xs) = ⊥ := by
  simp [encList, Nat.not_lt.mpr h]

/-- An encoding is a masked stream at the list's length. -/
theorem encList_eq_mk (enc : β → DomainResult ε X) (xs : List β) :
    encList enc xs = mk xs.length (fun i => if h : i < xs.length then enc xs[i] else ⊥) := by
  rw [mk_apply, encList]
  congr 1
  funext i
  by_cases h : i < xs.length <;> simp [h]

/-- Injective encodings that never diverge give injective list encodings. -/
theorem encList_injective {enc : β → DomainResult ε X} (henc : Function.Injective enc)
    (hbot : ∀ x, enc x ≠ ⊥) : Function.Injective (encList enc) := by
  intro xs ys h
  have hi : ∀ i, index i (encList enc xs) = index i (encList enc ys) := fun i => by rw [h]
  have hlen : xs.length = ys.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hi xs.length
      rw [index_encList_of_le enc xs _ le_rfl, index_encList enc ys _ hlt] at this
      exact hbot _ this.symm
    · have := hi ys.length
      rw [index_encList_of_le enc ys _ le_rfl, index_encList enc xs _ hlt] at this
      exact hbot _ this
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have := hi i
  rw [index_encList enc xs i h₁, index_encList enc ys i h₂] at this
  exact henc this

/-- A constant stream masked at `n` is the encoding of `n` copies. -/
theorem mk_const_eq_encList_replicate (enc : β → DomainResult ε X) (n : ℕ) (v : β) :
    mk (n : ℕ∞) (fun _ => enc v) = encList enc (List.replicate n v) := by
  rw [encList, mk_apply]
  congr 1
  funext i
  by_cases hi : i < n <;> simp [hi]

variable {Y Z : Type*} [OmegaCompletePartialOrder Y] [OmegaCompletePartialOrder Z]

/-- Mapping over an encoding below its length is the encoding of the mapped list. -/
theorem map_encList (encX : β → DomainResult ε X) (encY : γ → DomainResult ε Y)
    (f : DomainResult ε X →𝒄 DomainResult ε Y) (g : β → γ) (hf : ∀ x, f (encX x) = encY (g x))
    (xs : List β) : map xs.length f (encList encX xs) = encList encY (xs.map g) := by
  rw [encList, map_value, mk_apply, encList]
  congr 1
  funext i
  by_cases h : i < xs.length <;> simp [h, hf]

/-- Combining two encodings of one length pairwise is the encoding of the zipped list. -/
theorem zipWith_encList (encX : β → DomainResult ε X) (encY : γ → DomainResult ε Y)
    (encZ : δ → DomainResult ε Z) (f : DomainResult ε X →𝒄 DomainResult ε Y →𝒄 DomainResult ε Z)
    (g : β → γ → δ) (hf : ∀ x y, f (encX x) (encY y) = encZ (g x y)) (xs : List β)
    (ys : List γ) (hlen : xs.length = ys.length) :
    zipWith xs.length f (encList encX xs) (encList encY ys) =
      encList encZ (List.zipWith g xs ys) := by
  rw [encList, encList, zipWith_value, mk_apply, encList]
  congr 1
  funext i
  by_cases h : i < xs.length
  · have h' : i < ys.length := hlen ▸ h
    simp [h, h', hf]
  · simp [h]

/-- Taking a prefix of an encoded list is the encoded prefix. -/
theorem reindex_id_encList (enc : β → DomainResult ε X) (xs : List β) (front : ℕ) :
    reindex front id (encList enc xs) = encList enc (xs.take front) := by
  rw [reindex_apply, mk_apply, encList, encList]
  congr 1
  funext i
  rw [below_natCast]
  by_cases hi : i < front
  · simp [hi]
  · simp [hi]

/-- Dropping a prefix of an encoded list is the encoded suffix. -/
theorem reindex_add_encList (enc : β → DomainResult ε X) (xs : List β) (front : ℕ) :
    reindex (xs.length - front : ℕ) (fun i => front + i) (encList enc xs) =
      encList enc (xs.drop front) := by
  rw [reindex_apply, mk_apply, encList, encList]
  congr 1
  funext i
  rw [below_natCast]
  by_cases hi : i < xs.length - front
  · have h' : front + i < xs.length := by omega
    simp [hi, h']
  · simp [hi]

/-- Appending encoded lists is the encoded append. -/
theorem append_encList (enc : β → DomainResult ε X) (l r : List β) :
    append l.length ((l.length + r.length : ℕ) : ℕ∞) (encList enc l) (encList enc r) =
      encList enc (l ++ r) := by
  simp only [append_apply, mk_apply, encList, index_value, below_natCast]
  congr 1
  funext i
  by_cases hl : i < l.length
  · simp [hl, List.getElem_append_left hl, Nat.lt_add_right]
  · by_cases hr : i < l.length + r.length
    · have hr' : i - l.length < r.length := by omega
      simp [hl, hr, hr', List.getElem_append_right (Nat.not_lt.mp hl)]
    · simp [hr]

end Encoding

/-! ## Decoding a sequence of static length -/

section Decode

variable {ε X N : Type*}

/-- Read a sequence of length `n` as a native family: demand the spine, then decode elements `0`
to `n - 1` from left to right. The first element that does not decode to a value gives the
result, and no position at or past `n` is read. -/
@[expose] def decode (n : ℕ) (dec : DomainResult ε X → DomainResult ε N) (d : LazySeq ε X) :
    DomainResult ε (Fin n → N) :=
  bindPlain d fun xs => @Fin.mOfFn _ DomainResult.monad _ n fun i => dec (xs i)

@[simp] theorem decode_bot (n : ℕ) (dec : DomainResult ε X → DomainResult ε N) :
    decode n dec ⊥ = ⊥ := rfl

@[simp] theorem decode_error (n : ℕ) (dec : DomainResult ε X → DomainResult ε N) (e : ε) :
    decode n dec (error e) = error e := rfl

theorem decode_value (n : ℕ) (dec : DomainResult ε X → DomainResult ε N)
    (xs : ℕ → DomainResult ε X) :
    decode n dec (value xs) = @Fin.mOfFn _ DomainResult.monad _ n fun i => dec (xs i) := rfl

/-- A sequence decodes to `g` exactly when it returns a stream whose elements below `n` decode to
the matching values of `g`. -/
theorem decode_eq_value_iff {n : ℕ} {dec : DomainResult ε X → DomainResult ε N}
    {d : LazySeq ε X} {g : Fin n → N} :
    decode n dec d = value g ↔ ∃ xs, d = value xs ∧ ∀ i : Fin n, dec (xs i) = value (g i) := by
  rw [decode, DomainResult.bindPlain_eq_value_iff]
  exact exists_congr fun _ => and_congr_right fun _ => DomainResult.mOfFn_eq_value_iff

end Decode

end LazySeq

/-- Decoding a sequence of length `n` element by element decodes above the encoding of native
families as lists. -/
theorem DomainResult.DecodesAbove.lazySeq {ε X N : Type*} [Preorder X]
    {enc : N → DomainResult ε X} {dec : DomainResult ε X → DomainResult ε N}
    (h : DecodesAbove enc dec) (n : ℕ) :
    DecodesAbove (fun xs : Fin n → N => LazySeq.encList enc (List.ofFn xs))
      (LazySeq.decode n dec) := by
  intro d x
  rw [LazySeq.decode_eq_value_iff]
  constructor
  · rintro ⟨xs, rfl, hxs⟩
    exact (LazySeq.encList_ofFn_le_value_iff _ _ _).mpr fun i => (h _ _).mp (hxs i)
  · intro hle
    obtain ⟨xs, rfl, -⟩ := value_le_iff.mp hle
    exact ⟨xs, rfl, fun i => (h _ _).mpr ((LazySeq.encList_ofFn_le_value_iff enc x xs).mp hle i)⟩
