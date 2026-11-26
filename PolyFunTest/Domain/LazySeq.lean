/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.PrefixRecursion
public import PolyFun.Logic.KernelRfl

/-!
# Lazy sequence boundaries

A sequence's spine is available before its elements, and its static length masks every position at
and past it. `map` and `zipWith` demand their operands' spines, while `reindex` and `append`
return a spine at once. These equations hold by definitional unfolding through ordinary imports,
and a literal reads its elements at closed indices also in the kernel. On encodings of native
lists, the operations compute the `List` operations, and distinct lists have distinct encodings.
Decoding demands elements from left to right and reads nothing past the length. A step that reads
its own position is not productive; one that reads earlier positions determines its stream at
length `⊤`.
-/

public section

open OmegaCompletePartialOrder

namespace PolyFunTest.LazySeq

/-- Partial elements used by these regressions. -/
abbrev Entry := DomainResult String (DiscreteOrder ℕ)

/-- Lazy sequences of partial elements. -/
abbrev Seq := LazySeq String (DiscreteOrder ℕ)

/-- Numbers as returned elements. -/
abbrev enc (k : ℕ) : Entry := .value ⟨k⟩

/-! ## The spine is available before the elements -/

example (n : ℕ∞) : LazySeq.spine (LazySeq.mk n fun _ => (⊥ : Entry)) = .value ⟨()⟩ := rfl

/-- Demanding the outer constructor of a sequence of diverging elements does not diverge. -/
example (n : ℕ∞) (next : Entry) :
    DomainResult.force (LazySeq.mk n fun _ => (⊥ : Entry)) next = next := rfl

example : LazySeq.index 0 (LazySeq.mk 2 fun _ => (.error "e" : Entry)) = .error "e" := rfl

example : LazySeq.spine (⊥ : Seq) = ⊥ := rfl

/-! ## Which operations demand a spine -/

/-- `map` demands the spine of its operand. -/
example (f : Entry →𝒄 Entry) : LazySeq.map 2 f (⊥ : Seq) = ⊥ := rfl

/-- `zipWith` demands the left spine, then the right one. -/
example (f : Entry →𝒄 Entry →𝒄 Entry) (xs : ℕ → Entry) :
    LazySeq.zipWith 2 f (.value xs) (⊥ : Seq) = ⊥ := rfl

/-- `reindex` returns a spine at once, even from a diverging source. -/
example : LazySeq.spine (LazySeq.reindex 2 id (⊥ : Seq)) = .value ⟨()⟩ := rfl

/-- `append` returns a spine at once, even from diverging operands. -/
example : LazySeq.spine (LazySeq.append 1 2 (⊥ : Seq) ⊥) = .value ⟨()⟩ := rfl

/-- Reading an element of `append` demands the spine of the operand it comes from. -/
example (xs : ℕ → Entry) :
    LazySeq.index 0 (LazySeq.append 1 2 (.value xs) (⊥ : Seq)) = xs 0 ∧
      LazySeq.index 1 (LazySeq.append 1 2 (.value xs) (⊥ : Seq)) = ⊥ := ⟨rfl, rfl⟩

/-! ## Masking at the static length -/

example (xs : ℕ → Entry) : LazySeq.index 2 (LazySeq.mk 3 xs) = xs 2 := rfl

example (xs : ℕ → Entry) : LazySeq.index 5 (LazySeq.mk 3 xs) = ⊥ := rfl

example (xs : ℕ → Entry) (i : ℕ) : LazySeq.index i (LazySeq.mk ⊤ xs) = xs i := rfl

/-- Elements past the length are forgotten, so streams that agree below it give one sequence. -/
example : LazySeq.mk 2 (fun i => if i < 2 then enc i else .error "past") =
    LazySeq.mk 2 fun i => enc i := by
  rw [LazySeq.mk_apply, LazySeq.mk_apply]
  congr 1
  funext i
  by_cases hi : i < 2 <;> simp [hi]

/-! ## Literals read their elements at closed indices -/

example (x y z : Entry) : LazySeq.index 1 (LazySeq.ofFn 3 ![x, y, z]) = y := rfl

example (x y z : Entry) : LazySeq.index 1 (LazySeq.ofFn 3 ![x, y, z]) = y := by kernel_rfl

example (x y z : Entry) : LazySeq.index 3 (LazySeq.ofFn 3 ![x, y, z]) = ⊥ := rfl

/-! ## Operations on encodings -/

example : LazySeq.reindex (2 : ℕ) id (LazySeq.encList enc [1, 2, 3]) =
    LazySeq.encList enc [1, 2] :=
  LazySeq.reindex_id_encList enc [1, 2, 3] 2

/-- Taking more than the list keeps the list. -/
example : LazySeq.reindex (5 : ℕ) id (LazySeq.encList enc [1, 2]) = LazySeq.encList enc [1, 2] :=
  LazySeq.reindex_id_encList enc [1, 2] 5

example : LazySeq.reindex (3 - 1 : ℕ) (fun i => 1 + i) (LazySeq.encList enc [1, 2, 3]) =
    LazySeq.encList enc [2, 3] :=
  LazySeq.reindex_add_encList enc [1, 2, 3] 1

/-- Mapping a function that acts on encodings maps the list. -/
example : LazySeq.map (2 : ℕ) (DomainResult.strict1 fun m => enc (m + 1))
    (LazySeq.encList enc [1, 2]) = LazySeq.encList enc [2, 3] :=
  LazySeq.map_encList enc enc _ (· + 1) (fun _ => rfl) [1, 2]

/-- A constant stream at a finite length is the encoding of copies. -/
example : LazySeq.mk (3 : ℕ) (fun _ => enc 7) = LazySeq.encList enc [7, 7, 7] :=
  LazySeq.mk_const_eq_encList_replicate enc 3 7

/-- Distinct lists have distinct encodings. -/
example : LazySeq.encList enc [1, 2] ≠ LazySeq.encList enc [2, 1] := fun h => by
  have := LazySeq.encList_injective (fun _ _ h => by simpa using h)
    (fun _ => DomainResult.value_ne_bot _) h
  simp at this

example : LazySeq.append 1 (1 + 2 : ℕ) (LazySeq.encList enc [1]) (LazySeq.encList enc [2, 3]) =
    LazySeq.encList enc [1, 2, 3] :=
  LazySeq.append_encList enc [1] [2, 3]

/-- Past the front, an appended sequence reads the back. -/
example : LazySeq.index 2
    (LazySeq.append 1 3 (LazySeq.encList enc [1]) (LazySeq.encList enc [2, 3])) = enc 3 := rfl

/-! ## Strict operations and conditionals -/

/-- The left operand's error wins over a diverging right operand. -/
example : DomainResult.strict2 (fun a b : ℕ => enc (a + b)) (.error "left") ⊥ = .error "left" :=
  rfl

/-- A conditional demands only the branch it selects. -/
example (t : Entry) : DomainResult.condContinuous (t, ⊥) (.value ⟨true⟩) = t := rfl

example (t e : Entry) :
    DomainResult.condContinuous (t, e) (⊥ : DomainResult String (DiscreteOrder Bool)) = ⊥ := rfl

/-! ## Decoding from left to right, below the length -/

/-- Read a number back. -/
abbrev readNat : Entry → DomainResult String ℕ := DomainResult.map DiscreteOrder.value

/-- The first element's error wins over a diverging second element. -/
example : LazySeq.decode 2 readNat (LazySeq.ofFn 2 ![.error "first", ⊥]) = .error "first" := rfl

/-- The first element's divergence wins over a failing second element. -/
example : LazySeq.decode 2 readNat (LazySeq.ofFn 2 ![⊥, .error "second"]) = ⊥ := rfl

/-- Positions at and past the length are not read. -/
example : LazySeq.decode 2 readNat
    (.value fun i => if i < 2 then enc (i + 1) else .error "past") = .value ![1, 2] := by
  rw [LazySeq.decode_eq_value_iff]
  exact ⟨_, rfl, fun ⟨i, hi⟩ => by rcases i with _ | _ | i <;> first | rfl | omega⟩

/-- Reading back decodes above the encoding, so a sequence decodes exactly when it lies above an
encoding. -/
example (d : Seq) (xs : Fin 2 → ℕ) :
    LazySeq.decode 2 readNat d = .value xs ↔ LazySeq.encList enc (List.ofFn xs) ≤ d :=
  DomainResult.decodesAbove_map_value.lazySeq 2 d xs

/-- Behind a further suspension, a result decodes exactly when it returns a result above the
encoding. -/
example (d : DomainResult String Entry) (x : ℕ) :
    DomainResult.bindPlain d readNat = .value x ↔
      (.value (enc x) : DomainResult String Entry) ≤ d :=
  DomainResult.decodesAbove_map_value.bindPlain d x

/-! ## Productivity over a well-founded order -/

/-- A step that always yields bottom satisfies the prefix condition at every length. -/
example (n : ℕ∞) : LazySeq.Productive n (fun _ (_ : ℕ → Entry) => ⊥) :=
  fun _ _ _ _ _ => rfl

/-- A step that reads its own position is not productive. -/
example : ¬LazySeq.Productive (1 : ℕ∞) (fun i (xs : ℕ → Entry) => xs i) := by
  intro h
  have := h 0 rfl (fun _ => ⊥) (fun _ => enc 0) fun j hj => absurd hj (Nat.not_lt_zero j)
  exact DomainResult.value_ne_bot _ this.symm

/-- Prefix dependence over `ℕ` determines a solution. -/
example {x y : ℕ → ℕ} (hx : (fun i => if i = 0 then 0 else x (i - 1) + 1) = x)
    (hy : (fun i => if i = 0 then 0 else y (i - 1) + 1) = y) : x = y := by
  refine Function.UsesPrefix.fixedPoint_unique (f := fun z i => if i = 0 then 0 else z (i - 1) + 1)
    (fun i x y h => ?_) hx hy
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, ↓reduceIte, h (i - 1) (by omega)]

/-- The stream `xs = 0 : map (· + 1) xs` at length `⊤`. -/
noncomputable def countStep : ℕ → (ℕ → Entry) → Entry
  | 0, _ => enc 0
  | k + 1, xs => DomainResult.strict1 (fun m => enc (m + 1)) (xs k)

/-- The step reads only the previous element. -/
theorem countStep_productive : LazySeq.Productive ⊤ countStep := by
  rintro (_ | k) _ p q h
  · rfl
  · exact congrArg (DomainResult.strict1 fun m => enc (m + 1)) (h k (Nat.lt_succ_self k))

/-- Every fixed point is the stream of numbers. -/
example {Xs : Seq} (hX : Xs = LazySeq.mk ⊤ fun i => countStep i fun j => LazySeq.index j Xs) :
    Xs = LazySeq.mk ⊤ enc :=
  LazySeq.eq_mk_of_productive countStep_productive (by rintro (_ | k) _ <;> rfl) hX

/-- Two fixed points agree without computing either. -/
example {Xs Ys : Seq} (hX : Xs = LazySeq.mk ⊤ fun i => countStep i fun j => LazySeq.index j Xs)
    (hY : Ys = LazySeq.mk ⊤ fun i => countStep i fun j => LazySeq.index j Ys) : Xs = Ys :=
  LazySeq.eq_of_productive countStep_productive hX hY

end PolyFunTest.LazySeq
