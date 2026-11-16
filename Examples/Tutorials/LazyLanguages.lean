/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Pointed
public import PolyFun.Control.Domain.PrefixRecursion
public import Mathlib.Order.Category.OmegaCompletePartialOrder
public import Mathlib.Data.Nat.Fib.Basic

/-! # Meanings for a lazy typed language

A language with general recursion, runtime errors and lazy data needs a semantic target that keeps
three outcomes apart: a computation can diverge, fail, or return a value whose own entries,
arguments and results are still partial. `DomainResult` is that target.

This tutorial gives meanings to a small language with numbers, vectors, lazy sequences, functions
and a numeric quantifier. Syntax is left out, so each term appears as its meaning. The language is
not a model of any existing one.
-/

@[expose] public section

open OmegaCompletePartialOrder

namespace PolyFunExamples.LazyLanguages

/-- The runtime errors of the language. -/
abbrev Err := String

/-- Types of the language. -/
inductive Ty
  /-- Numbers. -/
  | nat
  /-- Vectors of a fixed length. -/
  | vec (length : Nat) (entry : Ty)
  /-- Lazy sequences of a static length, which may be infinite. -/
  | seq (length : ℕ∞) (entry : Ty)
  /-- Functions. -/
  | arrow (arg result : Ty)

/-- Values of each type. Entries, arguments and results are computations, so a value's outer
constructor can be known while they are still partial. A sequence is a stream whatever its length:
the length is read from the type. -/
@[implicit_reducible] noncomputable def Ty.value : Ty → ωCPO
  | .nat => .of (DiscreteOrder Nat)
  | .vec n a => .of (Fin n → DomainResult Err a.value)
  | .seq _ a => .of (ℕ → DomainResult Err a.value)
  | .arrow a b => .of (DomainResult Err a.value →𝒄 DomainResult Err b.value)

/-- Computations of a type: they diverge, fail or return a value. -/
abbrev Comp (a : Ty) := DomainResult Err a.value

/-! ## Data is available while its entries are partial -/

/-- A vector with a failing first entry and a diverging second entry. -/
noncomputable def partialPair : Comp (.vec 2 .nat) :=
  .value fun i => if i.val = 0 then .error "first" else ⊥

/-- The vector is a returned value, although neither of its entries is. -/
example : partialPair ≠ ⊥ := DomainResult.value_ne_bot _

/-- Demanding the outer constructor does not touch the entries. -/
example (next : Comp .nat) : DomainResult.force partialPair next = next := rfl

/-! ## Functions do not demand their arguments -/

/-- The function that ignores its argument. -/
noncomputable def constant (a : Ty) {b : Ty} (x : Comp b) : Comp (.arrow a b) :=
  .value (ContinuousHom.const x)

/-- An ignored argument can diverge. -/
example (x : Comp .nat) : DomainResult.applyContinuous (constant .nat x) ⊥ = x := rfl

/-- An ignored argument can fail. -/
example (x : Comp .nat) :
    DomainResult.applyContinuous (constant .nat x) (.error "unused") = x := rfl

/-! ## Strict operations demand their operands from left to right -/

/-- Addition demands both operands, the left one first. -/
noncomputable def add : Comp .nat →𝒄 (Comp .nat →𝒄 Comp .nat) :=
  DomainResult.strict2 fun a b => .value ⟨a + b⟩

/-- The left operand's error wins, even over a diverging right operand. -/
example : add (.error "left") ⊥ = .error "left" := rfl

/-- The left operand's divergence wins, even over a failing right operand. -/
example : add ⊥ (.error "right") = ⊥ := rfl

/-- Both operands return. -/
example : add (.value ⟨1⟩) (.value ⟨2⟩) = .value ⟨3⟩ := rfl

/-- `ifZero c t e` demands `c`, then returns `t` if it is zero and `e` otherwise. -/
noncomputable def ifZero (c t e : Comp .nat) : Comp .nat :=
  DomainResult.condContinuous (t, e) (DomainResult.strict1 (fun k => .value ⟨k == 0⟩) c)

/-- The branch that is not taken can diverge. -/
example (t : Comp .nat) : ifZero (.value ⟨0⟩) t ⊥ = t := rfl

/-- A failing condition fails, whatever the branches are. -/
example (t e : Comp .nat) : ifZero (.error "condition") t e = .error "condition" := rfl

/-! ## Recursion is a least fixed point -/

/-- The definition `x = x` carries no information, so it diverges rather than fails. -/
example : (ContinuousHom.id : Comp .nat →𝒄 Comp .nat).fix = ⊥ :=
  le_antisymm (ContinuousHom.fix_le _ le_rfl) bot_le

/-- The equations of `xs = [first, xs[0] + 1, xs[1] + 1]`: each entry reads an earlier one. -/
noncomputable def increments (first : Comp .nat) :
    (i : Fin 3) → (Fin i.val → Comp .nat) →𝒄 Comp .nat
  | ⟨0, _⟩ => .const first
  | ⟨k + 1, _⟩ => .ofFun fun xs => add (xs ⟨k, Nat.lt_succ_self k⟩) (.value ⟨1⟩)

/-- The recursive vector is a returned value for every `first`, including a diverging one, and it
is the vector that finite recursion on its entries computes. -/
theorem increments_fix (first : Comp .nat) :
    (DomainResult.generateStep (DomainResult.elim (fun e _ => .error e)
      (ContinuousHom.prefixMap (increments first)))).fix =
      DomainResult.value (Function.prefixRecursion fun i => increments first i) :=
  DomainResult.generateStep_fix_eq_prefixRecursion _ _ fun _ => rfl

/-! ## Lazy sequences have a static length

A sequence is a stream of suspended entries behind one suspension, a `LazySeq`. Its length is part
of its type and is not stored in the stream. Every operation that builds a sequence takes the
length as an argument and writes bottom at and past it, so a length can be `⊤`. -/

/-- The infinite stream of ones. -/
noncomputable def ones : Comp (.seq ⊤ .nat) := LazySeq.mk ⊤ fun _ => .value ⟨1⟩

/-- Every entry of `ones` returns. -/
example (i : ℕ) : LazySeq.index i ones = .value ⟨1⟩ := rfl

/-- A sequence of three failing entries still returns its spine. -/
example : LazySeq.spine (LazySeq.mk 3 fun _ => .error "entry" : Comp (.seq 3 .nat)) =
    .value ⟨()⟩ := rfl

/-- Positions at and past the length carry no information. -/
example : LazySeq.index 3 (LazySeq.mk 3 fun _ => .value ⟨1⟩ : Comp (.seq 3 .nat)) = ⊥ := rfl

/-- Force every entry of a finite sequence from left to right, as Haskell's `deepseq` forces a
list of numbers. -/
noncomputable def forceAll (n : ℕ) :
    Comp (.seq n .nat) →𝒄 DomainResult Err (DiscreteOrder Unit) :=
  DomainResult.bind (LazySeq.forceSteps (DomainResult.strict1 fun _ => .value ⟨()⟩) n 0)

/-- A sequence with a failing entry returns its spine, but forcing every entry finds the
failure. -/
example : LazySeq.spine (LazySeq.ofFn 2 ![.value ⟨1⟩, .error "second"] : Comp (.seq 2 .nat)) =
      .value ⟨()⟩ ∧
    forceAll 2 (LazySeq.ofFn 2 ![.value ⟨1⟩, .error "second"]) = .error "second" :=
  ⟨rfl, rfl⟩

/-! ## Recursive streams are determined by their productive steps -/

/-- The step of the Haskell definition `fibs = 1 : 1 : zipWith (+) fibs (tail fibs)`: the first
two entries are `1`, and entry `k + 2` adds entries `k` and `k + 1`. -/
noncomputable def fibStep : ℕ → (ℕ → Comp .nat) → Comp .nat
  | 0, _ => .value ⟨1⟩
  | 1, _ => .value ⟨1⟩
  | k + 2, xs => add (xs k) (xs (k + 1))

/-- The recursive definition of `fibs` at length `n`, as a map on sequences. -/
noncomputable def fibs (n : ℕ∞) : Comp (.seq n .nat) →𝒄 Comp (.seq n .nat) :=
  (LazySeq.mk n).comp (.ofFun (fun s i => fibStep i fun j => LazySeq.index j s) (by
    apply ωScottContinuous.of_apply₂
    rintro (_ | _ | k)
    · exact ωScottContinuous.const
    · exact ωScottContinuous.const
    · exact ContinuousHom.ωScottContinuous_apply
        (add.ωScottContinuous.comp (LazySeq.index k).ωScottContinuous)
        (LazySeq.index (k + 1)).ωScottContinuous))

/-- Each entry reads only earlier entries, at every length. -/
theorem fibStep_productive (n : ℕ∞) : LazySeq.Productive n fibStep := by
  rintro (_ | _ | k) _ p q h
  · rfl
  · rfl
  · exact congrArg₂ (fun x y => add x y) (h k (by omega)) (h (k + 1) (by omega))

/-- The Fibonacci numbers from `fib 1` satisfy the step. -/
theorem fibStep_fib (i : ℕ) :
    fibStep i (fun j => .value ⟨Nat.fib (j + 1)⟩) = .value ⟨Nat.fib (i + 1)⟩ := by
  rcases i with _ | _ | k
  · rfl
  · rfl
  · exact congrArg (fun m => (.value ⟨m⟩ : Comp .nat)) (Nat.fib_add_two (n := k + 1)).symm

/-- At a finite length, the least fixed point is the list of Fibonacci numbers. -/
theorem fibs_fix (n : ℕ) :
    (fibs n).fix = LazySeq.encList (fun m => .value ⟨m⟩)
      (List.ofFn fun i : Fin n => Nat.fib (i + 1)) :=
  LazySeq.fix_eq_encList_of_productive (w := fun i => Nat.fib (i + 1)) rfl
    (fibStep_productive n) fun i _ => fibStep_fib i

/-- At length `⊤`, it is the infinite stream of Fibonacci numbers. -/
theorem fibs_top_fix : (fibs ⊤).fix = LazySeq.mk ⊤ fun i => .value ⟨Nat.fib (i + 1)⟩ :=
  LazySeq.fix_eq_mk_of_productive rfl (fibStep_productive ⊤) fun i _ => fibStep_fib i

/-! ## Decoding a sequence of static length

`LazySeq.decode n dec` reads a sequence of length `n` as a native family: it demands the spine,
then the entries from left to right. When `dec` decodes above an encoding, so does the sequence
decoder, and a fact computed at an encoding transfers to every sequence that decodes to the same
value. -/

/-- Read a number back. -/
noncomputable def readNat : Comp .nat → DomainResult Err ℕ := DomainResult.map DiscreteOrder.value

/-- Reading three entries decodes above the encoding of native triples. -/
theorem readTriple_decodesAbove :
    DomainResult.DecodesAbove
      (fun xs : Fin 3 → ℕ => LazySeq.encList (fun m => (.value ⟨m⟩ : Comp .nat)) (List.ofFn xs))
      (LazySeq.decode 3 readNat) :=
  DomainResult.decodesAbove_map_value.lazySeq 3

/-- The first three Fibonacci numbers, read back as a native triple. -/
theorem decode_fibs_three :
    LazySeq.decode 3 readNat (fibs 3).fix = .value fun i => Nat.fib (i + 1) :=
  (congrArg (LazySeq.decode 3 readNat) (fibs_fix 3)).trans (readTriple_decodesAbove.dec_enc _)

/-! ## Decoded values pass through a fold

A fold over native rows keeps a count and the column sums of a sequence of length `3`. A pair is
read componentwise, and that reading decodes above the pair of encodings. Each step is computed at
encodings, and `DecodesAbove.dec_foldl_eq_of_monotone` carries it through the fold, from a start
that only decodes to its native value. No accumulator needs to be an encoding. -/

/-- Read a count and a sequence of length `3`, the count first. -/
noncomputable def readTally :
    Comp .nat × Comp (.seq 3 .nat) → DomainResult Err (ℕ × (Fin 3 → ℕ)) :=
  DomainResult.decodeProd readNat (LazySeq.decode 3 readNat)

/-- Reading a pair componentwise decodes above the pair of encodings. -/
theorem readTally_decodesAbove :
    DomainResult.DecodesAbove
      (Prod.map (fun m => (.value ⟨m⟩ : Comp .nat))
        fun xs : Fin 3 → ℕ => LazySeq.encList (fun m => (.value ⟨m⟩ : Comp .nat)) (List.ofFn xs))
      readTally :=
  DomainResult.decodesAbove_map_value.prod readTriple_decodesAbove

/-- Count one more row, and add the row to the column sums entry by entry. -/
noncomputable def tallyStep (acc : Comp .nat × Comp (.seq 3 .nat)) (row : Fin 3 → ℕ) :
    Comp .nat × Comp (.seq 3 .nat) :=
  (add acc.1 (.value ⟨1⟩),
    LazySeq.zipWith 3 add acc.2 (LazySeq.encList (fun m => .value ⟨m⟩) (List.ofFn row)))

theorem tallyStep_monotone (row : Fin 3 → ℕ) : Monotone fun acc => tallyStep acc row :=
  fun _ _ h => Prod.mk_le_mk.mpr ⟨add.monotone h.1 _, (LazySeq.zipWith 3 add).monotone h.2 _⟩

/-- At encodings, a step counts the row and adds it to the sums. -/
theorem readTally_tallyStep (k : ℕ) (sums row : Fin 3 → ℕ) :
    readTally (tallyStep (.value ⟨k⟩, LazySeq.encList (fun m => .value ⟨m⟩) (List.ofFn sums))
      row) = .value (k + 1, sums + row) := by
  have hrow : List.zipWith (· + ·) (List.ofFn sums) (List.ofFn row) = List.ofFn (sums + row) :=
    List.ext_getElem (by simp) fun i _ _ => by simp
  have hsums : LazySeq.decode 3 readNat (LazySeq.zipWith 3 add
      (LazySeq.encList (fun m => .value ⟨m⟩) (List.ofFn sums))
      (LazySeq.encList (fun m => .value ⟨m⟩) (List.ofFn row))) = .value (sums + row) := by
    have := LazySeq.zipWith_encList (fun m => (.value ⟨m⟩ : Comp .nat)) (fun m => .value ⟨m⟩)
      (fun m => .value ⟨m⟩) add (· + ·) (fun _ _ => rfl) (List.ofFn sums) (List.ofFn row)
      (by simp)
    rw [List.length_ofFn, hrow] at this
    exact (congrArg (LazySeq.decode 3 readNat) this).trans (readTriple_decodesAbove.dec_enc _)
  simp only [readTally, DomainResult.decodeProd, tallyStep, hsums]
  rfl

/-- From a start that reads back as `(k, sums)`, folding `tallyStep` over native rows reads back as
the native fold. -/
theorem readTally_foldl {acc : Comp .nat × Comp (.seq 3 .nat)} {k : ℕ} {sums : Fin 3 → ℕ}
    (hacc : readTally acc = .value (k, sums)) (rows : List (Fin 3 → ℕ)) :
    readTally (rows.foldl tallyStep acc) =
      .value (rows.foldl (fun t row => (t.1 + 1, t.2 + row)) (k, sums)) :=
  readTally_decodesAbove.dec_foldl_eq_of_monotone (fun row _ => tallyStep_monotone row)
    (fun t row _ => readTally_tallyStep t.1 t.2 row) hacc

/-! ## Polymorphic types have computed domains

The domain of a polymorphic type is defined by recursion on the type. `PointedDomain` lets that
recursion produce the carrier, its order and its bottom together. -/

/-- A type under `n` numeric parameters, or a quantifier over one more. -/
inductive Scheme : Nat → Type
  /-- A type that may mention the parameters. -/
  | mono {n : Nat} (type : (Fin n → Nat) → Ty) : Scheme n
  /-- A quantifier over one numeric parameter. -/
  | all {n : Nat} (body : Scheme (n + 1)) : Scheme n

/-- A quantifier denotes one meaning per parameter, behind one outer suspension: evaluating a
polymorphic definition can diverge or fail before any instance is selected. -/
@[implicit_reducible] noncomputable def Scheme.domain :
    {n : Nat} → Scheme n → (Fin n → Nat) → PointedDomain
  | _, .mono t, ρ => .ofType (Comp (t ρ))
  | _, .all s, ρ => .result Err (.pi Nat fun l => s.domain (Fin.cons (α := fun _ => Nat) l ρ))

/-- A failure at any scheme. -/
noncomputable def Scheme.fail :
    {n : Nat} → (s : Scheme n) → (ρ : Fin n → Nat) → Err → s.domain ρ
  | _, .mono _, _, e => DomainResult.error e
  | _, .all _, _, e => DomainResult.error e

/-- Instantiating a quantifier demands its suspension and selects one instance. It adds no
suspension of its own, because `DomainResult.elim` targets any pointed domain. -/
noncomputable def Scheme.instantiate {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) :
    (Scheme.all s).domain ρ →𝒄 s.domain (Fin.cons (α := fun _ => Nat) l ρ) :=
  DomainResult.elim (fun e => s.fail _ e) (.ofFun fun f => f l)

/-- A diverging polymorphic definition diverges at every instance. -/
example {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) : s.instantiate ρ l ⊥ = ⊥ := rfl

/-- A failing polymorphic definition fails at every instance. -/
example {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) (e : Err) :
    s.instantiate ρ l (DomainResult.error e) = s.fail _ e := rfl

end PolyFunExamples.LazyLanguages
