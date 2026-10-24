/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.ResolvedLaws
public import PolyFunCryptol.Model.NativeLaws

/-!
# Native values and primitive contracts

A computable shadow of the lazy semantics. `none` stands for divergence, errors and
unsupported constructs alike. Function arguments, aggregate components and sequence
elements stay suspended as `Option`s, as in the lazy semantics. `Represents` relates
a lazy computation to a native value, and `Agrees` relates it to a native result:
every value the result returns is represented.

Words are sequences of bits, read most significant first, as in `wordValue`. The
native word primitives first collect all bits into a `BitVec` (`Native.bits?`), so
their results are ordinary bit-vector expressions. Each supported primitive has a
contract, `Native.primitive_agrees`; the others evaluate to `none`.
-/

public section

open OmegaCompletePartialOrder

namespace Cryptol.Native

/-- Native values; suspended positions are `Option`s. -/
@[expose, reducible] def Value : ClosedTy → Type
  | .var e => e.elim
  | .bit => Bool
  | .integer => Int
  | .unit => Unit
  | .seq l a => l.Index → Option (Value a)
  | .prod a b => Option (Value a) × Option (Value b)
  | .arrow a b => Option (Value a) → Option (Value b)

/-- A native evaluation outcome: a value, or no answer. -/
@[expose, reducible] def Result (a : ClosedTy) : Type := Option (Value a)

/-- A lazy computation represents a native value. -/
@[expose] def Represents : (a : ClosedTy) → Computation a → Value a → Prop
  | .var e, _, _ => e.elim
  | .bit, d, b => d = .value ⟨b⟩
  | .integer, d, i => d = .value ⟨i⟩
  | .unit, d, _ => d = .value ⟨()⟩
  | .seq _ a, d, xs => ∃ ds, d = .value ds ∧ ∀ i x, xs i = some x → Represents a (ds i) x
  | .prod a b, d, p => ∃ x y, d = .value (x, y) ∧
      (∀ v, p.1 = some v → Represents a x v) ∧ (∀ v, p.2 = some v → Represents b y v)
  | .arrow a b, d, f => ∃ g : Computation a →𝒄 Computation b, d = .value g ∧
      ∀ e v, (∀ x, v = some x → Represents a e x) → ∀ y, f v = some y → Represents b (g e) y

/-- Every value that a native result returns is represented. -/
@[expose] def Agrees (a : ClosedTy) (d : Computation a) (v : Result a) : Prop :=
  ∀ x, v = some x → Represents a d x

theorem agrees_none (a : ClosedTy) (d : Computation a) : Agrees a d none := fun _ h => nomatch h

/-! ## Words -/

/-- The bit vector with the given bits, most significant first. -/
@[expose] def ofMsbBits : {n : Nat} → (Fin n → Bool) → BitVec n
  | 0, _ => 0#0
  | _ + 1, f => BitVec.cons (f 0) (ofMsbBits fun i => f i.succ)

theorem getMsbD_ofMsbBits {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (ofMsbBits f).getMsbD i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact BitVec.getMsbD_cons_zero
    | succ i =>
      change (BitVec.cons _ _).getMsbD (i.val + 1) = _
      rw [BitVec.getMsbD_cons_succ, ih]

theorem ofMsbBits_getMsbD {n : Nat} (x : BitVec n) : ofMsbBits (fun i => x.getMsbD i) = x := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  exact getMsbD_ofMsbBits (fun i : Fin n => x.getMsbD i) ⟨i, hi⟩

/-- A word's native bits. -/
@[expose] def word {n : Nat} (x : BitVec n) : Value (wordTy n) :=
  fun i : Fin n => some (x.getMsbD i.val)

/-- A fully defined native word, as an evaluation outcome. -/
@[expose] def wordResult {n : Nat} (x : BitVec n) : Result (wordTy n) := some (word x)

/-- All bits of a native word, when every bit is defined. -/
@[expose] def bits? {n : Nat} (xs : Fin n → Option Bool) : Option (BitVec n) :=
  if h : ∀ i, (xs i).isSome then some (ofMsbBits fun i => (xs i).get (h i)) else none

@[simp] theorem bits?_word {n : Nat} (x : BitVec n) : bits? (word x) = some x := by
  simp [bits?, word, ofMsbBits_getMsbD]

theorem represents_word {n : Nat} (x : BitVec n) :
    Represents (wordTy n) (.value (wordValue x)) (word x) :=
  ⟨wordValue x, rfl, fun _ _ h => by cases h; rfl⟩

/-- A represented word whose bits are all defined is that word's lazy value. -/
theorem eq_wordValue_of_bits? {n : Nat} {d : Computation (wordTy n)} {xs : Value (wordTy n)}
    {x : BitVec n} (hd : Represents (wordTy n) d xs) (hx : bits? xs = some x) :
    d = .value (wordValue x) := by
  obtain ⟨ds, rfl, hds⟩ := hd
  unfold bits? at hx
  split at hx
  · next h =>
    cases hx
    apply congrArg DomainResult.value
    funext i
    rw [hds i _ (Option.some_get (h i)).symm]
    change DomainResult.value _ = DomainResult.value _
    rw [getMsbD_ofMsbBits]
  · exact nomatch hx

/-! ## Primitive contracts -/

/-- Bitwise word logic on bit vectors. -/
@[expose, simp] def _root_.Cryptol.BitOp.word {n : Nat} : BitOp → BitVec n → BitVec n → BitVec n
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y

/-- Fixed word movement on bit vectors. -/
@[expose, simp] def _root_.Cryptol.ShiftOp.word {n : Nat} : ShiftOp → BitVec n → Nat → BitVec n
  | .left, x, k => x <<< k
  | .right, x, k => x >>> k
  | .rotateLeft, x, k => x.rotateLeft k
  | .rotateRight, x, k => x.rotateRight k

/-- Native word logic, defined when both operands have all their bits. -/
@[expose] def wordLogic {n : Nat} (op : BitOp) (x y : Result (wordTy n)) : Result (wordTy n) :=
  x.bind fun xs => y.bind fun ys => (bits? xs).bind fun a => (bits? ys).map fun b =>
    word (op.word a b)

/-- Native movement by a nonnegative integer amount; a negative amount has no answer. -/
@[expose] def shift {n : Nat} (op : ShiftOp) (x : Result (wordTy n)) (k : Result .integer) :
    Result (wordTy n) :=
  x.bind fun xs => k.bind fun k => (bits? xs).bind fun a =>
    if 0 ≤ k then some (word (op.word a k.toNat)) else none

/-- Native meanings of primitives; unsupported primitives have no answer. -/
@[expose] def primitive : {a : ClosedTy} → Primitive a → Result a
  | _, .word x => some (word x)
  | _, .wordLogic _ op => some fun x => some fun y => wordLogic op x y
  | _, .shift _ op => some fun x => some fun k => shift op x k
  | _, _ => none

@[simp] theorem primitive_word {n : Nat} (x : BitVec n) :
    primitive (.word x) = wordResult x := rfl

@[simp] theorem primitive_wordLogic (n : Nat) (op : BitOp) :
    primitive (.wordLogic n op) = some fun x => some fun y => wordLogic op x y := rfl

@[simp] theorem primitive_shift (n : Nat) (op : ShiftOp) :
    primitive (.shift n op) = some fun x => some fun k => shift op x k := rfl

@[simp] theorem wordLogic_word {n : Nat} (op : BitOp) (x y : BitVec n) :
    wordLogic op (wordResult x) (wordResult y) = wordResult (op.word x y) := by
  simp [wordLogic, wordResult]

/-- The amount is stated as an `Option Int`: simp indexes lemmas without unfolding the
pattern-matching family `Value`, but reduces `Value .integer` to `Int` in goals. -/
@[simp] theorem shift_word {n : Nat} (op : ShiftOp) (x : BitVec n) (k : Int) (hk : 0 ≤ k) :
    shift op (wordResult x) (some k : Option Int) = wordResult (op.word x k.toNat) := by
  simp [shift, wordResult, hk]

theorem agrees_wordLogic {n : Nat} (op : BitOp) {d e : Computation (wordTy n)}
    {x y : Result (wordTy n)} (hx : Agrees _ d x) (hy : Agrees _ e y) :
    Agrees (wordTy n) (Semantics.wordLogic n op d e) (wordLogic op x y) := by
  intro z hz
  simp only [wordLogic, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hz
  obtain ⟨xs, rfl, ys, rfl, a, ha, b, hb, rfl⟩ := hz
  rw [eq_wordValue_of_bits? (hx xs rfl) ha, eq_wordValue_of_bits? (hy ys rfl) hb,
    Semantics.wordLogic_values]
  cases op <;> exact represents_word _

theorem agrees_shift {n : Nat} (op : ShiftOp) {d : Computation (wordTy n)}
    {k : Computation .integer} {x : Result (wordTy n)} {m : Result .integer}
    (hx : Agrees _ d x) (hk : Agrees _ k m) :
    Agrees (wordTy n) (Semantics.shift op n d k) (shift op x m) := by
  intro z hz
  simp only [shift, Option.bind_eq_some_iff] at hz
  obtain ⟨xs, rfl, j, rfl, a, ha, hz⟩ := hz
  split at hz
  · next hj =>
    cases hz
    have hj' : (j.toNat : Int) = j := Int.toNat_of_nonneg hj
    rw [eq_wordValue_of_bits? (hx xs rfl) ha, show k = .value ⟨j⟩ from hk j rfl, ← hj',
      ← Semantics.shiftFixed_eq_shift, Semantics.shiftFixed_value]
    cases op <;> exact represents_word _
  · exact nomatch hz

/-- Every primitive's native meaning agrees with its lazy denotation. -/
theorem primitive_agrees : {a : ClosedTy} → (p : Primitive a) → Agrees a p.denote (primitive p)
  | _, .word x => fun _ h => by cases h; exact represents_word x
  | _, .wordLogic n op => fun _ h => by
      cases h
      refine ⟨_, rfl, fun d x hx f hf => ?_⟩
      cases hf
      exact ⟨_, rfl, fun e y hy z hz => agrees_wordLogic op hx hy z hz⟩
  | _, .shift n op => fun _ h => by
      cases h
      refine ⟨_, rfl, fun d x hx f hf => ?_⟩
      cases hf
      exact ⟨_, rfl, fun e y hy z hz => agrees_shift op hx hy z hz⟩
  | _, .zero _ | _, .logic _ _ | _, .complement _ | _, .ring _ _ | _, .intLe
  | _, .wordArrayArithmetic _ _ _ | _, .wordNot _ | _, .wordArithmetic _ _ | _, .wordEq _
  | _, .wordCompare _ _ | _, .toInteger _ | _, .fromInteger _ | _, .shiftFixed _ _ _
  | _, .append _ _ _ | _, .take _ _ _ | _, .drop _ _ _ | _, .reverse _ _ | _, .join _ _ _
  | _, .split _ _ _ | _, .transpose _ _ _ | _, .update _ _ | _, .updateEnd _ _
  | _, .indexEnd _ _ | _, .foldl _ _ _ => agrees_none _ _

end Cryptol.Native
