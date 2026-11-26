/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.LazySeq
public import ToCslib.Order.PrefixRecursion

/-!
# Recursively generated partial arrays and streams

A lazy language can define a sequence by allowing each entry to depend on earlier ones.
`Function.UsesPrefix` makes the resulting equations determine at most one sequence, even
when some entries are bottom or errors. The finite array and stream results use this
uniqueness to identify a recursive definition with a solution of its coordinate equations.

`DomainResult.generateStep body` wraps the array from `body` in `DomainResult.value`, so its
fixed point exposes the array even when an entry is bottom or an error. To identify its entries
by finite prefix recursion, it suffices to give their equations on inputs of the form `value xs`
(`DomainResult.generateStep_fix_eq_prefixRecursion`).

A recursive lazy sequence is a fixed point `X = mk n fun i => step i fun j => index j X`
in stream form. Its step is *productive* below `n` (`LazySeq.Productive`) when, at each position
below `n`, it reads only earlier elements. The masked stream equations then use only the strict
prefix (`LazySeq.Productive.usesPrefix_mask`), so the fixed point is determined element by
element, at any length, `⊤` included:

* `LazySeq.eq_mk_of_productive`: a stream that satisfies the step below `n`, masked at `n`, is the
  fixed point;
* `LazySeq.eq_encList_of_productive`: at a finite length, the fixed point is the encoding of the
  native sequence;
* `LazySeq.eq_of_productive`: two fixed points agree;
* `LazySeq.fix_eq_mk_of_productive` and `LazySeq.fix_eq_encList_of_productive` treat the least
  fixed point of a continuous map on sequences.
-/

public section

open OmegaCompletePartialOrder

namespace DomainResult

variable {n : Nat} {ε D : Type*} [OmegaCompletePartialOrder D]

/-- Apply `body` to the recursive input and wrap the resulting array in `value`.
This exposes the array constructor even when individual entries are partial. -/
@[expose] noncomputable def generateStep
    (body : DomainResult ε (Fin n → D) →𝒄 (Fin n → D)) :
    DomainResult ε (Fin n → D) →𝒄 DomainResult ε (Fin n → D) :=
  valueContinuous.comp body

/-- The recursive result always exposes the generated array constructor. -/
theorem generateStep_fix_value
    (body : DomainResult ε (Fin n → D) →𝒄 (Fin n → D)) :
    (generateStep body).fix = value (body (generateStep body).fix) :=
  (generateStep body).map_fix.symm

/-- A prefix-dependent generator is determined by any solution of its coordinate equations. -/
theorem generateStep_fix_eq
    (body : DomainResult ε (Fin n → D) →𝒄 (Fin n → D))
    (hprefix : Function.UsesPrefix (fun xs => body (value xs)))
    (result : Fin n → D) (hresult : body (value result) = result) :
    (generateStep body).fix = value result := by
  let xs := body (generateStep body).fix
  have hx : (generateStep body).fix = value xs := generateStep_fix_value body
  have hfix : body (value xs) = xs := by rw [← hx]
  exact hx.trans (congrArg value (hprefix.fixedPoint_unique hfix hresult))

/-- If `body (value xs)` follows `step` on each strict prefix of `xs`, the least fixed point
returns the array computed by finite prefix recursion. -/
theorem generateStep_fix_eq_prefixRecursion
    (body : DomainResult ε (Fin n → D) →𝒄 (Fin n → D))
    (step : (i : Fin n) → (Fin i.val → D) →𝒄 D)
    (hbody : ∀ xs, body (value xs) = ContinuousHom.prefixMap step xs) :
    (generateStep body).fix = value (Function.prefixRecursion (fun i => step i)) := by
  let xs := body (generateStep body).fix
  have hx : (generateStep body).fix = value xs := generateStep_fix_value body
  have hfix : ContinuousHom.prefixMap step xs = xs := by
    rw [← hbody, ← hx]
  have heq := (ContinuousHom.prefixMap_usesPrefix step).fixedPoint_unique hfix
    (ContinuousHom.prefixMap_prefixRecursion step)
  exact hx.trans (congrArg value heq)

end DomainResult

namespace LazySeq

variable {ε X : Type*} [OmegaCompletePartialOrder X]

/-- A stream step is productive below `n` when two streams that agree before `i` give the
same result at `i`, for every `i` below `n`. That result may be a value, an error, or bottom.
For example, a step that always returns bottom is productive at every length. -/
@[expose] def Productive (n : ℕ∞) (step : ℕ → (ℕ → DomainResult ε X) → DomainResult ε X) :
    Prop :=
  ∀ i, below n i → ∀ p q, (∀ j < i, p j = q j) → step i p = step i q

variable {n : ℕ∞} {step : ℕ → (ℕ → DomainResult ε X) → DomainResult ε X}

/-- The masked stream equations of a productive step depend only on earlier elements. -/
theorem Productive.usesPrefix_mask (hstep : Productive n step) :
    Function.UsesPrefix fun xs => mask n fun i => step i xs := by
  intro i p q hpq
  simp only [mask_apply]
  split
  · exact hstep i ‹_› p q hpq
  · rfl

/-- The elements of a sequence in the stream form of `step` solve the masked stream equations. -/
theorem index_eq_mask_of_eq_mk {Xs : LazySeq ε X}
    (hX : Xs = mk n fun i => step i fun j => index j Xs) :
    (fun j => index j Xs) = mask n fun i => step i fun j => index j Xs :=
  funext fun j => (congrArg (index j) hX).trans rfl

/-- A sequence in stream form returns its elements. -/
theorem eq_value_of_eq_mk {Xs : LazySeq ε X}
    (hX : Xs = mk n fun i => step i fun j => index j Xs) :
    Xs = DomainResult.value fun j => index j Xs :=
  hX.trans (congrArg DomainResult.value (index_eq_mask_of_eq_mk hX).symm)

/-- Any two fixed points of a productive step agree. -/
theorem eq_of_productive (hstep : Productive n step) {Xs Ys : LazySeq ε X}
    (hX : Xs = mk n fun i => step i fun j => index j Xs)
    (hY : Ys = mk n fun i => step i fun j => index j Ys) : Xs = Ys := by
  rw [eq_value_of_eq_mk hX, eq_value_of_eq_mk hY, hstep.usesPrefix_mask.fixedPoint_unique
    (index_eq_mask_of_eq_mk hX).symm (index_eq_mask_of_eq_mk hY).symm]

/-- A fixed point of a productive step is any stream that satisfies the step below the length,
masked at that length. -/
theorem eq_mk_of_productive (hstep : Productive n step) {ws : ℕ → DomainResult ε X}
    (hw : ∀ i, below n i → step i ws = ws i) {Xs : LazySeq ε X}
    (hX : Xs = mk n fun i => step i fun j => index j Xs) : Xs = mk n ws := by
  have hws : (mask n fun i => step i (mask n ws)) = mask n ws := by
    funext i
    simp only [mask_apply]
    split
    · rename_i hi
      rw [hstep i hi _ ws fun j hj => by simp [mask_apply, below_of_lt hi hj], hw i hi]
    · rfl
  rw [eq_value_of_eq_mk hX,
    hstep.usesPrefix_mask.fixedPoint_unique (index_eq_mask_of_eq_mk hX).symm hws]
  rfl

/-- At a finite length, a fixed point of a productive step is the encoding of the native
recursion `w`. -/
theorem eq_encList_of_productive {N : Type*} {m : ℕ} (hstep : Productive m step)
    {enc : N → DomainResult ε X} {w : ℕ → N}
    (hw : ∀ i < m, step i (fun j => enc (w j)) = enc (w i)) {Xs : LazySeq ε X}
    (hX : Xs = mk m fun i => step i fun j => index j Xs) :
    Xs = encList enc (List.ofFn fun i : Fin m => w i) := by
  rw [eq_mk_of_productive hstep (ws := fun j => enc (w j)) (fun i hi => hw i (by simpa using hi))
    hX, mk_apply, encList]
  congr 1
  funext i
  by_cases hi : i < m <;> simp [hi]

/-- The least fixed point of a productive map is any stream that satisfies the step below the
length. Only the map's equation at the least fixed point is needed. -/
theorem fix_eq_mk_of_productive {F : LazySeq ε X →𝒄 LazySeq ε X}
    (hF : F F.fix = mk n fun i => step i fun j => index j F.fix) (hstep : Productive n step)
    {ws : ℕ → DomainResult ε X} (hw : ∀ i, below n i → step i ws = ws i) : F.fix = mk n ws :=
  eq_mk_of_productive hstep hw ((ContinuousHom.map_fix F).symm.trans hF)

/-- At a finite length, the least fixed point of a productive map is the encoding of the native
recursion `w`. -/
theorem fix_eq_encList_of_productive {N : Type*} {m : ℕ} {F : LazySeq ε X →𝒄 LazySeq ε X}
    (hF : F F.fix = mk m fun i => step i fun j => index j F.fix) (hstep : Productive m step)
    {enc : N → DomainResult ε X} {w : ℕ → N}
    (hw : ∀ i < m, step i (fun j => enc (w j)) = enc (w i)) :
    F.fix = encList enc (List.ofFn fun i : Fin m => w i) :=
  eq_encList_of_productive hstep hw ((ContinuousHom.map_fix F).symm.trans hF)

end LazySeq
