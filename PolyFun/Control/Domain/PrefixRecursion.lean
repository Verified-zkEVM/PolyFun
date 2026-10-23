/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result
public import ToCslib.Order.PrefixRecursion

/-!
# Recursively generated partial arrays

A generator exposes an array constructor before its elements are demanded.
If every element uses only the strict prefix, its least fixed point agrees
with finite prefix recursion. This holds even when individual entries are
bottom or errors. Exposing the constructor is an explicit hypothesis.
-/

public section

open OmegaCompletePartialOrder

namespace DomainResult

variable {n : Nat} {ε D : Type*} [OmegaCompletePartialOrder D]

/-- The equations for a recursively generated array, retaining partial entries. -/
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

/-- A constructor-producing, prefix-dependent recurrence has its finite tabulated meaning. -/
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
