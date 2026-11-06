/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.PrefixRecursion

/-!
# Prefix recurrence boundaries

Constructor-producing arrays may contain bottom and errors. Prefix dependence
excludes self-reference; it is not a general uniqueness claim about recursion.
-/

public section

open OmegaCompletePartialOrder

namespace PolyFunTest.PrefixRecursion

/-- Partial scalar entries used by these recurrence regressions. -/
abbrev Entry := DomainResult String (DiscreteOrder Nat)

/-- A two-entry generator whose second entry reads the first. -/
noncomputable def copyFirst (first : Entry) :
    DomainResult String (Fin 2 → Entry) →𝒄 (Fin 2 → Entry) :=
  DomainResult.elim (fun e _ => .error e)
    (.ofFun (fun xs i => if i.val = 0 then first else xs 0) (by
      apply ωScottContinuous.of_apply₂
      intro i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        exact ωScottContinuous.const
      · simp only [hi, ↓reduceIte]
        exact ωScottContinuous.apply 0))

/-- The first entry reaches the second through the prefix hypothesis, whether it is a value,
an error or bottom. -/
example (first : Entry) : (DomainResult.generateStep (copyFirst first)).fix =
    DomainResult.value (fun _ => first) := by
  apply DomainResult.generateStep_fix_eq
  · intro i x y h
    obtain ⟨_ | _ | _, hi⟩ := i
    · rfl
    · exact h 0 (Nat.succ_pos 0)
    · omega
  · funext i
    obtain ⟨_ | _ | _, hi⟩ := i
    · rfl
    · rfl
    · omega

example : (DomainResult.generateStep (ε := String)
    (.const (fun i : Fin 2 => if i.val = 0 then (⊥ : Entry) else .error "entry"))).fix =
      DomainResult.value (fun i : Fin 2 => if i.val = 0 then (⊥ : Entry) else .error "entry") := by
  apply DomainResult.generateStep_fix_eq
  · intro i x y h
    rfl
  · rfl

example : (DomainResult.generateStep
    (.const (Fin.elim0 : Fin 0 → Entry)) :
      DomainResult String (Fin 0 → Entry) →𝒄 DomainResult String (Fin 0 → Entry)).fix =
      DomainResult.value Fin.elim0 := by
  apply DomainResult.generateStep_fix_eq
  · intro i
    exact i.elim0
  · rfl

example : ¬ Function.UsesPrefix (id : (Fin 1 → Bool) → Fin 1 → Bool) := by
  intro h
  have hf : false = true := h 0 (fun _ => false) (fun _ => true) (by
    intro j hj
    exact (Nat.not_lt_zero j.val hj).elim)
  cases hf

example {n : Nat} (step : (i : Fin n) → (Fin i.val → Entry) →𝒄 Entry) :
    (ContinuousHom.prefixMap step).fix = Function.prefixRecursion (fun i => step i) :=
  ContinuousHom.prefixMap_fix step

end PolyFunTest.PrefixRecursion
