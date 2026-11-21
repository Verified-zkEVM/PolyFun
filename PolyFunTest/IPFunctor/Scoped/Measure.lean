/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.IPFunctor.Scoped.Uses
public import PolyFun.IPFunctor.Scoped.Measure

/-!
# Scoped terms over a random tape

The tape language of `PolyFunTest.IPFunctor.Scoped.Uses` reads two tape positions, each uniform
over `Fin 4`. The program `readOne` does not read position `0`, so its result equals that position
with probability at most `1 / 4`. The program `rand 0` reads position `0` and equals it with
probability `1`, so the bound needs its side condition.
-/

public section

namespace PolyFunTest.Scoped.Measure

open MeasureTheory ProbabilityTheory IPFunctor IPFunctor.ScopedSignature PolyFunTest.Scoped.Uses

/-- A tape of two positions with four values each. Every other position reads `0`. -/
@[expose] def tapeOf (x : Fin 2 → Fin 4) : Nat → Nat := fun n =>
  if h : n < 2 then x ⟨n, h⟩ else 0

theorem tapeOf_update_zero (x : Fin 2 → Fin 4) (y : Fin 4) :
    tapeOf (Function.update x 0 y) = Function.update (tapeOf x) 0 y := by
  funext n
  rcases n with _ | n
  · simp [tapeOf]
  · simp only [tapeOf, Function.update_of_ne (Nat.succ_ne_zero n)]
    split_ifs with h
    · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e)]
    · rfl

/-- Two independent positions, each uniform over `Fin 4`. -/
noncomputable abbrev tapeLaw : Measure (Fin 2 → Fin 4) :=
  Measure.pi fun _ => uniformOn Set.univ

/-- `readOne` does not read position `0`, so it equals that position with probability at most
`1 / 4`. -/
example : tapeLaw {x | Fin.ofNat 4 (readOne.denote (algebra (tapeOf x)) Env.empty) = x 0} ≤
    4⁻¹ := by
  refine (Term.pi_setOf_denote_eq_apply_le_inv_card (fun _ => uniformOn Set.univ) rfl
    (fun x => algebra (tapeOf x)) readOne Env.empty (Fin.ofNat 4) ?_).trans (by simp)
  intro h hh x y
  rw [tapeOf_update_zero]
  have h0 : (⟨.nat, .rand 0⟩ : signature.Head) ∉ readOne.heads := by decide
  exact algebra_update_of_ne _ 0 y h fun e => h0 (e ▸ hh)

/-- `rand 0` reads position `0` and equals it surely. -/
example : tapeLaw
    {x | Fin.ofNat 4 ((rand 0 : signature.Term [] .nat).denote (algebra (tapeOf x)) Env.empty) =
      x 0} = 1 := by
  have h : {x : Fin 2 → Fin 4 | Fin.ofNat 4
      ((rand 0 : signature.Term [] .nat).denote (algebra (tapeOf x)) Env.empty) = x 0} =
      Set.univ := by
    ext x
    simp [rand, algebra, tapeOf]
  rw [h, measure_univ]

end PolyFunTest.Scoped.Measure
