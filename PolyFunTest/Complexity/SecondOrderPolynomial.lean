/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Complexity.SecondOrderPolynomial

/-!
# Second-order polynomial checks

Compile-time checks for evaluation, substitution, and monotonicity of open-resource bounds.
-/

public section

namespace Complexity.SecondOrderPolynomial

def exampleBound : SecondOrderPolynomial Bool :=
  .add .input (.oracle true (.oracle false .input))

example : exampleBound.eval (fun
    | false => fun n ↦ n + 1
    | true => fun n ↦ 2 * n) 3 = 11 := by
  decide

def replacement (interface : Bool) : SecondOrderPolynomial Unit :=
  if interface then .add .input (.const 1) else .mul (.const 2) .input

example (length : Unit → Nat → Nat) (n : Nat) :
    (exampleBound.subst replacement).eval length n =
      exampleBound.eval (fun interface size ↦ (replacement interface).eval length size) n :=
  eval_subst exampleBound replacement length n

example : MonotoneLengths (fun (_ : Unit) n ↦ n + 7) := by
  intro _ left right hle
  exact Nat.add_le_add_right hle 7

end Complexity.SecondOrderPolynomial
