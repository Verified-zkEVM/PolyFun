/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Uniform
public import Mathlib.Data.Nat.Size

/-!
# Unary parameter and uniform pure-family boundaries

The parameter is charged even for a one-bit result. Counting separates the uniform notion at
an injective query encoding. Binary parameter length cannot replace unary length in that bound:
`binary_no_envelope` is the arithmetic reason, independent of any machine.
-/

public section

open PFunctor ComplexityBackends.CslibSingleTape
open ComplexityBackends.CslibSingleTape.Uniform

namespace PolyFunTest.ComplexityBackends.CslibSingleTape.Uniform

/-- Under the unary parameter the parameter itself is part of the input, so the identity
polynomial already bounds it by the packed input length `n + k`. -/
theorem unary_envelope (n k : ℕ) : n ≤ (Polynomial.X : Polynomial ℕ).eval (n + k) := by
  simp

/-- No polynomial in the binary length `Nat.size n` bounds `n` itself, so a result carrying `n`
unary bits has no polynomial length bound in a binary parameter encoding. -/
theorem binary_no_envelope (q : Polynomial ℕ) : ∃ n, q.eval (Nat.size n) < n := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (Polynomial.eventually_eval_le_two_pow_div_four q)
  refine ⟨2 ^ (M + 3), ?_⟩
  rw [Nat.size_pow]
  calc q.eval (M + 3 + 1) ≤ 2 ^ ((M + 3 + 1) / 4) := hM _ (by omega)
    _ < 2 ^ (M + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end PolyFunTest.ComplexityBackends.CslibSingleTape.Uniform

open PolyFunTest.ComplexityBackends.CslibSingleTape.Uniform

example (n : ℕ) (b : Bool) : (unaryOutput ⟨n, b⟩).length = n + 2 :=
  length_unaryOutput n b

example {n m : ℕ} {s t : List Bool} (h : unaryTag n s = unaryTag m t) : n = m ∧ s = t :=
  unaryTag_inj h

example {p : ℕ → PFunctor.{0, 0}} {posEnc : (PFunctor.sigma p).A → List Bool}
    (hp : Function.Injective posEnc) :
    ∃ f : (n : ℕ) → BitVec n → Bool, IsEmpty (UniformPureWitness p posEnc f) :=
  exists_isEmpty_uniformPureWitness hp

example (q : Polynomial ℕ) : ∃ n, q.eval (Nat.size n) < n := binary_no_envelope q

noncomputable example {p : ℕ → PFunctor.{0, 0}} {posEnc : (PFunctor.sigma p).A → List Bool}
    {f : (n : ℕ) → BitVec n → Bool} (w : UniformPureWitness p posEnc f) :
    Backend.description.FamRealizer Backend.polynomialBackend
      (fun n (x : BitVec n) ↦ unaryInput ⟨n, x⟩) (fun _ ↦ headEnc posEnc)
      (fun n x ↦ Sum.inl ⟨n, f n x⟩) := w.toFam
