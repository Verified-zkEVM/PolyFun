/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Uniform

/-!
# Unary parameter and uniform pure-family boundaries

The parameter is charged even for a one-bit result. Counting separates the uniform notion at
an injective query encoding. Binary parameter length cannot replace unary length in that bound.
-/

public section

open PFunctor ComplexityBackends.CslibSingleTape
open ComplexityBackends.CslibSingleTape.Uniform

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
