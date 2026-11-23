/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedEffects

/-!
# Sums of binding signatures

The effectful-language tutorial's signature is the sum of the scoped-program signature and a
query signature.

* A term embedded from either summand means what it means in that summand, whatever the other
  summand's interpretation. The same holds for the call-by-value reading.
* An embedded term uses only heads of its own summand, and `decide` checks this for concrete
  terms through the finiteness instance of the sum's arguments.
* The combined interpretations are reducible, so the reading of a concrete term normalizes by
  `simp` with the equations of the summands' algebras.
* A term that uses a query changes its meaning when the query's interpretation does, and its run
  changes when the handler does. So the fragment condition of `run_denoteCBV_of_heads` cannot be
  dropped.
-/

@[expose] public section

namespace PolyFunTest.Scoped.Sum

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedPrograms Examples.ScopedEffects

/-- Whether a head of the effectful language comes from the scoped-program signature. -/
def isCore (h : Lang.Head) : Bool := Sum.isLeft h.op

/-! ## Embedded terms -/

/-- Embedding commutes with constructors. -/
example (n : Nat) : Term.inl (τ := querySignature) (Expr.literal n : Expr [] .nat) =
    .node (.inl (.literal n)) fun p => nomatch p := by
  rw [Expr.literal, Term.inl_node]
  congr 1
  funext p
  nomatch p

example (f g : Nat → Nat) :
    (Term.inl (sumTo 4)).denote (algebra.sum (queryAlgebra f)) Env.empty =
      (Term.inl (sumTo 4)).denote (algebra.sum (queryAlgebra g)) Env.empty := by
  rw [Term.denote_inl, Term.denote_inl]

example : (Term.inl (sumTo 4)).denoteCBV cbv Env.empty = (sumTo 4).denoteCBV coreCBV Env.empty :=
  Term.denoteCBV_inl _ _ _ _

/-- A query of the nearest variable, as a term of the query signature alone. -/
def queryVar : querySignature.Term [.nat] .nat := .node .query fun _ => .var .zero

example (f : Nat → Nat) (n : Nat) :
    (Term.inr (σ := signature) queryVar).denote (algebra.sum (queryAlgebra f)) (Env.single n) =
      f n := by
  rw [Term.denote_inr]
  rfl

example (n : Nat) :
    (Term.inr (σ := signature) queryVar).denoteCBV cbv (Env.single n) =
      PFunctor.FreeM.lift (P := Query) n := by
  rw [Term.denoteCBV_inr]
  rfl

/-! ## Heads -/

example : (Term.inl (τ := querySignature) (sumTo 3)).heads ⊆ {h | isCore h = true} := by decide

example : (Term.inr (σ := signature) queryVar).heads ⊆ {h | isCore h = false} := by decide

example : (Term.inl (τ := querySignature) (sumTo 3)).heads = Head.inl '' (sumTo 3).heads :=
  Term.heads_inl _

example : (Term.inr (σ := signature) queryVar).heads = {Head.inr ⟨.nat, QueryOp.query⟩} := by
  rw [Term.heads_inr]
  simp [queryVar]

example : ¬ askTwice.heads ⊆ {h | isCore h = true} := by decide

/-! ## Concrete readings by `simp` -/

/-- The ordinary reading of a concrete term normalizes by `simp` with the summands' equations, as
its call-by-value reading does in the tutorial. -/
example (f : Nat → Nat) :
    askNested.denote (algebra.sum (queryAlgebra f)) Env.empty = f (f 3) := by
  simp [askNested, query, algebra, queryAlgebra, Expr.literal]

/-! ## The fragment condition is needed -/

example : askTwice.denote (algebra.sum (queryAlgebra id)) Env.empty = 6 := rfl

example : askTwice.denote (algebra.sum (queryAlgebra (· + 1))) Env.empty = 9 := rfl

example :
    run id (askTwice.denoteCBV cbv Env.empty) ≠ run (· + 1) (askTwice.denoteCBV cbv Env.empty) := by
  decide

end PolyFunTest.Scoped.Sum
