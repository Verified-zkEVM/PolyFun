/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import PolyFun.IPFunctor.Scoped.CostD.Semantics

/-!
# Cost of the terms of D

The cost of a term in an environment is the worst-case cost (`CostD.cost`) of its evaluation:
the largest sum, along a branch of the evaluation, of the prices of the steps and the charges of
the calls. A call of the operation `e` at an argument is charged by `q`. The steps are priced as
in the weak call-by-value λ-calculus L of Forster, Kunze and Roth [FKR20]: the
price `1` for a β-step and logarithmic prices for arithmetic on `ℕ`.

## Main definitions

* `Tm.cost`: the cost of a term in an environment.

## Main results

* `Tm.cost_var`, `Tm.cost_lam`, `Tm.cost_lit`: variables, abstractions and literals are free.
* `Tm.cost_letE_of_eval`: a `letE` whose bound term evaluates to a value without a step costs
  one step plus its body.

## References

* [FKR20] Forster, Kunze and Roth, *The weak call-by-value λ-calculus is
  reasonable for both time and space*, POPL 2020.
-/

@[expose] public section

universe u

namespace IPFunctor.CostD

open IPFunctor.ScopedSignature PFunctor

variable {B : Ground.{u}} {E : Effect B} {ω : Type u} [Add ω] [Zero ω] [CompleteLattice ω]
  {Γ : List (Ty B.G)} {a b : Ty B.G}

namespace Tm

/-- The cost of the term `t` in the environment `η`: the worst-case cost of its evaluation, with
the calls charged by `q` and the steps priced by `π`. -/
noncomputable def cost (q : E.toPFunctor.A → ω) (π : Price B ω) (t : Tm E Γ a)
    (η : Env (Val B (Ticked E.toPFunctor ω)) Γ) : ω :=
  CostD.cost q (t.eval π η)

variable (q : E.toPFunctor.A → ω) (π : Price B ω)
  (η : Env (Val B (Ticked E.toPFunctor ω)) Γ)

/-- A variable is free. -/
@[simp] theorem cost_var (x : ScopedVar Γ a) : (Tm.var (E := E) x).cost q π η = 0 := rfl

/-- An abstraction is free. -/
@[simp] theorem cost_lam (body : Tm E (a :: Γ) b) : (Tm.lam body).cost q π η = 0 := rfl

/-- A literal is free. -/
@[simp] theorem cost_lit (g : B.G) (v : B.den g) : (Tm.lit (E := E) g v).cost q π η = 0 := rfl

/-- A `letE` whose bound term evaluates to the value `v` without a step or a call costs one step
plus its body at `v`. -/
theorem cost_letE_of_eval (e : Tm E Γ a) (body : Tm E (a :: Γ) b)
    (v : Val B (Ticked E.toPFunctor ω) a) (he : e.eval π η = pure v) :
    (Tm.letE e body).cost q π η = π.step + body.cost q π (Env.cons v η) := by
  have h : (Tm.letE e body).eval π η =
      e.eval π η >>= fun x => tick π.step >>= fun _ => body.eval π (Env.cons x η) := rfl
  unfold cost
  rw [h, he, pure_bind, cost_tick_bind]

end Tm

end IPFunctor.CostD
