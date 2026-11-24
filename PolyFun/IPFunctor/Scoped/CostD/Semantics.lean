/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import PolyFun.IPFunctor.Scoped.CostD.Syntax
public import PolyFun.IPFunctor.Scoped.CostD.Tree
public import PolyFun.IPFunctor.Scoped.CBVInterpretation

/-!
# Evaluator and denotation of the cost language D

D is read call by value (`CBVInterpretation`) into free programs over an interface `Q`. The
reading is parametric in a `Machine`: how a call of the effect signature runs in `Q`, and how a
step of a given price is recorded. A value of a function type is a Kleisli arrow
`Val a → PFunctor.FreeM Q (Val b)` (`Val`).

Steps are priced as in the weak call-by-value λ-calculus L of Forster, Kunze and Roth [FKR20]:
an application, a `letE` (priced as the β-redex `(λx. b) e`), a `seq`, a branch of `case` and
each iteration of `iter` cost one step of price `Price.step`; a primitive operation `p` at the argument `v` costs
`Price.prim p v`, which carries a logarithmic price of arithmetic on `ℕ` when `ℕ` is a ground
type. Variables, literals, abstractions, pairs, projections and injections are free.

The two instances are:

* `Tm.eval`: the evaluator, into `Ticked E.toPFunctor ω`, with a tick of the step's price at
  every step (`Machine.timed`).
* `Tm.den`: the denotation, into `E.toPFunctor`, without ticks (`Machine.untimed`).

## Main definitions

* `Val`: the values of D at a type, for programs over an interface `Q`.
* `Price`, `Price.unit`: the prices of the steps, and the trivial price record.
* `Machine`, `Machine.timed`, `Machine.untimed`: how calls run and how steps are recorded.
* `iterT`, `coreCBV`, `queryCBV`, `cbv`: the call-by-value algebra of D.
* `Tm.eval`, `Tm.den`: the evaluator and the denotation.

## Omitted constructors

The fragment has no

* inductive or dependent types: `mu`, `imu`, `pi`, `sig` with `con`, `fold`, `icon`, `ifold`,
  `ptab`, `papp`, `spair`, `scase`, `fcase`;
* lists: `nil`, `cons`, `lcase`, `foldl`;
* conditional `ite`;
* effect constructors `sample`, `get`, `set`, `fail`.

Effects are calls of an effect signature (`query`); booleans are a ground type, with `case` on
`unit ⊕ unit`.

## References

* [FKR20] Forster, Kunze and Roth, *The weak call-by-value λ-calculus is
  reasonable for both time and space*, POPL 2020.
-/

@[expose] public section

universe u

namespace IPFunctor.CostD

open IPFunctor.ScopedSignature PFunctor

variable {B : Ground.{u}}

/-- The values of D for programs over the interface `Q`: the values of the ground types, unit,
natural numbers, pairs, sums, and Kleisli arrows at function types. -/
@[reducible] def Val (B : Ground.{u}) (Q : PFunctor.{u, u}) : Ty B.G → Type u
  | .base g => B.den g
  | .unit => PUnit
  | .nat => ULift ℕ
  | .prod a b => Val B Q a × Val B Q b
  | .sum a b => Val B Q a ⊕ Val B Q b
  | .arr a b => Val B Q a → PFunctor.FreeM Q (Val B Q b)

/-- The prices of the evaluation steps of D in the cost codomain `ω`. -/
structure Price (B : Ground.{u}) (ω : Type u) where
  /-- The price of a β-step: an application, a `letE`, a `seq`, a branch, an iteration. -/
  step : ω
  /-- The price of a primitive operation at its argument. -/
  prim : {g h : B.G} → B.Prim g h → B.den g → ω

/-- How the evaluator runs in the interface `Q`: the calls of the effect signature `E`, and the
record of a step of price `w`. -/
structure Machine (E : Effect B) (Q : PFunctor.{u, u}) (ω : Type u) where
  /-- Run the operation `e` at an argument. -/
  call : (e : E.E) → B.den (E.dom e) → PFunctor.FreeM Q (B.den (E.cod e))
  /-- Record a step of price `w`. -/
  step : ω → PFunctor.FreeM Q PUnit

variable {E : Effect B} {Q : PFunctor.{u, u}} {ω : Type u}

/-- `iterT M π f i n` applies `f` to `i`, `n` times, with one step before each application. -/
def iterT (M : Machine E Q ω) (π : Price B ω) {c : Ty B.G} (f : Val B Q (.arr c c))
    (i : Val B Q c) : ℕ → PFunctor.FreeM Q (Val B Q c)
  | 0 => pure i
  | n + 1 => do
    let s ← iterT M π f i n
    M.step π.step
    f s

/-- The call-by-value reading of the constructors of D without effects. Arguments run from left
to right; an abstraction returns a Kleisli arrow. -/
def coreCBV (M : Machine E Q ω) (π : Price B ω) :
    CBVInterpretation (core B) (PFunctor.FreeM Q) (Val B Q)
  | _, .lam _ _, next => pure fun x => next 0 (Env.cons x Env.empty)
  | _, .app _ _, next => do
    let g ← next 0 Env.empty
    let x ← next 1 Env.empty
    M.step π.step
    g x
  | _, .letE _ _, next => do
    let x ← next 0 Env.empty
    M.step π.step
    next 1 (Env.cons x Env.empty)
  | _, .seq _ _, next => do
    let _ ← next 0 Env.empty
    M.step π.step
    next 1 Env.empty
  | _, .lit _ v, _ => pure v
  | _, .natLit n, _ => pure ⟨n⟩
  | _, .prim p, next => do
    let x ← next 0 Env.empty
    M.step (π.prim p x)
    pure (B.apply p x)
  | _, .unit, _ => pure PUnit.unit
  | _, .pair _ _, next => do
    let x ← next 0 Env.empty
    let y ← next 1 Env.empty
    pure (x, y)
  | _, .fst _ _, next => do
    let p ← next 0 Env.empty
    pure p.1
  | _, .snd _ _, next => do
    let p ← next 0 Env.empty
    pure p.2
  | _, .inl _ _, next => do
    let x ← next 0 Env.empty
    pure (Sum.inl x)
  | _, .inr _ _, next => do
    let y ← next 0 Env.empty
    pure (Sum.inr y)
  | _, .case _ _ _, next => do
    let s ← next 0 Env.empty
    M.step π.step
    match s with
    | .inl x => next 1 (Env.cons x Env.empty)
    | .inr y => next 2 (Env.cons y Env.empty)
  | _, .iter _, next => do
    let n ← next 0 Env.empty
    let f ← next 1 Env.empty
    let i ← next 2 Env.empty
    iterT M π f i n.down

/-- The call-by-value reading of the calls: run the argument, then the operation. -/
def queryCBV (M : Machine E Q ω) :
    CBVInterpretation (querySignature E) (PFunctor.FreeM Q) (Val B Q)
  | _, .query e, next => do
    let x ← next 0 Env.empty
    M.call e x

/-- The call-by-value reading of D in the machine `M` with the prices `π`. -/
abbrev cbv (M : Machine E Q ω) (π : Price B ω) :
    CBVInterpretation (signature E) (PFunctor.FreeM Q) (Val B Q) :=
  CBVInterpretation.sum (coreCBV M π) (queryCBV M)

/-- The machine of the evaluator: calls of `E` and a tick of the price of each step. -/
def Machine.timed (E : Effect B) (ω : Type u) : Machine E (Ticked E.toPFunctor ω) ω where
  call e x := CostD.call (P := E.toPFunctor) ⟨e, x⟩
  step := tick

/-- The machine of the denotation: calls of `E` and no record of steps. -/
def Machine.untimed (E : Effect B) : Machine E E.toPFunctor PUnit where
  call e x := PFunctor.FreeM.lift (P := E.toPFunctor) ⟨e, x⟩
  step _ := pure PUnit.unit

/-- The prices of the denotation, which records no step. -/
def Price.unit (B : Ground.{u}) : Price B PUnit := ⟨PUnit.unit, fun _ _ => PUnit.unit⟩

namespace Tm

variable {Γ : List (Ty B.G)} {a : Ty B.G}

/-- The evaluator: a tick of the price of each step. -/
def eval (π : Price B ω) (t : Tm E Γ a) (η : Env (Val B (Ticked E.toPFunctor ω)) Γ) :
    PFunctor.FreeM (Ticked E.toPFunctor ω) (Val B (Ticked E.toPFunctor ω) a) :=
  t.denoteCBV (cbv (Machine.timed E ω) π) η

/-- The denotation, a program over `E.toPFunctor` without ticks. -/
def den (t : Tm E Γ a) (η : Env (Val B E.toPFunctor) Γ) :
    PFunctor.FreeM E.toPFunctor (Val B E.toPFunctor a) :=
  t.denoteCBV (cbv (Machine.untimed E) (Price.unit B)) η

end Tm

end IPFunctor.CostD
