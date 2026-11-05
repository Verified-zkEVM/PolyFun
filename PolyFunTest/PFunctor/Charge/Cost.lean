/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic
public import PolyFun.PFunctor.Free.Cost.Loops
public import PolyFun.PFunctor.Free.Cost.Support

/-!
# Worst-case costs, loops and restricted sequencing

Checks for `PolyFun.PFunctor.Free.Cost.Value` and its companions:

* `cost_bound` computes the worst-case cost of a concrete program and decides its budget;
* a call with no answers is charged by the worst-case cost;
* `q` hash queries in a loop and one group operation have the per-kind budget
  `q • hash + group`;
* the cost of a handler's implementation is computed by `cost_bound`;
* sequencing needs the continuation's budget only on reachable results;
* charges that agree on the calls a program makes give the same bound.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeCost

/-! ## Concrete programs -/

/-- Two kinds of call, each with three answers. -/
abbrev Pq : PFunctor := ⟨Bool, fun _ => Fin 3⟩

noncomputable def chg : Pq.A → ℕ∞ := fun a => cond a 2 1

def chgN : Pq.A → ℕ := fun a => cond a 2 1

def prog : FreeM Pq Nat := do
  let x ← FreeM.lift (P := Pq) true
  let y ← FreeM.lift (P := Pq) false
  if x.val = 0 then
    let _ ← FreeM.lift (P := Pq) true
    pure y.val
  else pure (x.val + y.val)

example : cost chg prog = 5 := by
  cost_bound [prog, chg]

example : IsChargeBound prog chgN 5 := by
  cost_bound [prog, chgN]

example : ¬ IsChargeBound prog chgN 4 := by
  cost_bound [prog, chgN]

/-- A natural-number budget is a bound on the cost in `ℕ∞`. -/
example : cost (fun a => (chgN a : ℕ∞)) prog ≤ 5 :=
  isChargeBound_iff_cost_natCast_le.1 (by cost_bound [prog, chgN])

/-- One call that can never be answered. -/
abbrev Dead : PFunctor := ⟨Unit, fun _ => PEmpty⟩

def stuck : FreeM Dead PEmpty := FreeM.lift ()

/-- The worst-case cost charges the call. -/
example : cost (fun _ => (1 : ℕ∞)) stuck = 1 := by
  simp [stuck]

/-! ## Loops -/

/-- Two kinds of query. -/
inductive Op
  | hash
  | group
  deriving DecidableEq

/-- An interface with hash and group queries, each with four answers. -/
abbrev Iface : PFunctor := ⟨Op, fun _ => Fin 4⟩

/-- Count each kind of query separately. -/
def kind (o : Iface.A) : Op → ℕ := Pi.single o 1

/-- The body of the hash loop. -/
def hashOnce : FreeM Iface PUnit := do
  let _ ← FreeM.lift (P := Iface) Op.hash
  pure ()

/-- `q` hash queries in a loop, then one group operation. -/
def adv (q : ℕ) : FreeM Iface PUnit := do
  forM (List.range q) fun _ => hashOnce
  let _ ← FreeM.lift (P := Iface) Op.group
  pure ()

theorem adv_isChargeBound (q : ℕ) :
    (adv q).IsChargeBound kind (q • kind Op.hash + kind Op.group) := by
  refine IsChargeBound.bind (B₁ := q • kind Op.hash) ?_ fun _ => ?_
  · have h := isChargeBound_forM_const (xs := List.range q) (f := fun _ => hashOnce)
      (c := kind) (B := kind Op.hash) fun _ _ => by simp [hashOnce]
    simpa using h
  · simp

/-! ## Handler costs -/

/-- A single interface with two answers. -/
abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls, returning the second answer. -/
def doubled : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

/-- The doubled handler costs two per call. -/
example : handlerCost (fun _ => (1 : ℕ∞)) doubled = fun _ => 2 := by
  funext a
  cost_bound [handlerCost, doubled]

/-! ## Reachable results and provenance -/

/-- A continuation that is expensive except at the result `0`, which is the only one reached. -/
def pricey (n : ℕ) : FreeM Coin Bool :=
  if n = 0 then FreeM.lift (P := Coin) () else do
    let _ ← FreeM.lift (P := Coin) ()
    let _ ← FreeM.lift (P := Coin) ()
    FreeM.lift (P := Coin) ()

example : (FreeM.bind (pure 0 : FreeM Coin ℕ) pricey).IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  have := (isChargeBound_pure (c := fun _ : Coin.A => (1 : ℕ)) (B := 0) (0 : ℕ)).bind_supp
    (f := pricey) (B₂ := 1) fun a ha => by
      obtain rfl : a = 0 := ha
      cost_bound [pricey]
  simpa using this

/-- Two operations with a single answer each. -/
abbrev Two : PFunctor := ⟨Bool, fun _ => PUnit⟩

/-- A program that only calls `true` sees only the charge at `true`. -/
example (x : FreeM Two PUnit) (hS : x.CallsIn {true}) (B s : ℕ) :
    x.IsChargeBound (fun b => if b then 1 else 7) B s ↔ x.IsChargeBound (fun _ => 1) B s :=
  IsChargeBound.congr_charge hS fun a ha => by simp_all

/-- The calls occurring in `prog` are exactly those at `true` and `false`; a program calls only in
a set exactly when every call occurring in it lies there. -/
example : prog.MayCall true ∧ prog.CallsIn {a | prog.MayCall a} :=
  ⟨Or.inl rfl, callsIn_setOf_mayCall prog⟩

example (x : FreeM Two PUnit) : x.CallsIn {true} ↔ ∀ a, x.MayCall a → a = true :=
  callsIn_iff_forall_mayCall x

/-! ## Restricted answers -/

/-- Flip a coin; on `false`, make two more calls. -/
def flipThenMore : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then pure true else do
    let _ ← FreeM.lift (P := Coin) ()
    let _ ← FreeM.lift (P := Coin) ()
    pure false

/-- Over the answers a sampler supported on `true` can return, the worst case is one call. -/
example : costUnder (fun _ => (1 : ℕ∞)) (fun _ b => b = true) flipThenMore ≤ 1 :=
  isChargeBoundUnder_iff_costUnder_le.1 (by simp [flipThenMore])

/-- The restricted cost never exceeds the worst-case cost, which counts the `false` branch. -/
example (x : FreeM Coin Bool) :
    costUnder (fun _ => (1 : ℕ∞)) (fun _ b => b = true) x ≤ cost (fun _ => (1 : ℕ∞)) x :=
  costUnder_le_cost x

end PolyFunTest.ChargeCost
