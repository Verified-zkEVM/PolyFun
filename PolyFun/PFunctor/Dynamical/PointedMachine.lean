/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic
public import PolyFun.PFunctor.Free.Basic

/-!
# Pointed machines and sequential composition

A **pointed machine** is a `p`-dynamical system pointed by an initialisation
map and equipped with a partial (Moore) readout:

* `init : α → State` — where the machine starts, given an input;
* `output : State → Option β` — the value read off a state, `none` while running.

This is the interface-agnostic core of VCVio's `OracleMachine` (an oracle
machine is a `PointedMachine` over an oracle spec's polynomial).

## Sequential composition (Spivak–Niu Example 6.41)

`seqComp M₁ M₂ : PointedMachine p α β` runs `M₁ : PointedMachine p α mid` until it produces a
`mid` value, then hands off to `M₂ : PointedMachine p mid β`, over the *same* interface
`p`. Its state set is `M₁.State ⊕ M₂.State` — the "cascading menus" two-phase
machine. This is the structural content of VCVio's `OracleMachine.seqComp` and
the structural half of the sought `IsPolyTime.bind`: the definition (with its
`⊕`-state) is exactly what is currently missing downstream. The complementary
half — the Turing-machine running-time bound for the composed machine — is
computability content that stays in VCVio.

## Fuelled unrolling

`toComp k : State → FreeM p (Option β)` unrolls a machine into a free-monad
program that makes at most `k` queries; the readout is free, so at fuel
exhaustion the current output is still read off (`none` marks a machine that is
genuinely unresolved after `k` answered queries). Fuel thereby counts queries
exactly — the `k`-step unrolling resolves precisely when the machine is steady
within `k` queries, the identification that makes steadiness fuel a total query
bound downstream. It is the deterministic, interface-generic core of VCVio's
`runD` / `toComp`. `toComp_seqComp_inr` shows the second phase of `seqComp` is
faithful to `M₂`; the fuel-exact cross-phase `bind` law is the next increment.
-/

@[expose] public section

universe u v uA uB

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). The deterministic case is a plain section
of the polynomial — `Handler Id q` is `Section q` unbundled — while a
probabilistic monad gives a randomized oracle. This is the flat-interface
notion; the tree-shaped `Interaction.Spec.Sampler` decorates a different
substrate and should not be conflated with it. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) := (a : q.A) → m (q.B a)

/-- A **pointed machine** over the interface `p`: a `p`-dynamical system pointed
by an `init` map and read out by a partial `output` (`none` while still
running). The interface-agnostic form of VCVio's `OracleMachine`. -/
structure PointedMachine (p : PFunctor.{uA, uB}) (α : Type u) (β : Type u)
    extends DynSystem.{u} p where
  /-- Where the machine starts, given an input. -/
  init : α → State
  /-- The value read off a state; `none` while the machine is still running. -/
  output : State → Option β

namespace PointedMachine

variable {p : PFunctor.{uA, uB}} {α β mid : Type u}

/-! ## Sequential composition -/

/-- Sequential composition of machines over a shared interface (Spivak–Niu
Example 6.41): run `M₁` until it outputs a `mid` value, then run `M₂` from that
value. The state set is `M₁.State ⊕ M₂.State`; phase one never reads out, phase
two carries the final output. -/
def seqComp (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) : PointedMachine p α β where
  State := M₁.State ⊕ M₂.State
  expose := fun s => match s with
    | Sum.inl s₁ => M₁.expose s₁
    | Sum.inr s₂ => M₂.expose s₂
  update := fun s => match s with
    | Sum.inl s₁ => fun d =>
        let s₁' := M₁.update s₁ d
        match M₁.output s₁' with
        | some m => Sum.inr (M₂.init m)
        | none => Sum.inl s₁'
    | Sum.inr s₂ => fun d => Sum.inr (M₂.update s₂ d)
  init := fun x =>
    match M₁.output (M₁.init x) with
    | some m => Sum.inr (M₂.init m)
    | none => Sum.inl (M₁.init x)
  output := fun s => match s with
    | Sum.inl _ => none
    | Sum.inr s₂ => M₂.output s₂

@[simp] theorem seqComp_expose_inr (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (s₂ : M₂.State) : (M₁.seqComp M₂).expose (Sum.inr s₂) = M₂.expose s₂ := rfl

@[simp] theorem seqComp_output_inr (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (s₂ : M₂.State) : (M₁.seqComp M₂).output (Sum.inr s₂) = M₂.output s₂ := rfl

@[simp] theorem seqComp_output_inl (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (s₁ : M₁.State) : (M₁.seqComp M₂).output (Sum.inl s₁) = none := rfl

@[simp] theorem seqComp_update_inr (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (s₂ : M₂.State) (d : p.B (M₂.expose s₂)) :
    (M₁.seqComp M₂).update (Sum.inr s₂) d = Sum.inr (M₂.update s₂ d) := rfl

/-! ## Fuelled unrolling -/

/-- Unroll a machine into a free-monad program making at most `k` queries: at
each step, halt with the current `output` if it is `some`, otherwise query the
exposed position and recurse on the answer. The readout is free, so fuel
exhaustion still reads off the current output; `none` marks a machine that is
unresolved after `k` answered queries. -/
def toComp (M : PointedMachine p α β) : ℕ → M.State → FreeM p (Option β)
  | 0, st => FreeM.pure (M.output st)
  | k + 1, st => match M.output st with
    | some b => FreeM.pure (some b)
    | none => FreeM.roll (M.expose st) (fun d => M.toComp k (M.update st d))

@[simp] theorem toComp_zero (M : PointedMachine p α β) (st : M.State) :
    M.toComp 0 st = FreeM.pure (M.output st) := rfl

theorem toComp_succ (M : PointedMachine p α β) (k : ℕ) (st : M.State) :
    M.toComp (k + 1) st = (match M.output st with
      | some b => FreeM.pure (some b)
      | none => FreeM.roll (M.expose st) (fun d => M.toComp k (M.update st d))) := rfl

/-- A resolved state unrolls to its readout at any fuel: the readout is free,
so extra fuel is never consumed. -/
theorem toComp_of_output_eq_some (M : PointedMachine p α β) (k : ℕ) {st : M.State}
    {b : β} (hb : M.output st = some b) : M.toComp k st = FreeM.pure (some b) := by
  cases k with
  | zero => rw [toComp_zero, hb]
  | succ k => rw [toComp_succ, hb]

/-- First phase, one step: while in `M₁` (a left state), `seqComp` exposes `M₁`'s
position and, after `M₁`'s update, hands off to `M₂` exactly when `M₁` produces an
output. Together with `toComp_seqComp_inr` this fixes the whole operational
behaviour of the composite: run `M₁`, then run `M₂` from `M₁`'s output. This is
the structural content of the sought `IsPolyTime.bind` (the composite is a
faithful sequential composition); the fuel-threaded single-`bind` form is not a
plain fuel-additive law — `runWith_output_some` supplies the fuel irrelevance it
needs. -/
theorem toComp_seqComp_inl (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (k : ℕ) (s₁ : M₁.State) :
    (M₁.seqComp M₂).toComp (k + 1) (Sum.inl s₁)
      = FreeM.roll (M₁.expose s₁) (fun d =>
          (M₁.seqComp M₂).toComp k (match M₁.output (M₁.update s₁ d) with
            | some m => Sum.inr (M₂.init m)
            | none => Sum.inl (M₁.update s₁ d))) := rfl

/-- Faithfulness of the second phase: once `seqComp` has handed off to `M₂`, its
unrolling coincides with `M₂`'s. -/
theorem toComp_seqComp_inr (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (k : ℕ) (s₂ : M₂.State) :
    (M₁.seqComp M₂).toComp k (Sum.inr s₂) = M₂.toComp k s₂ := by
  induction k generalizing s₂ with
  | zero => rfl
  | succ k ih =>
    -- `seqComp`'s output/expose/update on `inr s₂` are definitionally `M₂`'s, so the
    -- one-step unrolling of the left side is defeq to this `M₂`-flavoured form.
    change (match M₂.output s₂ with
          | some b => FreeM.pure (some b)
          | none => FreeM.roll (M₂.expose s₂)
              (fun d => (M₁.seqComp M₂).toComp k (Sum.inr (M₂.update s₂ d))))
        = M₂.toComp (k + 1) s₂
    rw [toComp_succ]
    cases M₂.output s₂ with
    | some b => rfl
    | none => exact congrArg (FreeM.roll (M₂.expose s₂)) (funext fun d => ih (M₂.update s₂ d))

/-! ## Monad-parametric fuelled run

`toComp` unrolls a machine into the *syntactic* free monad. Interpreting that
unrolling in any monad `m` — via a handler `h : (a : q.A) → m (q.B a)` that
resolves each exposed position monadically — gives the machine a run in `m`. This
is the interface-generic core of VCVio's deterministic `runD` (`m = Option`) and
probabilistic `runK` (`m = SPMF`); the actual ω-limit of the fuel-indexed chain
needs an order/ωCPO on `m` and stays with the concrete instance. The direction
universe is pinned to `β`'s (`q : PFunctor.{uA, u}`) so `FreeM.mapM` applies. -/

section Run

variable {q : PFunctor.{uA, u}} {m : Type u → Type v} [Monad m]

/-- The **monad-parametric fuelled run**: interpret the `k`-step unrolling
`toComp` in the monad `m` through a handler `h`. `toComp` is the syntactic case
`m = FreeM q`, `h = FreeM.liftA`. -/
def runWith (M : PointedMachine q α β) (h : Handler m q) (k : ℕ) (s : M.State) : m (Option β) :=
  FreeM.mapM h (M.toComp k s)

@[simp] theorem runWith_zero (M : PointedMachine q α β) (h : Handler m q) (s : M.State) :
    M.runWith h 0 s = pure (M.output s) := rfl

/-- One-step unfolding of the run: halt with the current output if it is `some`,
else resolve the exposed position with `h` and recurse. The generic shadow of
VCVio's `runLimit_fix`. -/
theorem runWith_succ (M : PointedMachine q α β) (h : Handler m q) (k : ℕ) (s : M.State) :
    M.runWith h (k + 1) s = (match M.output s with
      | some b => pure (some b)
      | none => h (M.expose s) >>= fun d => M.runWith h k (M.update s d)) := by
  unfold runWith
  rw [toComp_succ]
  cases M.output s <;> rfl

/-- **Fuel irrelevance**: once a state has resolved (`output = some b`), any
fuel produces `pure (some b)` — the readout is free and extra fuel does not
change the run. The generic shadow of VCVio's `runK_eq_of_apply_none_eq_zero`,
the run-extension lemma sequential composition consumes. -/
theorem runWith_output_some (M : PointedMachine q α β) (h : Handler m q) (k : ℕ) {s : M.State}
    {b : β} (hb : M.output s = some b) : M.runWith h k s = pure (some b) := by
  unfold runWith
  rw [toComp_of_output_eq_some M k hb]
  rfl

end Run

end PointedMachine

end PFunctor
