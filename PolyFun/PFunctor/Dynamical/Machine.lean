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

A **machine** is a `p`-dynamical system pointed by an initialisation map and
equipped with a partial (Moore) readout:

* `init : α → State` — where the machine starts, given an input;
* `output : State → Option β` — the value read off a state, `none` while running.

This is the interface-agnostic core of VCVio's `OracleMachine` (an oracle
machine is a `Machine` over an oracle spec's polynomial).

## Sequential composition (Spivak–Niu Example 6.41)

`seqComp M₁ M₂ : Machine p α β` runs `M₁ : Machine p α mid` until it produces a
`mid` value, then hands off to `M₂ : Machine p mid β`, over the *same* interface
`p`. Its state set is `M₁.State ⊕ M₂.State` — the "cascading menus" two-phase
machine. This is the structural content of VCVio's `OracleMachine.seqComp` and
the structural half of the sought `IsPolyTime.bind`: the definition (with its
`⊕`-state) is exactly what is currently missing downstream. The complementary
half — the Turing-machine running-time bound for the composed machine — is
computability content that stays in VCVio.

## Fuelled unrolling

`toComp k : State → FreeM p (Option β)` unrolls `k` steps of a machine into a
free-monad program (`none` on fuel exhaustion). It is the deterministic,
interface-generic core of VCVio's `runD` / `toComp`. `toComp_seqComp_inr` shows
the second phase of `seqComp` is faithful to `M₂`; the fuel-exact cross-phase
`bind` law is the next increment.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

/-- A **machine** over the interface `p`: a `p`-dynamical system pointed by an
`init` map and read out by a partial `output` (`none` while still running). The
interface-agnostic form of VCVio's `OracleMachine`. -/
structure Machine (p : PFunctor.{uA, uB}) (α : Type u) (β : Type u)
    extends DynSystem.{u} p where
  /-- Where the machine starts, given an input. -/
  init : α → State
  /-- The value read off a state; `none` while the machine is still running. -/
  output : State → Option β

namespace Machine

variable {p : PFunctor.{uA, uB}} {α β mid : Type u}

/-! ## Sequential composition -/

/-- Sequential composition of machines over a shared interface (Spivak–Niu
Example 6.41): run `M₁` until it outputs a `mid` value, then run `M₂` from that
value. The state set is `M₁.State ⊕ M₂.State`; phase one never reads out, phase
two carries the final output. -/
def seqComp (M₁ : Machine p α mid) (M₂ : Machine p mid β) : Machine p α β where
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

@[simp] theorem seqComp_expose_inr (M₁ : Machine p α mid) (M₂ : Machine p mid β)
    (s₂ : M₂.State) : (M₁.seqComp M₂).expose (Sum.inr s₂) = M₂.expose s₂ := rfl

@[simp] theorem seqComp_output_inr (M₁ : Machine p α mid) (M₂ : Machine p mid β)
    (s₂ : M₂.State) : (M₁.seqComp M₂).output (Sum.inr s₂) = M₂.output s₂ := rfl

@[simp] theorem seqComp_output_inl (M₁ : Machine p α mid) (M₂ : Machine p mid β)
    (s₁ : M₁.State) : (M₁.seqComp M₂).output (Sum.inl s₁) = none := rfl

@[simp] theorem seqComp_update_inr (M₁ : Machine p α mid) (M₂ : Machine p mid β)
    (s₂ : M₂.State) (d : p.B (M₂.expose s₂)) :
    (M₁.seqComp M₂).update (Sum.inr s₂) d = Sum.inr (M₂.update s₂ d) := rfl

/-! ## Fuelled unrolling -/

/-- Unroll `k` steps of a machine into a free-monad program: at each step, halt
with the current `output` if it is `some`, otherwise query the exposed position
and recurse on the answer. `none` marks fuel exhaustion. -/
def toComp (M : Machine p α β) : ℕ → M.State → FreeM p (Option β)
  | 0, _ => FreeM.pure none
  | k + 1, st => match M.output st with
    | some b => FreeM.pure (some b)
    | none => FreeM.roll (M.expose st) (fun d => M.toComp k (M.update st d))

@[simp] theorem toComp_zero (M : Machine p α β) (st : M.State) :
    M.toComp 0 st = FreeM.pure none := rfl

theorem toComp_succ (M : Machine p α β) (k : ℕ) (st : M.State) :
    M.toComp (k + 1) st = (match M.output st with
      | some b => FreeM.pure (some b)
      | none => FreeM.roll (M.expose st) (fun d => M.toComp k (M.update st d))) := rfl

/-- Faithfulness of the second phase: once `seqComp` has handed off to `M₂`, its
unrolling coincides with `M₂`'s. (The cross-phase `bind` law is the next step.) -/
theorem toComp_seqComp_inr (M₁ : Machine p α mid) (M₂ : Machine p mid β)
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

/-! ## Reachability -/

/-- `ReachableIn D n s s'`: state `s'` is reachable from `s` in exactly `n` steps
of the dynamical system `D` under some sequence of directions. -/
inductive ReachableIn (D : DynSystem p) : ℕ → D.State → D.State → Prop
  | refl (s : D.State) : ReachableIn D 0 s s
  | step {n : ℕ} {s s' : D.State} (d : p.B (D.expose s)) :
      ReachableIn D n (D.update s d) s' → ReachableIn D (n + 1) s s'

end Machine

end PFunctor
