/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.PointedMachine
public import PolyFun.PFunctor.Dynamical.RunN

/-!
# Examples for two-step systems and machine composition

Regression tests: `twoStep` preserves the state set, `M₁ ⨟ M₂` (`seqComp`) has
`⊕`-state and a faithful second phase, resolution certificates compose, and the
fuel-exact run law threads one ambient handler state through both phases.
-/

@[expose] public section

universe u v w

namespace PFunctor

variable {S : Type u} {p : PFunctor.{u, u}} {α β γ mid mid₁ mid₂ : Type u}

/-- The two-step system shares its state set with the original, as recorded by
its type: it is literally `Lens.speedup` on the system's lens. -/
example (s : DynSystem S p) : s.twoStep = Lens.speedup s := rfl

/-- The `⨟` notation is diagrammatic sequential composition. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) :
    M₁ ⨟ M₂ = M₁.seqComp M₂ := rfl

/-- Sequential composition has state `M₁.State ⊕ M₂.State`. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) :
    (M₁ ⨟ M₂).State = (M₁.State ⊕ M₂.State) := rfl

/-- Chained `⨟` notation parses to the left, fixing the corresponding nested sum state. -/
example (M₁ : PointedMachine p α mid₁) (M₂ : PointedMachine p mid₁ mid₂)
    (M₃ : PointedMachine p mid₂ γ) : M₁ ⨟ M₂ ⨟ M₃ = (M₁ ⨟ M₂) ⨟ M₃ := rfl

example (M₁ : PointedMachine p α mid₁) (M₂ : PointedMachine p mid₁ mid₂)
    (M₃ : PointedMachine p mid₂ γ) :
    (M₁ ⨟ M₂ ⨟ M₃).State = ((M₁.State ⊕ M₂.State) ⊕ M₃.State) := rfl

/-- The second phase of `seqComp` unrolls exactly like `M₂`. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) (s₂ : M₂.State) :
    (M₁ ⨟ M₂).toComp 3 (Sum.inr s₂) = M₂.toComp 3 s₂ :=
  PointedMachine.toComp_seqComp_inr M₁ M₂ 3 s₂

/-- The first phase exposes `M₁` and hands off to `M₂` exactly on `M₁`'s output. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) (s₁ : M₁.State) :
    (M₁ ⨟ M₂).toComp 1 (Sum.inl s₁)
      = FreeM.roll (M₁.expose s₁) (fun d =>
          (M₁ ⨟ M₂).toComp 0 (match M₁.output (M₁.update s₁ d) with
            | some m => Sum.inr (M₂.init m)
            | none => Sum.inl (M₁.update s₁ d))) :=
  PointedMachine.toComp_seqComp_inl M₁ M₂ 0 s₁

/-- A machine that halts immediately with output `b`. -/
def haltMachine (b : β) : PointedMachine X.{u, u} α β where
  State := PUnit
  expose := fun _ => PUnit.unit
  update := fun _ _ => PUnit.unit
  init := fun _ => PUnit.unit
  output := fun _ => some b

/-- A machine that makes exactly one query before returning `b`. -/
def oneQueryMachine (b : β) : PointedMachine X.{u, u} α β where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun _ _ => true
  init := fun _ => false
  output := fun
    | false => none
    | true => some b

/-! ## Collatz as a pointed machine -/

namespace Collatz

/-- One step of the Collatz iteration. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The Collatz iteration as a deterministic pointed machine over the clock
interface `X`. Its input selects the initial natural-number state, its unique
direction advances one Collatz step, and it reads out upon reaching `1`. -/
def machine : PointedMachine.{0, 0, 0, 0, 0} X.{0, 0} ℕ PUnit where
  State := ℕ
  expose := fun _ => PUnit.unit
  update := fun n _ => step n
  init := id
  output := fun n => if n = 1 then some PUnit.unit else none

/-- The Collatz conjecture says exactly that every positive input eventually
resolves in this pointed machine. The query budget is the number of Collatz
steps; reaching `1` itself requires no additional fuel because readout is free. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, machine.ResolvesIn k (machine.init n)

/-- Machine resolution recovers the usual reachability formulation: a Collatz
run terminates exactly when some iterate of `step` is `1`. -/
theorem eventually_resolves_iff_reaches_one (n : ℕ) :
    (∃ k, machine.ResolvesIn k (machine.init n)) ↔
      ∃ k, (step^[k]) n = 1 := by
  rw [machine.exists_resolvesIn_iff_exists_iterate_output_isSome]
  change (∃ k, (if (step^[k]) n = 1 then some PUnit.unit else none).isSome) ↔ _
  simp

/-- Thus the pointed-machine formulation is equivalent to the familiar
statement of the Collatz conjecture. -/
theorem conjecture_iff :
    Conjecture ↔ ∀ n : ℕ, 0 < n → ∃ k, (step^[k]) n = 1 := by
  simp only [Conjecture, eventually_resolves_iff_reaches_one]

/-- The distinguished initial state `1` is already resolved. -/
example : machine.ResolvesIn 0 (machine.init 1) := by
  simp [machine]

/-- The trajectory `3, 10, 5, 16, 8, 4, 2, 1` resolves in seven steps. -/
example : machine.ResolvesIn 7 (machine.init 3) := by
  simp [PointedMachine.ResolvesIn, machine, step]

/-- Once a trajectory resolves, monotonicity permits any larger fuel budget. -/
example : machine.ResolvesIn 20 (machine.init 3) :=
  (show machine.ResolvesIn 7 (machine.init 3) by
    simp [PointedMachine.ResolvesIn, machine, step]).mono (by omega)

end Collatz

/-- Machine states, inputs, and outputs may inhabit independent universes. -/
def universeSeparatedMachine {α : Type v} {β : Type w} (b : β) :
    PointedMachine X.{0, 0} α β where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun state _ => state
  init := fun _ => false
  output := fun _ => some b

/-- The one-query elaboration can likewise separate input and output universes;
the interface direction universe follows the output because `runWith` uses a
homogeneous monad. -/
def universeSeparatedOneQueryMachine {input : Type v} {out : Type w} (b : out) :
    PointedMachine X.{0, w} input out where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun _ _ => true
  init := fun _ => false
  output := fun
    | false => none
    | true => some b

/-- An immediate-output machine over the same homogeneous run interface. -/
def universeSeparatedRunHaltMachine {input : Type v} {out : Type w} (b : out) :
    PointedMachine X.{0, w} input out where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun state _ => state
  init := fun _ => false
  output := fun _ => some b

/-- The readout is free: a halted machine reads off its value at any fuel,
including zero. -/
example (b : β) : (haltMachine (α := α) b).toComp 1 PUnit.unit = FreeM.pure (some b) := rfl

example (b : β) : (haltMachine (α := α) b).toComp 0 PUnit.unit = FreeM.pure (some b) := rfl

/-- The machine fuel is a total structural roll bound, including at zero. -/
example (M : PointedMachine p α β) (k : ℕ) (s : M.State) :
    (M.toComp k s).IsTotalRollBound k :=
  M.isTotalRollBound_toComp k s

/-- A single roll cannot fit in a zero total-roll budget. -/
example (a : p.A) (r : p.B a → FreeM p β) :
    ¬ (FreeM.roll a r).IsTotalRollBound 0 := by
  simp

/-- Total structural bounds add through free-monad sequencing. -/
example (oa : FreeM p α) (ob : α → FreeM p β) (j k : ℕ)
    (ha : oa.IsTotalRollBound j) (hb : ∀ x, (ob x).IsTotalRollBound k) :
    (oa >>= ob).IsTotalRollBound (j + k) :=
  FreeM.isTotalRollBound_bind ha hb

/-- The resolved-output equation is available directly to `simp`. -/
example (M : PointedMachine p α β) (k : ℕ) (s : M.State) (b : β)
    (hb : M.output s = some b) : M.toComp k s = FreeM.pure (some b) := by
  simp [hb]

/-! ## Resolution certificates -/

/-- Zero fuel detects an already resolved state. -/
example (b : β) : (haltMachine (α := α) b).ResolvesIn 0 PUnit.unit := by
  simp [haltMachine]

/-- The one-query example has an exact budget: zero is insufficient and one
query resolves every answer path. -/
example (b : β) : ¬ (oneQueryMachine (α := α) b).ResolvesIn 0 false := by
  simp [oneQueryMachine]

example (b : β) : (oneQueryMachine (α := α) b).ResolvesIn 1 false := by
  simp [oneQueryMachine]

/-- Resolution is monotone, and its leaf characterization works in both
directions without exposing the recursive definition to clients. -/
example (b : β) : (oneQueryMachine (α := α) b).ResolvesIn 4 false :=
  (by simp [oneQueryMachine] : (oneQueryMachine (α := α) b).ResolvesIn 1 false).mono
    (by omega)

example (b : β) : ∃ z : FreeM X β,
    (oneQueryMachine (α := α) b).toComp 1 false = some <$> z :=
  PointedMachine.toComp_eq_map_some_of_resolvesIn (by simp [oneQueryMachine])

example (b : β) (z : FreeM X β)
    (h : (oneQueryMachine (α := α) b).toComp 1 false = some <$> z) :
    (oneQueryMachine (α := α) b).ResolvesIn 1 false :=
  PointedMachine.resolvesIn_of_toComp_eq_map_some h

/-- Once resolution is certified, surplus fuel does not change the run. -/
example (b : β) :
    (oneQueryMachine (α := α) b).runWith (m := Id) (fun _ => PUnit.unit) 4 false =
      (oneQueryMachine (α := α) b).runWith (m := Id) (fun _ => PUnit.unit) 1 false :=
  PointedMachine.runWith_eq_of_resolvesIn _ _ (by simp [oneQueryMachine]) (by omega)

/-! ## Machine-implements-program -/

/-- The immediate-halt machine implements the pure program, at any fuel. -/
example (b : β) (k : ℕ) :
    PointedMachine.Implements (haltMachine (α := α) b) (fun _ => (FreeM.pure b : FreeM X β)) k :=
  fun _ => PointedMachine.toComp_of_output_eq_some _ k rfl

/-- `Implements` yields the syntactic resolution certificate. -/
example (b : β) (k : ℕ) (x : α) :
    (haltMachine (α := α) b).ResolvesIn k ((haltMachine b).init x) :=
  PointedMachine.Implements.resolvesIn (z := fun _ => (FreeM.pure b : FreeM X β))
    (fun _ => PointedMachine.toComp_of_output_eq_some _ k rfl) x

/-- The step-synchronized proof method certifies `Implements` from a simulation relation. -/
example (b : β) :
    PointedMachine.Implements (haltMachine (α := α) b) (fun _ => (FreeM.pure b : FreeM X β)) 0 :=
  PointedMachine.implements_of_isSimulation
    (R := fun _ z => z = FreeM.pure b)
    { output_pure := fun _ _ h => by injection h with h; subst h; rfl
      output_roll := fun _ _ _ h => by cases h
      expose_eq := fun _ _ _ h => by cases h
      update_rel := fun _ _ _ h => by cases h }
    (fun _ => rfl) (fun _ => FreeM.isTotalRollBound_pure _ _)

/-! ## Compositional resolution and the fuel-exact run law -/

/-- A second-phase certificate lifts through the composite. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β)
    (k : ℕ) (s₂ : M₂.State) (h : M₂.ResolvesIn k s₂) :
    (M₁.seqComp M₂).ResolvesIn k (Sum.inr s₂) := h.seqComp_inr

/-- Exact-budget handoff: one query in each phase resolves the composite in
two queries. -/
example (y : mid) (b : β) (x : α) :
    ((oneQueryMachine (α := α) y).seqComp (oneQueryMachine (α := mid) b)).ResolvesIn 2
      (((oneQueryMachine (α := α) y).seqComp
        (oneQueryMachine (α := mid) b)).init x) := by
  exact PointedMachine.ResolvesIn.seqComp_init
    (show (oneQueryMachine (α := α) y).ResolvesIn 1 false by
      simp [oneQueryMachine])
    (fun _ => show (oneQueryMachine (α := mid) b).ResolvesIn 1 false by
      simp [oneQueryMachine])

/-- The certificate algebra also handles immediate handoff, early completion
with surplus phase-one fuel, and an already halted second phase. -/
example (y : mid) (b : β) (x : α) :
    ((haltMachine (α := α) y).seqComp (oneQueryMachine (α := mid) b)).ResolvesIn 1
      (((haltMachine (α := α) y).seqComp (oneQueryMachine (α := mid) b)).init x) := by
  exact PointedMachine.ResolvesIn.seqComp_init
    (show (haltMachine (α := α) y).ResolvesIn 0 PUnit.unit by
      simp [haltMachine])
    (fun _ => show (oneQueryMachine (α := mid) b).ResolvesIn 1 false by
      simp [oneQueryMachine])

example (y : mid) (b : β) (x : α) :
    ((oneQueryMachine (α := α) y).seqComp (haltMachine (α := mid) b)).ResolvesIn 3
      (((oneQueryMachine (α := α) y).seqComp
        (haltMachine (α := mid) b)).init x) := by
  exact PointedMachine.ResolvesIn.seqComp_init (k₁ := 3) (k₂ := 0)
    ((show (oneQueryMachine (α := α) y).ResolvesIn 1 false by
      simp [oneQueryMachine]).mono (by omega))
    (fun _ => show (haltMachine (α := mid) b).ResolvesIn 0 PUnit.unit by
      simp [haltMachine])

/-- Concrete run canaries cover exact-budget handoff, immediate handoff,
surplus fuel after early completion, and an already halted second phase. -/
example (y : mid) (b : β) (x : α) :
    ((oneQueryMachine (α := α) y).seqComp
      (oneQueryMachine (α := mid) b)).runWith (m := Id) (fun _ => PUnit.unit) 2
        (((oneQueryMachine (α := α) y).seqComp
          (oneQueryMachine (α := mid) b)).init x) = some b := rfl

example (y : mid) (b : β) (x : α) :
    ((haltMachine (α := α) y).seqComp
      (oneQueryMachine (α := mid) b)).runWith (m := Id) (fun _ => PUnit.unit) 1
        (((haltMachine (α := α) y).seqComp
          (oneQueryMachine (α := mid) b)).init x) = some b := rfl

example (y : mid) (b : β) (x : α) :
    ((oneQueryMachine (α := α) y).seqComp
      (oneQueryMachine (α := mid) b)).runWith (m := Id) (fun _ => PUnit.unit) 5
        (((oneQueryMachine (α := α) y).seqComp
          (oneQueryMachine (α := mid) b)).init x) = some b := rfl

example (y : mid) (b : β) (x : α) :
    ((oneQueryMachine (α := α) y).seqComp
      (haltMachine (α := mid) b)).runWith (m := Id) (fun _ => PUnit.unit) 1
        (((oneQueryMachine (α := α) y).seqComp
          (haltMachine (α := mid) b)).init x) = some b := rfl

/-- A lossy handler does not invalidate fuel irrelevance: it may discard a
query path, but the result is still stable after the structural resolution
budget. -/
def rejectHandler : Handler Option X := fun _ => none

example (b : β) :
    (oneQueryMachine (α := α) b).runWith rejectHandler 3 false = none := rfl

/-- A stateful handler is ambient to the composite. Both phases use the same
counter, so the final state records two answered queries rather than two fresh
per-phase counters. This is the relevant shape for a shared random-oracle cache
or transcript state. -/
def countingHandler : Handler (StateT ℕ Id) X := fun _ => do
  modify (· + 1)
  pure PUnit.unit

example :
    StateT.run
      (((oneQueryMachine (α := PUnit) 7).seqComp
        (oneQueryMachine (α := ℕ) 9)).runWith countingHandler 2
          (((oneQueryMachine (α := PUnit) 7).seqComp
            (oneQueryMachine (α := ℕ) 9)).init PUnit.unit)) 0 =
      (some 9, 2) := rfl

/-- The run law elaborates with independent machine-state/input universes and
the homogeneous handler/output universe required by `FreeM.mapM`. -/
example {input : Type v} {out : Type w} (y b : out) (x : input) :
    let M₁ := universeSeparatedOneQueryMachine (input := input) y
    let M₂ := universeSeparatedRunHaltMachine (input := out) b
    let h : Handler Id X.{0, w} := fun _ => PUnit.unit
    (M₁.seqComp M₂).runWith h 1
        ((M₁.seqComp M₂).init x) =
      M₁.runWith h 1 (M₁.init x) >>= fun r =>
        match r with
        | some y => M₂.runWith h 0 (M₂.init y)
        | none => pure none := by
  simp only
  let h : Handler Id X.{0, w} := fun _ => PUnit.unit
  exact PointedMachine.runWith_seqComp_init
    (universeSeparatedOneQueryMachine (input := input) y)
    (universeSeparatedRunHaltMachine (input := out) b) h (k₁ := 1) 0 x
    (by simp [universeSeparatedOneQueryMachine])
    (fun _ => by simp [universeSeparatedRunHaltMachine])

end PFunctor
