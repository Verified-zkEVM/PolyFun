/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedPrograms
public import PolyFun.Control.Semantics.Correspondence
public import PolyFun.ITree.Transition

/-!
# A strict evaluator for scoped arithmetic and bounded loops

The supported fragment retains the existing scoped syntax and supplies checked
evidence for its first-order constructors. Evaluation sequences computations
through a free program of unit steps. The same transition adapter and semantic
certificate interfaces apply to lazy frontends with partial semantic carriers.
-/

public section

namespace Examples.ScopedPrograms

open IPFunctor IPFunctor.ScopedSignature PFunctor

/-- Evidence that a natural-number term uses the first-order evaluator's fragment. -/
inductive FirstOrder : {Γ : List Ty} → Expr Γ .nat → Type 1 where
  | var {Γ : List Ty} (x : ScopedVar Γ .nat) : FirstOrder (.var x)
  | literal {Γ} (n : Nat) : FirstOrder (Expr.literal (Γ := Γ) n)
  | add {Γ} {x y : Expr Γ .nat} : FirstOrder x → FirstOrder y → FirstOrder (.add x y)
  | letE {Γ} {x : Expr Γ .nat} {body : Expr (.nat :: Γ) .nat} :
      FirstOrder x → FirstOrder body → FirstOrder (.letE x body)
  | loop {Γ} (n : Nat) {seed : Expr Γ .nat} {body : Expr (.nat :: .nat :: Γ) .nat} :
      FirstOrder seed → FirstOrder body → FirstOrder (.loop n seed body)

namespace FirstOrder

/-- A free program whose only request is one internal evaluation step. -/
abbrev Program := FreeM PFunctor.y.{0, 0} Nat

/-- An evaluator step followed by the remainder of the program. -/
@[expose] def pulse (program : Program) : Program := .liftBind PUnit.unit (fun _ => program)

/-- Interpret unit steps without any external effect. -/
@[expose] def runFree (program : Program) : Nat := program.liftM Control.Transition.tickHandler

/-- A returned free value needs no handler observation. -/
@[simp] theorem runFree_pure (x : Nat) : runFree (pure x) = x := rfl

/-- An internal pulse preserves the eventual result. -/
@[simp] theorem runFree_pulse (program : Program) : runFree (pulse program) = runFree program := rfl

/-- Strict sequencing agrees with composition of native results. -/
theorem runFree_bind (program : Program) (f : Nat → Program) :
    runFree (program >>= f) = runFree (f (runFree program)) := by
  exact FreeM.liftM_bind _ _ _

/-- Execute a bounded loop, sequencing each body before the following iteration. -/
@[expose] def loopProgram (body : Nat → Nat → Program) (seed : Nat) : Nat → Program
  | 0 => .pure seed
  | n + 1 => loopProgram body seed n >>= body n

/-- Bounded evaluation preserves the native loop recurrence. -/
theorem runFree_loopProgram (body : Nat → Nat → Program) (seed n : Nat) :
    runFree (loopProgram body seed n) =
      Nat.rec seed (fun i value => runFree (body i value)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [loopProgram, runFree_bind, ih]

/-- Interpret supported syntax strictly, keeping environments and binders typed. -/
@[expose] def compile {Γ : List Ty} {e : Expr Γ .nat} (h : FirstOrder e)
    (ρ : Env Ty.Value Γ) : Program := pulse (match h with
  | .var x => .pure (ρ x)
  | .literal n => .pure n
  | .add x y => do
      let a ← compile x ρ
      let b ← compile y ρ
      pure (a + b)
  | .letE x body => do
      let value ← compile x ρ
      compile body (Env.cons value ρ)
  | .loop n seed body => do
      let value ← compile seed ρ
      loopProgram (fun i value => compile body (Env.cons i (Env.cons value ρ))) value n)

/-- Every supported term's strict evaluator has its scoped algebraic meaning. -/
theorem compile_correct {Γ : List Ty} {e : Expr Γ .nat} (h : FirstOrder e)
    (ρ : Env Ty.Value Γ) : runFree (compile h ρ) = e.denote algebra ρ := by
  induction h with
  | var x => rfl
  | literal n => rfl
  | add x y ihx ihy =>
      simp only [compile, runFree_pulse, runFree_bind, ihx, ihy]
      rfl
  | letE x body ihx ihbody =>
      simp only [compile, runFree_pulse, runFree_bind, ihx]
      exact ihbody _
  | loop n seed body ihseed ihbody =>
      simp only [compile, runFree_pulse, runFree_bind, ihseed, runFree_loopProgram]
      simp_rw [ihbody]
      rfl

/-- Inspect one free-program node, retaining the continuation as the exact residual. -/
@[expose] def step : Control.Transition Program Nat
  | .pure value => .inl value
  | .liftBind _ next => .inr (next PUnit.unit)

/-- Every transition preserves the interpreted result. -/
theorem step_meaning (program : Program) :
    runFree program = Sum.elim id runFree (step program) := by
  cases program <;> rfl

/-- Finite free programs terminate in their interpreted result. -/
theorem executes (program : Program) :
    Control.Transition.Executes step program (runFree program) := by
  induction program with
  | pure value => exact .done rfl
  | liftBind op next ih => exact .next rfl (ih PUnit.unit)

/-- Successful execution agrees with the source algebra. -/
theorem execution_correct {Γ : List Ty} {e : Expr Γ .nat} (h : FirstOrder e)
    (ρ : Env Ty.Value Γ) {result : Nat}
    (execution : Control.Transition.Executes step (compile h ρ) result) :
    result = e.denote algebra ρ :=
  (Control.Transition.Executes.meaning step runFree id step_meaning execution).symm.trans
    (compile_correct h ρ)

/-- The first-order fragment of the tutorial's summation program. -/
@[expose] def sumSupported (n : Nat) : FirstOrder (sumTo n) :=
  .loop n (.literal 0) (.add (.var .zero) (.var (.succ .zero)))

/-- A second frontend's all-input certificate uses no Cryptol types or primitives. -/
@[expose] def sumCertificate : Control.Semantics.CertifiedMeaning
    (Function.Embedding.refl Nat) (Function.Embedding.refl Nat) where
  meaning n := runFree (compile (sumSupported n) Env.empty)
  implementation n := (sumTo n).denote algebra Env.empty
  correct n := compile_correct (sumSupported n) Env.empty

end FirstOrder
end Examples.ScopedPrograms
