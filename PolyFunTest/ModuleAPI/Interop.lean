/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Semantics.Correspondence
public import PolyFun.ITree.Transition
public import Examples.Tutorials.ScopedExecution

/-! # Ordinary-import checks for reusable semantic and execution boundaries -/

open Control.Semantics Control.Transition

public section

namespace PolyFunTest.Interop

/-- Successful values represented inside a carrier that also has failure. -/
def represented : Nat ↪ Option Nat := ⟨some, Option.some_injective Nat⟩

private def increment : CertifiedMeaning represented represented where
  meaning := Option.map (· + 1)
  implementation := (· + 1)
  correct _ := rfl

example (x : Nat) : (increment.comp increment).meaning (some x) = some (x + 1 + 1) :=
  (increment.comp increment).correct x

example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract represented represented increment.meaning pre post ↔
      ∀ x, pre x → post x (x + 1) := increment.contract_iff pre post

-- Unrepresented failure cannot satisfy total correctness, even for a trivial postcondition.
example : ¬ DataContract represented represented (fun _ => none)
    (fun x => x = 0) (fun _ _ => True) := by
  intro h
  obtain ⟨_, he, _⟩ := h 0 rfl
  cases he

example {valid valid' : Nat → Prop} {f g : Nat → Nat}
    {m n : Option Nat → Option Nat}
    (hf : CorrespondsOn represented represented valid m f)
    (hg : CorrespondsOn represented represented valid' n g)
    (domain : ∀ x, valid x → valid' (f x)) :
    CorrespondsOn represented represented valid (n ∘ m) (g ∘ f) := hf.comp hg domain

private def countdown : Control.Transition Nat (Except String Nat)
  | 0 => .inl (.ok 0)
  | n + 1 => .inr n

example : run countdown 0 0 = .inr 0 := rfl
example : run countdown 1 0 = .inl (.ok 0) := rfl
example : run countdown 2 5 = .inr 3 := rfl
example : run countdown 6 5 = .inl (.ok 0) := rfl
example : run (fun (_ : Nat) => .inl (Except.error "failure" : Except String Nat)) 1 0 =
    .inl (.error "failure") := rfl

example (n : Nat) : run (fun s : Nat => (Sum.inr s : Nat ⊕ Nat)) n 4 = .inr 4 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

example (n m state : Nat) :
    run countdown (n + m) state = continueRun countdown m (run countdown n state) :=
  run_add countdown n m state

example (fuel state : Nat) :
    (toMachine countdown).runChunk tickHandler fuel (.inr state) =
      toChunk (run countdown fuel state) := runChunk_toMachine countdown fuel state

open Examples.ScopedPrograms IPFunctor.ScopedSignature

-- Nested lets use the outer binding through the correct de Bruijn position.
private def nested : Expr [] .nat :=
  .letE (.literal 4) (.letE (.literal 7) (.add (.var .zero) (.var (.succ .zero))))

private def nestedSupported : FirstOrder nested :=
  .letE (.literal 4) (.letE (.literal 7) (.add (.var .zero) (.var (.succ .zero))))

example : FirstOrder.runFree (FirstOrder.compile nestedSupported Env.empty) = 11 :=
  FirstOrder.compile_correct nestedSupported Env.empty

example (n : Nat) :
    Executes FirstOrder.step (FirstOrder.compile (FirstOrder.sumSupported n) Env.empty)
      ((sumTo n).denote algebra Env.empty) := by
  rw [← FirstOrder.compile_correct (FirstOrder.sumSupported n) Env.empty]
  exact FirstOrder.executes _

example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract (Function.Embedding.refl Nat) (Function.Embedding.refl Nat)
      FirstOrder.sumCertificate.meaning pre post ↔
      ∀ n, pre n → post n ((sumTo n).denote algebra Env.empty) :=
  FirstOrder.sumCertificate.contract_iff pre post

end PolyFunTest.Interop
