/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Model

/-!
# Declarative rule programs and their executable checker

A rule program specifies ordered premises, an explicit rejection, or a conclusion.
`Derives` is its inductive inference semantics; `evaluate` is its executable checker.
Their equivalence is proved by induction, rather than defining derivability as success.
-/

@[expose] public section

namespace Parliament

/-- Ordered executable premises with an explicit rejection or conclusion. -/
inductive RuleProgram (α : Type) where
  | reject (error : RuleError)
  | require (condition : Bool) (error : RuleError) (rest : RuleProgram α)
  | conclude (result : α)

namespace RuleProgram

/-- Compose rule programs while preserving premise and rejection order. -/
def bind {α β : Type} (p : RuleProgram α) (f : α → RuleProgram β) : RuleProgram β :=
  match p with
  | .reject e => .reject e
  | .require c e rest => .require c e (bind rest f)
  | .conclude a => f a

instance : Monad RuleProgram where
  pure := .conclude
  bind := bind

/-- Require one Boolean premise with its specific rejection reason. -/
def ensure (condition : Bool) (error : RuleError) : RuleProgram Unit :=
  .require condition error (.conclude ())

/-- Require an optional value, rejecting if it is absent. -/
def need {α : Type} (value : Option α) (error : RuleError) : RuleProgram α :=
  match value with
  | none => .reject error
  | some value => .conclude value

/-- Execute ordered premises and return the first error or the derived result. -/
def evaluate {α : Type} : RuleProgram α → Except RuleError α
  | .reject e => .error e
  | .require c e rest => if c then evaluate rest else .error e
  | .conclude a => .ok a

/-- An inference requires evidence for every premise on the path to its conclusion. -/
inductive Derives {α : Type} : RuleProgram α → α → Prop where
  | conclude (a : α) : Derives (.conclude a) a
  | premise {c : Bool} {e : RuleError} {rest : RuleProgram α} {a : α}
      (holds : c = true) (continuation : Derives rest a) : Derives (.require c e rest) a

theorem evaluate_iff {α : Type} (p : RuleProgram α) (a : α) :
    evaluate p = .ok a ↔ Derives p a := by
  induction p with
  | reject e =>
    constructor
    · simp [evaluate]
    · intro h; cases h
  | conclude value =>
    constructor
    · intro h
      have : value = a := by simpa [evaluate] using h
      subst a
      exact .conclude value
    · intro h; cases h; rfl
  | require c e rest ih =>
    constructor
    · intro h
      cases c with
      | false => simp [evaluate] at h
      | true => exact .premise rfl (ih.mp (by simpa [evaluate] using h))
    · intro h
      cases h with
      | premise holds continuation => simp [evaluate, holds, ih.mpr continuation]

theorem derives_unique {α : Type} {p : RuleProgram α} {a b : α}
    (ha : Derives p a) (hb : Derives p b) : a = b := by
  have h := (evaluate_iff p a).mpr ha
  have h' := (evaluate_iff p b).mpr hb
  exact Except.ok.inj (h.symm.trans h')

theorem evaluate_bind {α β : Type} (p : RuleProgram α) (f : α → RuleProgram β) :
    evaluate (p.bind f) = (evaluate p).bind (fun a => evaluate (f a)) := by
  induction p with
  | reject e => rfl
  | conclude a => rfl
  | require c e rest ih => cases c <;> simp [bind, evaluate, ih, Except.bind]

end RuleProgram

end Parliament
