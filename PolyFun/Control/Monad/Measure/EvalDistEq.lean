/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Event

/-!
# Equality in distribution

`EvalDistEq mx my` says that two computations, possibly in different monads, give every event the
same probability. The relation needs no measurable space on the output. Under lawful semantics it
is equality of the output measures in the discrete structure (`evalDistEq_iff_evalDist_eq`), and
it gives equal output measures in every structure (`EvalDistEq.evalDist_eq`).

Equality in distribution is preserved by maps and binds (`EvalDistEq.map`, `EvalDistEq.bind`),
is an equivalence, and composes in `calc` through its `Trans` instance.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v v' v''

section defs

variable {m : Type → Type v} {m' : Type → Type v'} [EvalDistSemantics m] [EvalDistSemantics m']
  [Monad m] [Monad m'] {α : Type}

/-- Two computations are equal in distribution when every event has the same probability under
both. -/
def EvalDistEq (mx : m α) (my : m' α) : Prop :=
  ∀ p : α → Prop, prEvent (p <$> mx) = prEvent (p <$> my)

end defs

namespace EvalDistEq

variable {m : Type → Type v} {m' : Type → Type v'} {m'' : Type → Type v''}
  [Monad m] [Monad m'] [Monad m''] [EvalDistSemantics m] [EvalDistSemantics m']
  [EvalDistSemantics m''] {α β : Type}

/-- Equality in distribution gives every event the same probability. -/
theorem prEvent_eq {mx : m α} {my : m' α} (h : EvalDistEq mx my) (p : α → Prop) :
    prEvent (p <$> mx) = prEvent (p <$> my) :=
  h p

/-- Computations whose events all have the same probabilities are equal in distribution. -/
theorem of_forall_prEvent_eq {mx : m α} {my : m' α}
    (h : ∀ p : α → Prop, prEvent (p <$> mx) = prEvent (p <$> my)) : EvalDistEq mx my :=
  h

@[refl, simp]
theorem refl (mx : m α) : EvalDistEq mx mx := fun _ ↦ rfl

protected theorem rfl {mx : m α} : EvalDistEq mx mx := refl mx

@[symm]
theorem symm {mx : m α} {my : m' α} (h : EvalDistEq mx my) : EvalDistEq my mx :=
  fun p ↦ (h p).symm

theorem trans {mx : m α} {my : m' α} {mz : m'' α} (h₁ : EvalDistEq mx my)
    (h₂ : EvalDistEq my mz) : EvalDistEq mx mz :=
  fun p ↦ (h₁ p).trans (h₂ p)

instance : @Trans (m α) (m' α) (m'' α) EvalDistEq EvalDistEq EvalDistEq := ⟨trans⟩

instance : Std.Refl (α := m α) EvalDistEq := ⟨refl⟩

instance : Std.Symm (α := m α) EvalDistEq := ⟨fun _ _ ↦ symm⟩

instance : IsTrans (m α) EvalDistEq := ⟨fun _ _ _ ↦ trans⟩

/-- A common map preserves equality in distribution. -/
theorem map [LawfulMonad m] [LawfulMonad m'] {mx : m α} {my : m' α} (h : EvalDistEq mx my)
    (f : α → β) : EvalDistEq (f <$> mx) (f <$> my) :=
  fun p ↦ by simpa only [prEvent_map] using h fun x ↦ p (f x)

section lawful

variable [LawfulMonad m] [LawfulMonad m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m']

/-- Computations equal in distribution have the same output measure in every measurable
structure on their outputs. -/
theorem evalDist_eq [MeasurableSpace α] {mx : m α} {my : m' α} (h : EvalDistEq mx my) :
    evalDist mx = evalDist my := by
  ext s hs
  have hp : Measurable fun x : α ↦ x ∈ s := measurableSet_setOfPred.mp hs
  simpa using (prEvent_eq_evalDist mx _ hp).symm.trans ((h _).trans (prEvent_eq_evalDist my _ hp))

/-- Computations with the same output measure in a discrete structure are equal in
distribution. -/
theorem of_evalDist_eq {_ : MeasurableSpace α} [DiscreteMeasurableSpace α] {mx : m α}
    {my : m' α} (h : evalDist mx = evalDist my) : EvalDistEq mx my := fun p ↦ by
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, h]

/-- Equality in distribution is equality of the output measures in the discrete structure. -/
theorem _root_.evalDistEq_iff_evalDist_eq {mx : m α} {my : m' α} :
    EvalDistEq mx my ↔ (letI : MeasurableSpace α := ⊤; evalDist mx = evalDist my) :=
  letI : MeasurableSpace α := ⊤
  ⟨evalDist_eq, of_evalDist_eq⟩

/-- On a countable output type, equality in distribution is equality of every point mass. -/
theorem _root_.evalDistEq_iff_forall_prEvent_eq_output [Countable α] {mx : m α} {my : m' α} :
    EvalDistEq mx my ↔
      ∀ x, prEvent ((fun y ↦ y = x) <$> mx) = prEvent ((fun y ↦ y = x) <$> my) := by
  let : MeasurableSpace α := ⊤
  refine ⟨fun h x ↦ h (· = x), fun h ↦ of_evalDist_eq (Measure.ext_of_singleton fun x ↦ ?_)⟩
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  exact h x

/-- Binds of computations and continuations equal in distribution are equal in distribution. -/
theorem bind {mx : m α} {my : m' α} (h : EvalDistEq mx my) {f : α → m β} {g : α → m' β}
    (hfg : ∀ a, EvalDistEq (f a) (g a)) : EvalDistEq (mx >>= f) (my >>= g) := by
  let : MeasurableSpace α := ⊤
  intro p
  rw [map_bind, map_bind, prEvent_bind_of_discrete, prEvent_bind_of_discrete, h.evalDist_eq]
  exact lintegral_congr fun a ↦ hfg a p

end lawful

section sameMonad

/-- A common map is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem map_congr [LawfulMonad m] (f : α → β) {mx my : m α} (h : EvalDistEq mx my) :
    EvalDistEq (f <$> mx) (f <$> my) :=
  h.map f

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Bind is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem bind_congr {mx my : m α} {f g : α → m β} (h : EvalDistEq mx my)
    (hfg : ∀ a, EvalDistEq (f a) (g a)) : EvalDistEq (mx >>= f) (my >>= g) :=
  h.bind hfg

/-- A computation equal in distribution may replace the first draw of a bind. -/
theorem bind_left {mx my : m α} (h : EvalDistEq mx my) (f : α → m β) :
    EvalDistEq (mx >>= f) (my >>= f) :=
  h.bind fun _ ↦ .rfl

/-- Continuations equal in distribution may replace one another after a common draw. -/
theorem bind_right (mx : m α) {f g : α → m β} (hfg : ∀ a, EvalDistEq (f a) (g a)) :
    EvalDistEq (mx >>= f) (mx >>= g) :=
  EvalDistEq.rfl.bind hfg

end sameMonad

end EvalDistEq
