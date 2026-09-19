/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Backend
public import ComplexityBackends.CslibSingleTape.Counting

/-!
# Per-step adequacy of the cost envelope

`Backend.quantitative.cost code x` is the certified time polynomial evaluated at the encoded input
length. It is an upper envelope on a real machine run: some halting run of the underlying
single-tape machine from the encoded input to the encoded output takes at most `cost` steps
(`cost_adequate`), and because the machine is deterministic and the halting configuration is
irreducible, every halting run takes the same number of steps (`run_length_unique`). A prover can
therefore only overstate cost, never understate it (`run_length_le_cost`).

This is the per-step half of machine adequacy. Linking the three step maps of a realization into
one whole-program machine whose run length meets the additive envelope remains open.
-/

public section

open PFunctor Cslib.Turing Cslib.Turing.SingleTapeTM

namespace ComplexityBackends.CslibSingleTape

/-- Two step-counted runs of a deterministic relation to an irreducible endpoint have the same
length. -/
theorem _root_.Relation.RelatesInSteps.eq_of_deterministic {α : Type*} {r : α → α → Prop}
    (hdet : ∀ {a b c : α}, r a b → r a c → b = c) {b : α} (hb : ∀ c, ¬ r b c) :
    ∀ {a : α} {n m : ℕ},
      Relation.RelatesInSteps r a b n → Relation.RelatesInSteps r a b m → n = m := by
  intro a n
  induction n generalizing a with
  | zero =>
      intro m h₁ h₂
      obtain rfl := Relation.RelatesInSteps.zero h₁
      cases m with
      | zero => rfl
      | succ k =>
          obtain ⟨c, hc, -⟩ := Relation.RelatesInSteps.succ' h₂
          exact absurd hc (hb c)
  | succ n ih =>
      intro m h₁ h₂
      obtain ⟨c, hac, hcb⟩ := Relation.RelatesInSteps.succ' h₁
      cases m with
      | zero =>
          obtain rfl := Relation.RelatesInSteps.zero h₂
          exact absurd hac (hb c)
      | succ k =>
          obtain ⟨c', hac', hc'b⟩ := Relation.RelatesInSteps.succ' h₂
          obtain rfl := hdet hac hac'
          rw [ih hcb hc'b]

namespace Backend

/-- The transition relation of a single-tape machine is deterministic. -/
theorem transitionRelation_deterministic {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] (tm : SingleTapeTM Symbol) {c₁ c₂ c₃ : tm.Cfg}
    (h₂ : tm.TransitionRelation c₁ c₂) (h₃ : tm.TransitionRelation c₁ c₃) :
    c₂ = c₃ := by
  rw [TransitionRelation] at h₂ h₃
  rw [h₂] at h₃
  exact Option.some.inj h₃

variable {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}

/-- **Per-step adequacy.** The cost of a realizer at an input bounds an actual halting run of the
underlying machine: some run of length at most `cost` reaches the halting configuration holding
the encoded output. -/
theorem cost_adequate (code : EncPolyTime a b f) (x : A) :
    ∃ t ≤ quantitative.cost code x,
      Relation.RelatesInSteps code.polyTime.tm.TransitionRelation
        (code.polyTime.tm.initCfg (a x)) (code.polyTime.tm.haltCfg (b (f x))) t := by
  obtain ⟨t, ht, hrun⟩ := code.polyTime.outputsFunInTime (a x)
  refine ⟨t, ht.trans ?_, ?_⟩
  · rw [cost_eq_time_envelope, EncPolyTime.time_eq_poly]
    exact code.polyTime.bounds _
  · rwa [code.map_encode x] at hrun

/-- Every halting run of a realizer's machine on an encoded input has the same length. -/
theorem run_length_unique (code : EncPolyTime a b f) (x : A) {t t' : ℕ}
    (h : Relation.RelatesInSteps code.polyTime.tm.TransitionRelation
      (code.polyTime.tm.initCfg (a x)) (code.polyTime.tm.haltCfg (b (f x))) t)
    (h' : Relation.RelatesInSteps code.polyTime.tm.TransitionRelation
      (code.polyTime.tm.initCfg (a x)) (code.polyTime.tm.haltCfg (b (f x))) t') : t = t' :=
  Relation.RelatesInSteps.eq_of_deterministic (r := code.polyTime.tm.TransitionRelation)
    (transitionRelation_deterministic code.polyTime.tm)
    (not_transitionRelation_haltCfg code.polyTime.tm (b (f x))) h h'

/-- **A prover can only overstate cost.** Every halting run of a realizer's machine on an encoded
input takes at most `cost` steps. -/
theorem run_length_le_cost (code : EncPolyTime a b f) (x : A) {t : ℕ}
    (h : Relation.RelatesInSteps code.polyTime.tm.TransitionRelation
      (code.polyTime.tm.initCfg (a x)) (code.polyTime.tm.haltCfg (b (f x))) t) :
    t ≤ quantitative.cost code x := by
  obtain ⟨t₀, ht₀, h₀⟩ := cost_adequate code x
  rw [run_length_unique code x h h₀]
  exact ht₀

end Backend

end ComplexityBackends.CslibSingleTape
