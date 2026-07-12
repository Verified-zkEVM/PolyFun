/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import PolyFun.Interaction.UC.OpenProcess
import PolyFun.Control.Bisimulation

/-!
# `OpenProcessIso` as an instance of the generic weak bisimulation

`Interaction.UC.OpenProcessIso` (the weak bisimulation used to prove the concrete
process model's monoidal laws) is exactly the generic `Control.WeakBisim`
(`Control/Bisimulation.lean`) at the transition system `openLTS` whose moves are
the transcripts out of each state, silent iff the step is silent
(`IsSilentStep`), with the trivial one-point observation alphabet `PUnit`.

This file makes that identification precise (`openProcessIso_iff_weakBisim`) and,
as its payoff, re-derives `OpenProcessIso`'s reflexivity, symmetry, and
transitivity from the *generic* `Control.WeakBisim` laws
(`OpenProcessIso.refl'`/`.symm'`/`.trans'`). In particular the transitivity that
`OpenProcess.lean` proves by hand with a `Classical.em` stutter argument is
recovered from the axiom-free generic `Control.WeakBisim.trans`, so the
per-model proof is no longer the only route — it is one instance of a reusable
theory shared with `ITree.WeakBisim`.
-/

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

variable {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}

open Classical in
/--
The transition system underlying an open process: states are the residual
`Proc`, the moves out of a state `s` are the transcripts of its open step, a
move's successor is the process continuation `next`, and a move is silent (`none`)
exactly when the step is silent (`IsSilentStep`). The observation alphabet is the
one-point type `PUnit` — `OpenProcessIso` distinguishes only silent from visible
steps, not *which* observation a visible step makes.
-/
noncomputable def openLTS (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    Control.LTS.{v, w, 0} PUnit where
  State := p.Proc
  Move s := Spec.Transcript (p.step s).spec
  next s tr := (p.step s).next tr
  label s tr := if IsSilentStep p s tr then none else some PUnit.unit

@[simp]
theorem openLTS_next (p : OpenProcess.{u, v, w, w'} m Party Δ) (s : p.Proc)
    (tr : Spec.Transcript (p.step s).spec) :
    (openLTS p).next s tr = (p.step s).next tr := rfl

theorem openLTS_label_eq_none {p : OpenProcess.{u, v, w, w'} m Party Δ} {s : p.Proc}
    {tr : Spec.Transcript (p.step s).spec} :
    (openLTS p).label s tr = none ↔ IsSilentStep p s tr := by
  simp only [openLTS]
  split <;> simp_all

theorem openLTS_label_eq_some {p : OpenProcess.{u, v, w, w'} m Party Δ} {s : p.Proc}
    {tr : Spec.Transcript (p.step s).spec} {o : PUnit} :
    (openLTS p).label s tr = some o ↔ ¬ IsSilentStep p s tr := by
  simp only [openLTS]
  split <;> simp_all

/--
`OpenProcessIso` is precisely the generic weak bisimulation on `openLTS`. Both
are `∃ rel, …`; the clause sets agree once `label = none` is read as
`IsSilentStep` and `label = some ()` as its negation (the observation being the
unique point of `PUnit`).
-/
theorem openProcessIso_iff_weakBisim
    (p₁ p₂ : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessIso p₁ p₂ ↔ Control.WeakBisim (openLTS p₁) (openLTS p₂) := by
  constructor
  · rintro ⟨rel, htot, hsurj, hfs, hfv, hbs, hbv⟩
    refine ⟨rel, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact htot
    · exact hsurj
    · intro s₁ s₂ hr μ hμ
      exact hfs s₁ s₂ hr μ (openLTS_label_eq_none.mp hμ)
    · intro s₁ s₂ hr μ o hμ
      obtain ⟨μ₂, hv₂, hn⟩ := hfv s₁ s₂ hr μ (openLTS_label_eq_some.mp hμ)
      exact ⟨μ₂, openLTS_label_eq_some.mpr hv₂, hn⟩
    · intro s₁ s₂ hr μ hμ
      exact hbs s₁ s₂ hr μ (openLTS_label_eq_none.mp hμ)
    · intro s₁ s₂ hr μ o hμ
      obtain ⟨μ₁, hv₁, hn⟩ := hbv s₁ s₂ hr μ (openLTS_label_eq_some.mp hμ)
      exact ⟨μ₁, openLTS_label_eq_some.mpr hv₁, hn⟩
  · rintro ⟨rel, hb⟩
    refine ⟨rel, hb.total_left, hb.total_right, ?_, ?_, ?_, ?_⟩
    · intro s₁ s₂ hr tr hsilent
      exact hb.silent_forward hr tr (openLTS_label_eq_none.mpr hsilent)
    · intro s₁ s₂ hr tr hvisible
      obtain ⟨μ₂, hlbl, hn⟩ :=
        hb.visible_forward hr tr PUnit.unit (openLTS_label_eq_some.mpr hvisible)
      exact ⟨μ₂, openLTS_label_eq_some.mp hlbl, hn⟩
    · intro s₁ s₂ hr tr hsilent
      exact hb.silent_backward hr tr (openLTS_label_eq_none.mpr hsilent)
    · intro s₁ s₂ hr tr hvisible
      obtain ⟨μ₁, hlbl, hn⟩ :=
        hb.visible_backward hr tr PUnit.unit (openLTS_label_eq_some.mpr hvisible)
      exact ⟨μ₁, openLTS_label_eq_some.mp hlbl, hn⟩

namespace OpenProcessIso

/-- Reflexivity of `OpenProcessIso`, obtained from the generic
`Control.WeakBisim.refl`. -/
theorem refl' (p : OpenProcess.{u, v, w, w'} m Party Δ) : OpenProcessIso p p :=
  (openProcessIso_iff_weakBisim p p).mpr (Control.WeakBisim.refl _)

/-- Symmetry of `OpenProcessIso`, obtained from the generic
`Control.WeakBisim.symm`. -/
theorem symm' {p₁ p₂ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h : OpenProcessIso p₁ p₂) : OpenProcessIso p₂ p₁ :=
  (openProcessIso_iff_weakBisim p₂ p₁).mpr
    (Control.WeakBisim.symm ((openProcessIso_iff_weakBisim p₁ p₂).mp h))

/-- **Transitivity of `OpenProcessIso`, re-derived from the axiom-free generic
`Control.WeakBisim.trans`** — no per-model `Classical.em` stutter argument
needed. -/
theorem trans' {p₁ p₂ p₃ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h₁₂ : OpenProcessIso p₁ p₂) (h₂₃ : OpenProcessIso p₂ p₃) : OpenProcessIso p₁ p₃ :=
  (openProcessIso_iff_weakBisim p₁ p₃).mpr
    (Control.WeakBisim.trans
      ((openProcessIso_iff_weakBisim p₁ p₂).mp h₁₂)
      ((openProcessIso_iff_weakBisim p₂ p₃).mp h₂₃))

end OpenProcessIso

end UC
end Interaction
