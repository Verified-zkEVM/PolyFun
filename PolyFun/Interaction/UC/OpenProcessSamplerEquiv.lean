/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcess

/-!
# Sampler-aware equivalence of open processes

`OpenProcessActivationEquiv` deliberately erases packet identity and
`stepSampler` effects, so no distributional observation can factor through it.
This module defines the strengthening that retains both, relative to an
abstract relation family on `m`-computations.

`MonadRelFamily m` axiomatizes what a downstream semantics must supply: a
per-type equivalence on `m`-computations respecting `map` and one-sided
`bind`.  PolyFun never names a concrete instance beyond `MonadRelFamily.top`;
the intended downstream instantiation is equality of denotations (for example
`R x y := evalDist x = evalDist y` for a measure-valued `evalDist`), for which
every field holds.

`IsSamplerBisimulation R p₁ p₂ rel` demands a *strong* step matching: related
states carry a bijection of complete step paths preserving silence, boundary
traces, and successor relatedness, and relating the whole-step sampled path
computations through `R`.  This is deliberately stronger than the delay
matching of `OpenProcessActivationEquiv` — the structural reassociation
witnesses behind the factorization laws are one-to-one, so nothing weaker is
needed, and the strength is what lets sampled paths be compared step by step.
`OpenProcessSamplerEquiv.toActivationEquiv` forgets back down.

Scheduler-transport facts (which concrete `R`-relations hold between
reassociated scheduler draws) are deliberately *hypotheses* of the
sampler-aware factorization theorems, not theorems of this module: a single
shared scheduler does not preserve per-step scheduling distributions across
reassociation, so the transport facts genuinely depend on the downstream
observation.  See the instantiation gates in `docs/wiki/uc.md`.
-/

public section

universe u v v₁ v₂ v₃ w w'

namespace Interaction
namespace UC

/-! ## Relation families on the sampling monad -/

/-- A per-type equivalence on `m`-computations respecting `map` and one-sided
`bind`: the interface a downstream semantics supplies to compare sampler
effects.  Equality of any monad-morphism image satisfies every field. -/
structure MonadRelFamily (m : Type w → Type w') [Monad m] where
  /-- The relation at each result type. -/
  rel : ∀ {α : Type w}, m α → m α → Prop
  /-- The relation is reflexive. -/
  refl : ∀ {α : Type w} (x : m α), rel x x
  /-- The relation is symmetric. -/
  symm : ∀ {α : Type w} {x y : m α}, rel x y → rel y x
  /-- The relation is transitive. -/
  trans : ∀ {α : Type w} {x y z : m α}, rel x y → rel y z → rel x z
  /-- Mapping a function over related computations preserves the relation. -/
  map_congr : ∀ {α β : Type w} (f : α → β) {x y : m α},
    rel x y → rel (f <$> x) (f <$> y)
  /-- Binding related computations against a common continuation preserves
  the relation. -/
  bind_congr : ∀ {α β : Type w} {x y : m α} (f : α → m β),
    rel x y → rel (x >>= f) (y >>= f)

/-- The everything-relation: forgetting sampler effects entirely.  At this
instantiation the sampler-aware equivalence retains exactly packet identity
over the activation notion. -/
def MonadRelFamily.top (m : Type w → Type w') [Monad m] : MonadRelFamily m where
  rel _ _ := True
  refl := by intros; trivial
  symm := by intros; trivial
  trans := by intros; trivial
  map_congr := by intros; trivial
  bind_congr := by intros; trivial

/-- The everything-relation holds between any two computations. -/
@[simp]
theorem MonadRelFamily.top_rel {m : Type w → Type w'} [Monad m]
    {α : Type w} (x y : m α) : (MonadRelFamily.top m).rel x y :=
  trivial

/-! ## Sampler bisimulation -/

/-- A strong sampler bisimulation between open processes on a common
boundary: related states carry a bijection of complete step paths preserving
silence, boundary traces, and successor relatedness, and relating the sampled
path computations through `R`. -/
structure IsSamplerBisimulation {m : Type w → Type w'} [Monad m]
    {Party : Type u} {Δ : PortBoundary} (R : MonadRelFamily m)
    (p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ)
    (p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ)
    (rel : p₁.Proc → p₂.Proc → Prop) : Prop where
  /-- Each related pair of states admits a path bijection preserving the
  security-visible step data. -/
  step_equiv : ∀ s₁ s₂, rel s₁ s₂ →
    ∃ e : TypeTree.Path (p₁.step s₁).tree ≃ TypeTree.Path (p₂.step s₂).tree,
      (∀ tr : TypeTree.Path (p₁.step s₁).tree,
        IsSilentStep p₁ s₁ tr ↔ IsSilentStep p₂ s₂ (e tr)) ∧
      (∀ tr : TypeTree.Path (p₁.step s₁).tree,
        OpenNodeContext.boundaryTrace (p₁.step s₁).tree
            (p₁.step s₁).semantics tr =
          OpenNodeContext.boundaryTrace (p₂.step s₂).tree
            (p₂.step s₂).semantics (e tr)) ∧
      (∀ tr : TypeTree.Path (p₁.step s₁).tree,
        rel ((p₁.step s₁).next tr) ((p₂.step s₂).next (e tr))) ∧
      R.rel ((fun tr => e tr) <$>
          TypeTree.samplePath (p₁.step s₁).tree (p₁.stepSampler s₁))
        (TypeTree.samplePath (p₂.step s₂).tree (p₂.stepSampler s₂))

/-- Whole-system sampler equivalence: a sampler bisimulation whose relation is
total on both state spaces. -/
def OpenProcessSamplerEquiv {m : Type w → Type w'} [Monad m]
    {Party : Type u} {Δ : PortBoundary} (R : MonadRelFamily m)
    (p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ)
    (p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ) : Prop :=
  ∃ rel, IsSamplerBisimulation R p₁ p₂ rel ∧
    (∀ s₁, ∃ s₂, rel s₁ s₂) ∧ (∀ s₂, ∃ s₁, rel s₁ s₂)

namespace OpenProcessSamplerEquiv

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m]
  {Party : Type u} {Δ : PortBoundary} {R : MonadRelFamily m}

/-- Every open process is sampler equivalent to itself. -/
protected theorem refl (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessSamplerEquiv R p p := by
  refine ⟨Eq, ⟨?_⟩, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩⟩
  rintro s _ rfl
  refine ⟨Equiv.refl _, fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  have heq : (fun tr => (Equiv.refl (TypeTree.Path (p.step s).tree)) tr) <$>
      TypeTree.samplePath (p.step s).tree (p.stepSampler s) =
      TypeTree.samplePath (p.step s).tree (p.stepSampler s) := by
    simp
  rw [heq]
  exact R.refl _

/-- Sampler equivalence is symmetric. -/
protected theorem symm
    {p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ}
    {p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ}
    (h : OpenProcessSamplerEquiv R p₁ p₂) : OpenProcessSamplerEquiv R p₂ p₁ := by
  obtain ⟨rel, hbisim, htot₁, htot₂⟩ := h
  refine ⟨fun s₂ s₁ => rel s₁ s₂, ⟨?_⟩,
    fun s₂ => htot₂ s₂, fun s₁ => htot₁ s₁⟩
  intro s₂ s₁ hrel
  obtain ⟨e, hsil, htr, hnext, hsam⟩ := hbisim.step_equiv s₁ s₂ hrel
  refine ⟨e.symm, ?_, ?_, ?_, ?_⟩
  · intro tr
    have h' := hsil (e.symm tr)
    rw [Equiv.apply_symm_apply] at h'
    exact h'.symm
  · intro tr
    have h' := htr (e.symm tr)
    rw [Equiv.apply_symm_apply] at h'
    exact h'.symm
  · intro tr
    have := hnext (e.symm tr)
    rwa [Equiv.apply_symm_apply] at this
  · have h' := R.map_congr (fun tr => e.symm tr) (R.symm hsam)
    have heq : (fun tr => e.symm tr) <$> ((fun tr => e tr) <$>
        TypeTree.samplePath (p₁.step s₁).tree (p₁.stepSampler s₁)) =
        TypeTree.samplePath (p₁.step s₁).tree (p₁.stepSampler s₁) := by
      simp [Functor.map_map]
    rw [heq] at h'
    exact h'

/-- Sampler equivalence composes transitively. -/
protected theorem trans
    {p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ}
    {p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ}
    {p₃ : OpenProcess.{u, v₃, w, w'} m Party Δ}
    (h₁₂ : OpenProcessSamplerEquiv R p₁ p₂)
    (h₂₃ : OpenProcessSamplerEquiv R p₂ p₃) :
    OpenProcessSamplerEquiv R p₁ p₃ := by
  obtain ⟨r₁₂, hb₁₂, h₁₂tot₁, h₁₂tot₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, h₂₃tot₁, h₂₃tot₂⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃, ⟨?_⟩, ?_, ?_⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩
    obtain ⟨e₁, hsil₁, htr₁, hnext₁, hsam₁⟩ := hb₁₂.step_equiv s₁ s₂ hr₁₂
    obtain ⟨e₂, hsil₂, htr₂, hnext₂, hsam₂⟩ := hb₂₃.step_equiv s₂ s₃ hr₂₃
    refine ⟨e₁.trans e₂, ?_, ?_, ?_, ?_⟩
    · intro tr
      exact (hsil₁ tr).trans (hsil₂ (e₁ tr))
    · intro tr
      exact (htr₁ tr).trans (htr₂ (e₁ tr))
    · intro tr
      exact ⟨(p₂.step s₂).next (e₁ tr), hnext₁ tr, hnext₂ (e₁ tr)⟩
    · have h' := R.map_congr (fun tr => e₂ tr) hsam₁
      have heq : (fun tr => e₂ tr) <$> ((fun tr => e₁ tr) <$>
          TypeTree.samplePath (p₁.step s₁).tree (p₁.stepSampler s₁)) =
          (fun tr => (e₁.trans e₂) tr) <$>
            TypeTree.samplePath (p₁.step s₁).tree (p₁.stepSampler s₁) := by
        simp [Functor.map_map]
      rw [heq] at h'
      exact R.trans h' hsam₂
  · intro s₁
    obtain ⟨s₂, hr₁₂⟩ := h₁₂tot₁ s₁
    obtain ⟨s₃, hr₂₃⟩ := h₂₃tot₁ s₂
    exact ⟨s₃, s₂, hr₁₂, hr₂₃⟩
  · intro s₃
    obtain ⟨s₂, hr₂₃⟩ := h₂₃tot₂ s₃
    obtain ⟨s₁, hr₁₂⟩ := h₁₂tot₂ s₂
    exact ⟨s₁, s₂, hr₁₂, hr₂₃⟩

/-! ## Forgetting to activation equivalence -/

omit [LawfulMonad m] in
/-- Sampler equivalence refines activation equivalence: the one-to-one path
matching is in particular a strong (hence delay) bisimulation of the
activation-labelled transition systems. -/
theorem toActivationEquiv
    {p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ}
    {p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ}
    (h : OpenProcessSamplerEquiv R p₁ p₂) :
    OpenProcessActivationEquiv p₁ p₂ := by
  obtain ⟨rel, hbisim, htot₁, htot₂⟩ := h
  refine ⟨rel, Control.IsStrongBisimulation.toDelay ⟨?_, ?_⟩, htot₁, htot₂⟩
  · rintro s₁ s₂ hrel label t₁ ⟨tr, hlabel, hnext⟩
    obtain ⟨e, hsil, _, hnextrel, _⟩ := hbisim.step_equiv s₁ s₂ hrel
    refine ⟨(p₂.step s₂).next (e tr), ⟨e tr, ?_, rfl⟩, hnext ▸ hnextrel tr⟩
    by_cases hs : IsSilentStep p₁ s₁ tr
    · rw [OpenProcess.activationLTS_label_of_silent p₂ s₂ (e tr)
        ((hsil tr).mp hs), ← hlabel,
        OpenProcess.activationLTS_label_of_silent p₁ s₁ tr hs]
    · rw [OpenProcess.activationLTS_label_of_not_silent p₂ s₂ (e tr)
        (fun hc => hs ((hsil tr).mpr hc)), ← hlabel,
        OpenProcess.activationLTS_label_of_not_silent p₁ s₁ tr hs]
  · rintro s₂ s₁ hrel label t₂ ⟨tr, hlabel, hnext⟩
    obtain ⟨e, hsil, _, hnextrel, _⟩ := hbisim.step_equiv s₁ s₂ hrel
    refine ⟨(p₁.step s₁).next (e.symm tr), ⟨e.symm tr, ?_, rfl⟩, ?_⟩
    · by_cases hs : IsSilentStep p₂ s₂ tr
      · have hs₁ : IsSilentStep p₁ s₁ (e.symm tr) :=
          (hsil (e.symm tr)).mpr ((Equiv.apply_symm_apply e tr).symm ▸ hs)
        rw [OpenProcess.activationLTS_label_of_silent p₁ s₁ _ hs₁, ← hlabel,
          OpenProcess.activationLTS_label_of_silent p₂ s₂ tr hs]
      · have hs₁ : ¬ IsSilentStep p₁ s₁ (e.symm tr) := fun hc =>
          hs ((Equiv.apply_symm_apply e tr) ▸ (hsil (e.symm tr)).mp hc)
        rw [OpenProcess.activationLTS_label_of_not_silent p₁ s₁ _ hs₁,
          ← hlabel,
          OpenProcess.activationLTS_label_of_not_silent p₂ s₂ tr hs]
    · have h' := (Equiv.apply_symm_apply e tr) ▸ hnextrel (e.symm tr)
      exact hnext ▸ h'

end OpenProcessSamplerEquiv

end UC
end Interaction
