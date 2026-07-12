/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Logic.Basic
public import Batteries.Tactic.Lint

/-!
# Generic silent-absorbing bisimulation over a labeled transition system

Silent-step-absorbing bisimulation is written out by hand in more than one place
in this library, each time with its own reflexivity/symmetry/transitivity proof
— in particular a bespoke `Classical.em` stutter argument for transitivity. The
clearest example is `Interaction.UC.OpenProcessIso`, whose seven-clause relation
absorbs silent (unactivated / scheduler) process steps and matches visible ones.

This file factors that construction out into a reusable theory. A `LTS Obs` is a
labeled transition system: a state space, a family of moves out of each state, a
successor for each move, and a label that is either **silent** (`none`, a τ-move)
or a **visible** observation (`some o`). `IsWeakBisim L₁ L₂ rel` is the
six-clause bisimulation on a relation between two systems sharing an observation
alphabet, and `WeakBisim L₁ L₂` is its existential closure. Reflexivity,
symmetry, and **transitivity are proved once, generically**
(`WeakBisim.refl`/`.symm`/`.trans`); downstream relations obtain their metatheory
by exhibiting an `LTS` and reusing these lemmas rather than re-proving them.
`Interaction.UC.OpenProcessIso` is exactly this relation at its process
transition system (see `Interaction/UC/OpenProcessBisim.lean`, where its `refl`,
`symm`, and `trans` are re-derived from the lemmas here).

## Design

* Visible moves must be matched by visible moves carrying the *same*
  observation, so `WeakBisim` is observation-preserving. Taking `Obs := PUnit`
  recovers the coarse "silent-vs-visible only" notion, which is exactly
  `OpenProcessIso`.
* Silent moves may be matched by *any* move on the other side or **stuttered**
  (the other side stays put) — this is the silent-absorbing content.
* A visible move is matched **immediately** by a visible move (no silent steps
  are absorbed *around* a visible action).
* The relation is heterogeneous (the two systems may have different state
  types), so `trans` genuinely composes across a middle system.

## Relation to other bisimulations in the library

Because silence here is a decidable `Option` label rather than an opaque
predicate, the transitivity proof is **constructive** — it reads the middle
move's label to classify it and needs no `Classical.em`, unlike the per-model
hand-rolled proof it replaces. Situated in the standard spectrum:

* `ITree.Bisim` (`= Eq`, definitional strong bisimulation) is *finer* than this
  notion.
* This notion (silent-absorbing, **visible matched immediately**) is exactly
  `OpenProcessIso`.
* `ITree.WeakBisim` (`eutt`) is *coarser*: it additionally absorbs silent steps
  *around* visible actions (e.g. `pure r ≈ step (pure r)`), so it is **not** an
  instance of `IsWeakBisim` — capturing it would require a visible-up-to-silent
  clause. It is a natural extension of this framework, not the same relation.

## Main definitions

* `LTS Obs` — a labeled transition system with observation alphabet `Obs`.
* `IsWeakBisim L₁ L₂ rel` — the six bisimulation clauses on `rel`.
* `WeakBisim L₁ L₂` — `∃ rel, IsWeakBisim L₁ L₂ rel`.
* `WeakBisim.refl`, `WeakBisim.symm`, `WeakBisim.trans` — the equivalence laws,
  proved once for all transition systems. `trans` is the single generic
  (constructive) stutter argument.
-/

@[expose] public section

universe u v w

namespace Control

/--
A labeled transition system with observation alphabet `Obs`: a state space, a
family of outgoing moves at each state, a successor state for each move, and a
label marking each move as silent (`none`) or visible with a concrete
observation (`some o`).
-/
-- The state, move, and observation universes are genuinely independent.
@[nolint checkUnivs]
structure LTS (Obs : Type w) where
  /-- The states of the system. -/
  State : Type u
  /-- The moves available out of each state. -/
  Move : State → Type v
  /-- The successor reached by taking a move. -/
  next : (s : State) → Move s → State
  /-- The observation label of a move: `none` is a silent (τ) move; `some o` is a
  visible move observing `o`. -/
  label : (s : State) → Move s → Option Obs

variable {Obs : Type w}

/--
`IsWeakBisim L₁ L₂ rel` states that `rel` is a weak bisimulation between the
transition systems `L₁` and `L₂`:

* every state on each side is related to some state on the other (`total_*`);
* a silent move on one side is matched by *some* move on the other (preserving
  the relation) or **stuttered** — the other side stays put (`silent_*`);
* a visible move is matched by a visible move carrying the *same* observation,
  preserving the relation (`visible_*`).
-/
structure IsWeakBisim (L₁ L₂ : LTS Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop where
  /-- Every `L₁`-state is related to some `L₂`-state. -/
  total_left : ∀ s₁, ∃ s₂, rel s₁ s₂
  /-- Every `L₂`-state is related to some `L₁`-state. -/
  total_right : ∀ s₂, ∃ s₁, rel s₁ s₂
  /-- A silent `L₁`-move is matched by some `L₂`-move or stuttered. -/
  silent_forward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ μ : L₁.Move s₁, L₁.label s₁ μ = none →
    (∃ μ₂ : L₂.Move s₂, rel (L₁.next s₁ μ) (L₂.next s₂ μ₂)) ∨ rel (L₁.next s₁ μ) s₂
  /-- A visible `L₁`-move is matched by an equally-labeled visible `L₂`-move. -/
  visible_forward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ (μ : L₁.Move s₁) (o : Obs),
    L₁.label s₁ μ = some o →
      ∃ μ₂ : L₂.Move s₂, L₂.label s₂ μ₂ = some o ∧ rel (L₁.next s₁ μ) (L₂.next s₂ μ₂)
  /-- A silent `L₂`-move is matched by some `L₁`-move or stuttered. -/
  silent_backward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ μ : L₂.Move s₂, L₂.label s₂ μ = none →
    (∃ μ₁ : L₁.Move s₁, rel (L₁.next s₁ μ₁) (L₂.next s₂ μ)) ∨ rel s₁ (L₂.next s₂ μ)
  /-- A visible `L₂`-move is matched by an equally-labeled visible `L₁`-move. -/
  visible_backward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ (μ : L₂.Move s₂) (o : Obs),
    L₂.label s₂ μ = some o →
      ∃ μ₁ : L₁.Move s₁, L₁.label s₁ μ₁ = some o ∧ rel (L₁.next s₁ μ₁) (L₂.next s₂ μ)

/--
`WeakBisim L₁ L₂` holds when there is a weak bisimulation relating the two
transition systems: some relation satisfying all six `IsWeakBisim` clauses,
witnessing that every state of each system is matched by a state of the other.
-/
def WeakBisim (L₁ L₂ : LTS Obs) : Prop :=
  ∃ rel : L₁.State → L₂.State → Prop, IsWeakBisim L₁ L₂ rel

namespace WeakBisim

/-- Every transition system is weakly bisimilar to itself, witnessed by `Eq`. -/
protected theorem refl (L : LTS Obs) : WeakBisim L L :=
  ⟨Eq, by
    refine ⟨fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rintro s₁ _ rfl μ _; exact .inl ⟨μ, rfl⟩
    · rintro s₁ _ rfl μ o h; exact ⟨μ, h, rfl⟩
    · rintro _ s₂ rfl μ _; exact .inl ⟨μ, rfl⟩
    · rintro _ s₂ rfl μ o h; exact ⟨μ, h, rfl⟩⟩

/-- Weak bisimilarity is symmetric: swap the two systems and the relation, which
exchanges the forward and backward clauses. -/
protected theorem symm {L₁ L₂ : LTS Obs}
    (h : WeakBisim L₁ L₂) : WeakBisim L₂ L₁ := by
  obtain ⟨rel, hb⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂,
    { total_left := hb.total_right
      total_right := hb.total_left
      silent_forward := fun hr μ hμ => hb.silent_backward hr μ hμ
      visible_forward := fun hr μ o hμ => hb.visible_backward hr μ o hμ
      silent_backward := fun hr μ hμ => hb.silent_forward hr μ hμ
      visible_backward := fun hr μ o hμ => hb.visible_forward hr μ o hμ }⟩

/-- **Transitivity of weak bisimilarity**, proved once for all transition
systems. The composite relation `∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃` witnesses the
middle system. When a silent move is matched by a middle-system move `μ₂`, that
move is classified silent or visible by simply reading its `label` — so, unlike
the per-model hand-rolled proofs, the stutter argument here needs **no**
`Classical.em`. This is the single generic proof that `ITree.WeakBisim` and
`OpenProcessIso` both inherit. -/
protected theorem trans {L₁ L₂ L₃ : LTS Obs}
    (h₁₂ : WeakBisim L₁ L₂) (h₂₃ : WeakBisim L₂ L₃) : WeakBisim L₁ L₃ := by
  obtain ⟨r₁₂, hb₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s₁
    obtain ⟨s₂, h₂⟩ := hb₁₂.total_left s₁
    obtain ⟨s₃, h₃⟩ := hb₂₃.total_left s₂
    exact ⟨s₃, s₂, h₂, h₃⟩
  · intro s₃
    obtain ⟨s₂, h₂⟩ := hb₂₃.total_right s₃
    obtain ⟨s₁, h₁⟩ := hb₁₂.total_right s₂
    exact ⟨s₁, s₂, h₁, h₂⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ hμ
    rcases hb₁₂.silent_forward hr₁₂ μ hμ with ⟨μ₂, hn₁₂⟩ | hstay
    · cases hlbl : L₂.label s₂ μ₂ with
      | none =>
        rcases hb₂₃.silent_forward hr₂₃ μ₂ hlbl with ⟨μ₃, hn₂₃⟩ | hstay₂₃
        · exact .inl ⟨μ₃, _, hn₁₂, hn₂₃⟩
        · exact .inr ⟨_, hn₁₂, hstay₂₃⟩
      | some o =>
        obtain ⟨μ₃, _, hn₂₃⟩ := hb₂₃.visible_forward hr₂₃ μ₂ o hlbl
        exact .inl ⟨μ₃, _, hn₁₂, hn₂₃⟩
    · exact .inr ⟨s₂, hstay, hr₂₃⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ o hμ
    obtain ⟨μ₂, hlbl₂, hn₁₂⟩ := hb₁₂.visible_forward hr₁₂ μ o hμ
    obtain ⟨μ₃, hlbl₃, hn₂₃⟩ := hb₂₃.visible_forward hr₂₃ μ₂ o hlbl₂
    exact ⟨μ₃, hlbl₃, _, hn₁₂, hn₂₃⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ hμ
    rcases hb₂₃.silent_backward hr₂₃ μ hμ with ⟨μ₂, hn₂₃⟩ | hstay
    · cases hlbl : L₂.label s₂ μ₂ with
      | none =>
        rcases hb₁₂.silent_backward hr₁₂ μ₂ hlbl with ⟨μ₁, hn₁₂⟩ | hstay₁₂
        · exact .inl ⟨μ₁, _, hn₁₂, hn₂₃⟩
        · exact .inr ⟨_, hstay₁₂, hn₂₃⟩
      | some o =>
        obtain ⟨μ₁, _, hn₁₂⟩ := hb₁₂.visible_backward hr₁₂ μ₂ o hlbl
        exact .inl ⟨μ₁, _, hn₁₂, hn₂₃⟩
    · exact .inr ⟨s₂, hr₁₂, hstay⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ o hμ
    obtain ⟨μ₂, hlbl₂, hn₂₃⟩ := hb₂₃.visible_backward hr₂₃ μ o hμ
    obtain ⟨μ₁, hlbl₁, hn₁₂⟩ := hb₁₂.visible_backward hr₁₂ μ₂ o hlbl₂
    exact ⟨μ₁, hlbl₁, _, hn₁₂, hn₂₃⟩

end WeakBisim

/-! ## Strong bisimulation and the spectrum inclusion

The **strong** bisimulation on the same transition systems matches *every* move
immediately — including silent ones — with no stuttering. It is finer than
`WeakBisim`; the inclusion `StrongBisim.toWeakBisim` records where it sits in the
spectrum. Its transitivity needs no stutter argument at all, so it is trivially
constructive. -/

/--
`IsStrongBisim L₁ L₂ rel` states that `rel` is a **strong** bisimulation:
every move on either side is matched *immediately* by an equally-labeled move on
the other, preserving `rel`. No move — silent or visible — may be stuttered.
-/
structure IsStrongBisim (L₁ L₂ : LTS Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop where
  /-- Every `L₁`-state is related to some `L₂`-state. -/
  total_left : ∀ s₁, ∃ s₂, rel s₁ s₂
  /-- Every `L₂`-state is related to some `L₁`-state. -/
  total_right : ∀ s₂, ∃ s₁, rel s₁ s₂
  /-- Every `L₁`-move is matched immediately by an equally-labeled `L₂`-move. -/
  forward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ μ : L₁.Move s₁,
    ∃ μ₂ : L₂.Move s₂,
      L₂.label s₂ μ₂ = L₁.label s₁ μ ∧ rel (L₁.next s₁ μ) (L₂.next s₂ μ₂)
  /-- Every `L₂`-move is matched immediately by an equally-labeled `L₁`-move. -/
  backward : ∀ {s₁ s₂}, rel s₁ s₂ → ∀ μ : L₂.Move s₂,
    ∃ μ₁ : L₁.Move s₁,
      L₁.label s₁ μ₁ = L₂.label s₂ μ ∧ rel (L₁.next s₁ μ₁) (L₂.next s₂ μ)

/-- `StrongBisim L₁ L₂` holds when some relation is a strong bisimulation between
the two transition systems. -/
def StrongBisim (L₁ L₂ : LTS Obs) : Prop :=
  ∃ rel : L₁.State → L₂.State → Prop, IsStrongBisim L₁ L₂ rel

namespace StrongBisim

/-- Every transition system is strongly bisimilar to itself. -/
protected theorem refl (L : LTS Obs) : StrongBisim L L :=
  ⟨Eq, by
    refine ⟨fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩, ?_, ?_⟩
    · rintro s₁ _ rfl μ; exact ⟨μ, rfl, rfl⟩
    · rintro _ s₂ rfl μ; exact ⟨μ, rfl, rfl⟩⟩

/-- Strong bisimilarity is symmetric. -/
protected theorem symm {L₁ L₂ : LTS Obs}
    (h : StrongBisim L₁ L₂) : StrongBisim L₂ L₁ := by
  obtain ⟨rel, hb⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂,
    { total_left := hb.total_right
      total_right := hb.total_left
      forward := fun hr μ => hb.backward hr μ
      backward := fun hr μ => hb.forward hr μ }⟩

/-- Strong bisimilarity is transitive — no stutter argument, hence constructive. -/
protected theorem trans {L₁ L₂ L₃ : LTS Obs}
    (h₁₂ : StrongBisim L₁ L₂) (h₂₃ : StrongBisim L₂ L₃) : StrongBisim L₁ L₃ := by
  obtain ⟨r₁₂, hb₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃, ?_, ?_, ?_, ?_⟩
  · intro s₁
    obtain ⟨s₂, h₂⟩ := hb₁₂.total_left s₁
    obtain ⟨s₃, h₃⟩ := hb₂₃.total_left s₂
    exact ⟨s₃, s₂, h₂, h₃⟩
  · intro s₃
    obtain ⟨s₂, h₂⟩ := hb₂₃.total_right s₃
    obtain ⟨s₁, h₁⟩ := hb₁₂.total_right s₂
    exact ⟨s₁, s₂, h₁, h₂⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ
    obtain ⟨μ₂, hl₁₂, hn₁₂⟩ := hb₁₂.forward hr₁₂ μ
    obtain ⟨μ₃, hl₂₃, hn₂₃⟩ := hb₂₃.forward hr₂₃ μ₂
    exact ⟨μ₃, hl₂₃.trans hl₁₂, _, hn₁₂, hn₂₃⟩
  · rintro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ μ
    obtain ⟨μ₂, hl₂₃, hn₂₃⟩ := hb₂₃.backward hr₂₃ μ
    obtain ⟨μ₁, hl₁₂, hn₁₂⟩ := hb₁₂.backward hr₁₂ μ₂
    exact ⟨μ₁, hl₁₂.trans hl₂₃, _, hn₁₂, hn₂₃⟩

/-- **Strong bisimilarity refines weak bisimilarity.** Every strong bisimulation
is a weak one: an immediate move-match discharges the weak silent clause via
`.inl` and the weak visible clause with the matched label. This situates
`StrongBisim` above `WeakBisim` in the spectrum. -/
protected theorem toWeakBisim {L₁ L₂ : LTS Obs}
    (h : StrongBisim L₁ L₂) : WeakBisim L₁ L₂ := by
  obtain ⟨rel, hb⟩ := h
  refine ⟨rel, hb.total_left, hb.total_right, ?_, ?_, ?_, ?_⟩
  · intro s₁ s₂ hr μ _
    obtain ⟨μ₂, _, hn⟩ := hb.forward hr μ
    exact .inl ⟨μ₂, hn⟩
  · intro s₁ s₂ hr μ o hμ
    obtain ⟨μ₂, hl, hn⟩ := hb.forward hr μ
    exact ⟨μ₂, hl.trans hμ, hn⟩
  · intro s₁ s₂ hr μ _
    obtain ⟨μ₁, _, hn⟩ := hb.backward hr μ
    exact .inl ⟨μ₁, hn⟩
  · intro s₁ s₂ hr μ o hμ
    obtain ⟨μ₁, hl, hn⟩ := hb.backward hr μ
    exact ⟨μ₁, hl.trans hμ, hn⟩

end StrongBisim

end Control
