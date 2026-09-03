/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support.Instances

/-!
# Exact Support: Indexed Support of Stateful Monads

`StateT` and `ReaderT` carry core's canonical support, existentially quantified over the initial
state or environment, and are deliberately not `ExactMonadAttach`: possible outputs do not
compose along `bind` when the flattened premises choose unrelated initial indices. This file
reasons per run instead: `StateT.supportFrom s x` and `ReaderT.supportAt r x`, their exact
`pure` / `bind` / `map` laws, and the indexed judgments `⊨ₐ[s]` / `⊨ₛ[s]` / `⊭[s]` with their
bridges to the flattened judgments.
-/

@[expose] public section

universe u v w

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u}

section Indexed

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-! ### Stateful monads

`StateT` and `ReaderT` do have core `MonadAttach` instances, existentially quantified over
the initial state or environment, and those supports are canonical. They are *not*
`ExactMonadAttach`: possible outputs do not compose along `bind`, because its flattened
premises may be witnessed at different initial indices. Reason per run instead. -/

omit [LawfulMonad m] [ExactMonadAttach m] in
theorem mem_support_stateT_iff {σ : Type u} {x : StateT σ m α} {a : α} :
    a ∈ support x ↔ ∃ s s', (a, s') ∈ support (x.run s) :=
  Iff.rfl

omit [LawfulMonad m] [ExactMonadAttach m] in
theorem mem_support_readerT_iff {ρ : Type u} {x : ReaderT ρ m α} {a : α} :
    a ∈ support x ↔ ∃ r, a ∈ support (x.run r) :=
  Iff.rfl

omit [LawfulMonad m] [ExactMonadAttach m] in
theorem mem_support_of_run_stateT {σ : Type u} {x : StateT σ m α} {a : α} {s s' : σ}
    (h : (a, s') ∈ support (x.run s)) : a ∈ support x :=
  ⟨s, s', h⟩

omit [LawfulMonad m] [ExactMonadAttach m] in
theorem mem_support_of_run_readerT {ρ : Type u} {x : ReaderT ρ m α} {a : α} {r : ρ}
    (h : a ∈ support (x.run r)) : a ∈ support x :=
  ⟨r, h⟩

/-! #### Indexed support

The flattened support above is canonical but coarse: it quantifies the initial state
existentially, and independently on each side of a `bind`, which is exactly why
`ExactMonadAttach` fails. Indexing repairs that. `supportFrom s x` is the set of
result/final-state pairs reachable *from `s`*, and its bind law is exact — the
continuation is only ever run from states the prefix actually produced — needing no
exactness on the transformer, because nothing is flattened away.

This is the same move the probabilistic semantics makes for the same transformer:
state-indexed computations denote a `Kernel σ (α × σ)` rather than a measure, because
there is no canonical initial state to integrate over. Kernels are to measures as
indexed support is to support. -/

/-- The result/final-state pairs reachable by running `x` from the initial state `s`. -/
def StateT.supportFrom {σ : Type u} (s : σ) (x : StateT σ m α) : Set (α × σ) :=
  support (x.run s)

/-- The outputs reachable by running `x` in the environment `r`. -/
def ReaderT.supportAt {ρ : Type u} (r : ρ) (x : ReaderT ρ m α) : Set α :=
  support (x.run r)

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
theorem StateT.mem_supportFrom_iff {σ : Type u} {s : σ} {x : StateT σ m α} {p : α × σ} :
    p ∈ StateT.supportFrom s x ↔ p ∈ support (x.run s) :=
  Iff.rfl

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
theorem ReaderT.mem_supportAt_iff {ρ : Type u} {r : ρ} {x : ReaderT ρ m α} {a : α} :
    a ∈ ReaderT.supportAt r x ↔ a ∈ support (x.run r) :=
  Iff.rfl

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- The flattened support is the union of the indexed ones. Recovers
`mem_support_stateT_iff` and pins that indexing loses nothing. -/
theorem StateT.mem_support_iff_exists_supportFrom {σ : Type u} {x : StateT σ m α} {a : α} :
    a ∈ support x ↔ ∃ s s', (a, s') ∈ StateT.supportFrom s x :=
  Iff.rfl

omit [LawfulMonad m] [ExactMonadAttach m] in
theorem ReaderT.mem_support_iff_exists_supportAt {ρ : Type u} {x : ReaderT ρ m α} {a : α} :
    a ∈ support x ↔ ∃ r, a ∈ ReaderT.supportAt r x :=
  Iff.rfl

@[simp, grind =]
theorem StateT.supportFrom_pure {σ : Type u} (s : σ) (a : α) :
    StateT.supportFrom s (pure a : StateT σ m α) = {(a, s)} := by
  rw [StateT.supportFrom, StateT.run_pure, support_pure]

@[simp, grind =]
theorem ReaderT.supportAt_pure {ρ : Type u} (r : ρ) (a : α) :
    ReaderT.supportAt r (pure a : ReaderT ρ m α) = {a} := by
  rw [ReaderT.supportAt, ReaderT.run_pure, support_pure]

/-- **The exact bind law.** Unlike the flattened `support`, this composes: the
continuation is run only from states the prefix actually produces, so no witness is
chosen independently on the two sides. Needs only `[ExactMonadAttach m]` on the base
monad — `StateT σ m` itself is deliberately not `ExactMonadAttach`, and does not need
to be. -/
@[simp]
theorem StateT.supportFrom_bind {σ : Type u} (s : σ) (x : StateT σ m α)
    (f : α → StateT σ m β) :
    StateT.supportFrom s (x >>= f)
      = ⋃ p ∈ StateT.supportFrom s x, StateT.supportFrom p.2 (f p.1) := by
  rw [StateT.supportFrom, StateT.run_bind, support_bind]
  rfl

/-- The environment version, where the same `r` is threaded to both sides. -/
@[simp]
theorem ReaderT.supportAt_bind {ρ : Type u} (r : ρ) (x : ReaderT ρ m α)
    (f : α → ReaderT ρ m β) :
    ReaderT.supportAt r (x >>= f)
      = ⋃ a ∈ ReaderT.supportAt r x, ReaderT.supportAt r (f a) := by
  rw [ReaderT.supportAt, ReaderT.run_bind, support_bind]
  rfl

@[simp]
theorem StateT.supportFrom_map {σ : Type u} (s : σ) (g : α → β) (x : StateT σ m α) :
    StateT.supportFrom s (g <$> x)
      = (fun p => (g p.1, p.2)) '' StateT.supportFrom s x := by
  rw [StateT.supportFrom, StateT.run_map, support_map]
  rfl

@[simp]
theorem ReaderT.supportAt_map {ρ : Type u} (r : ρ) (g : α → β) (x : ReaderT ρ m α) :
    ReaderT.supportAt r (g <$> x) = g '' ReaderT.supportAt r x := by
  rw [ReaderT.supportAt, ReaderT.run_map, support_map]
  rfl

/-! #### Indexed judgments

The modal pair, indexed. These are the primary indexed notions and `supportFrom` is
their equality instance, exactly as `support` is `SomeOutput`'s in the unindexed case
(`support_eq_setOf_someOutput`). The state-indexed predicate ranges over the *pair*: a
`StateT` computation's outcome is a value together with a final state, and forgetting
the state is what makes the flattened judgments fail to compose. -/

/-- Every outcome reachable from `s` satisfies `p`. -/
def StateT.AllOutputsFrom {σ : Type u} (s : σ) (p : α → σ → Prop) (x : StateT σ m α) : Prop :=
  ∀ q ∈ StateT.supportFrom s x, p q.1 q.2

/-- Some outcome reachable from `s` satisfies `p`. -/
def StateT.SomeOutputFrom {σ : Type u} (s : σ) (p : α → σ → Prop) (x : StateT σ m α) : Prop :=
  ∃ q ∈ StateT.supportFrom s x, p q.1 q.2

/-- No outcome reachable from `s` satisfies `p`. -/
def StateT.NoOutputFrom {σ : Type u} (s : σ) (p : α → σ → Prop) (x : StateT σ m α) : Prop :=
  StateT.AllOutputsFrom s (fun a s' => ¬ p a s') x

@[inherit_doc StateT.AllOutputsFrom]
scoped notation:50 x:51 " ⊨ₐ[" s "] " p:51 => MonadAttach.StateT.AllOutputsFrom s p x

@[inherit_doc StateT.SomeOutputFrom]
scoped notation:50 x:51 " ⊨ₛ[" s "] " p:51 => MonadAttach.StateT.SomeOutputFrom s p x

@[inherit_doc StateT.NoOutputFrom]
scoped notation:50 x:51 " ⊭[" s "] " p:51 => MonadAttach.StateT.NoOutputFrom s p x

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
/-- `supportFrom` is the equality instance of the indexed angelic judgment — the indexed
counterpart of `support_eq_setOf_someOutput`. -/
theorem StateT.supportFrom_eq_setOf_someOutputFrom {σ : Type u} (s : σ) (x : StateT σ m α) :
    StateT.supportFrom s x = {q | StateT.SomeOutputFrom s (fun a s' => (a, s') = q) x} :=
  Set.ext fun q => ⟨fun hq => ⟨q, hq, rfl⟩, fun ⟨_, hb, hbq⟩ => hbq ▸ hb⟩

@[simp]
theorem StateT.allOutputsFrom_pure {σ : Type u} (s : σ) (p : α → σ → Prop) (a : α) :
    StateT.AllOutputsFrom s p (pure a : StateT σ m α) ↔ p a s := by
  simp [StateT.AllOutputsFrom]

@[simp]
theorem StateT.someOutputFrom_pure {σ : Type u} (s : σ) (p : α → σ → Prop) (a : α) :
    StateT.SomeOutputFrom s p (pure a : StateT σ m α) ↔ p a s := by
  simp [StateT.SomeOutputFrom]

/-- The indexed demonic bind rule. This is the judgment-level form of
`StateT.supportFrom_bind`, and like it needs no exactness on the transformer. -/
@[simp]
theorem StateT.allOutputsFrom_bind {σ : Type u} (s : σ) (p : β → σ → Prop)
    (x : StateT σ m α) (f : α → StateT σ m β) :
    StateT.AllOutputsFrom s p (x >>= f)
      ↔ ∀ q ∈ StateT.supportFrom s x, StateT.AllOutputsFrom q.2 p (f q.1) := by
  constructor
  · intro h q hq a ha
    exact h a (by rw [StateT.supportFrom_bind]; exact Set.mem_biUnion hq ha)
  · intro h a ha
    rw [StateT.supportFrom_bind] at ha
    obtain ⟨q, hq, ha'⟩ := Set.mem_iUnion₂.mp ha
    exact h q hq a ha'

/-- The indexed angelic bind rule. -/
@[simp]
theorem StateT.someOutputFrom_bind {σ : Type u} (s : σ) (p : β → σ → Prop)
    (x : StateT σ m α) (f : α → StateT σ m β) :
    StateT.SomeOutputFrom s p (x >>= f)
      ↔ ∃ q ∈ StateT.supportFrom s x, StateT.SomeOutputFrom q.2 p (f q.1) := by
  simp only [StateT.SomeOutputFrom, StateT.supportFrom_bind, Set.mem_iUnion, exists_prop]
  tauto

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
theorem StateT.not_someOutputFrom_iff_noOutputFrom {σ : Type u} (s : σ) (p : α → σ → Prop)
    (x : StateT σ m α) :
    ¬ StateT.SomeOutputFrom s p x ↔ StateT.NoOutputFrom s p x := by
  simp [StateT.SomeOutputFrom, StateT.NoOutputFrom, StateT.AllOutputsFrom]

omit [Monad m] [LawfulMonad m] [ExactMonadAttach m] in
theorem StateT.allOutputsFrom_mono {σ : Type u} {s : σ} {p q : α → σ → Prop}
    (h : ∀ a s', p a s' → q a s') {x : StateT σ m α}
    (hx : StateT.AllOutputsFrom s p x) : StateT.AllOutputsFrom s q x :=
  fun r hr => h r.1 r.2 (hx r hr)

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- Indexed demonic implies flattened demonic: if a value-only `p` holds of every outcome
from every initial state, it holds of every possible output. -/
theorem StateT.allOutputs_of_allOutputsFrom {σ : Type u} {p : α → Prop} {x : StateT σ m α}
    (h : ∀ s, StateT.AllOutputsFrom s (fun a _ => p a) x) : AllOutputs p x :=
  fun _ ⟨s, s', hs⟩ => h s (_, s') hs

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- A flattened value-only guarantee holds at every initial state. Flattening loses the
ability to mention the final state, but it loses nothing for postconditions on values
alone. -/
theorem StateT.allOutputsFrom_of_allOutputs {σ : Type u} {p : α → Prop} {x : StateT σ m α}
    (h : AllOutputs p x) (s : σ) : StateT.AllOutputsFrom s (fun a _ => p a) x :=
  fun q hq => h q.1 ⟨s, q.2, hq⟩

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- For value-only postconditions, flattened demonic support is exactly the universal
closure of the indexed judgment. -/
theorem StateT.allOutputs_iff_forall_allOutputsFrom {σ : Type u} {p : α → Prop}
    {x : StateT σ m α} :
    AllOutputs p x ↔ ∀ s, StateT.AllOutputsFrom s (fun a _ => p a) x :=
  ⟨fun h s => StateT.allOutputsFrom_of_allOutputs h s, StateT.allOutputs_of_allOutputsFrom⟩

end Indexed

end MonadAttach
