/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra
public import Mathlib.Data.Set.Functor

/-!
# Exact Monadic Support

Lean core's `MonadAttach` already provides the notion this layer needs: a predicate
`MonadAttach.CanReturn x a`, meaning `a` is a possible return value of `x`, together with
`attach`, which decorates a computation's results with proofs of that predicate.
`LawfulMonadAttach` further pins `CanReturn` down as *the* strongest postcondition. This
file adds the missing half and the `Set`-valued view:

* `ExactMonadAttach` — the *introduction* rules for `CanReturn`. Core proves only
  elimination rules (`canReturn_bind_imp'`, `eq_of_canReturn_pure`, `canReturn_map_imp'`),
  which bound the support from above. Those alone do not pin it down: the monad
  `fun _ => PUnit` with `CanReturn := fun _ _ => False` satisfies `LawfulMonadAttach`
  vacuously, since every core law is an implication *out of* `CanReturn`. Assuming the two
  introduction rules turns each of core's implications into an equivalence, which is what
  support reasoning actually rewrites with.
* `MonadAttach.support x : Set α` — the `Set`-valued view of `CanReturn`, definitionally
  the predicate itself, so `a ∈ support x ↔ CanReturn x a` is `Iff.rfl`.
* The qualitative judgments `AllOutputs` ("always"), `SomeOutput`, and `NoOutput`
  ("never"), with scoped notation `x ⊨ₐ p`, `x ⊨ₛ p`, and `x ⊭ p`.

`ExactMonadAttach` extends `LawfulMonadAttach` rather than the weak class: that excludes
`MonadAttach.trivial` (`CanReturn := fun _ _ => True`, i.e. `support = univ`), while the
introduction rules exclude the empty model. Between them the support is exact.

`AllOutputs` induces the demonic `Prop`-carrier ordered monad algebra `MAlgOrdered m Prop`,
identifying "always" with the trivial-precondition Hoare triple
(`triple_top_iff_allOutputs`); `SomeOutput` gives the angelic companion. Both
algebras are named definitions rather than global instances: transformer
algebras such as `MAlgOrdered.instOptionT` give failures a different meaning,
so a generic global support instance would be incoherent with them.

## Scope

Support is a *value*-level notion here. Core states the limitation directly: `CanReturn`
"neither depends on the prior internal state of the monad, nor does it contain information
about how the state of the monad changes". Concretely, `StateT σ m` and `ReaderT ρ m` do
have `MonadAttach` instances — quantifying existentially over the initial state — and those
supports are canonical, so the elimination theory applies. But `ExactMonadAttach` is *false*
for them: possible outputs do not compose along `bind` when the continuation may observe a
state the prefix did not produce. Reason about those per run instead, via
`mem_support_stateT_iff` / `mem_support_readerT_iff`; `PolyFunTest` pins the failure with a
counterexample. Oracle- and state-relative supports belong at the specification layer
(`PolyFun.PFunctor.Free.WP`), which indexes the notion by a per-operation answer assignment.

A second limitation is inherited from `MonadAttach`: obtaining an instance requires
producing `attach`, which for continuation-passing monads is impossible to do
non-trivially. CPS encodings such as `PolyFun.Control.Monad.FreeContT` therefore cannot be
`ExactMonadAttach`, matching core's treatment of `StateCpsT` and `ExceptCpsT`.
-/

@[expose] public section

universe u v

/-- A monad whose `MonadAttach.CanReturn` predicate is *exact*: besides being the strongest
postcondition (`LawfulMonadAttach`), it is closed under the monad's introduction rules, so
the possible outputs of `pure` and `bind` are exactly what one expects.

Core assumes only the elimination direction of each law, which leaves `CanReturn` free to be
uniformly `False`. These two fields rule that out; together with the `LawfulMonadAttach`
parent — which rules out the uniformly-`True` model — they determine the support exactly. -/
class ExactMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m]
    extends LawfulMonadAttach m where
  /-- A pure computation can return its own value. -/
  canReturn_pure {α : Type u} (a : α) : MonadAttach.CanReturn (pure a : m α) a
  /-- Possible outputs compose along `bind`. -/
  canReturn_bind {α β : Type u} {x : m α} {f : α → m β} {a : α} {b : β} :
    MonadAttach.CanReturn x a → MonadAttach.CanReturn (f a) b →
      MonadAttach.CanReturn (x >>= f) b

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u}

/-- The set of possible outputs of a monadic computation: the `Set`-valued view of
`CanReturn`. Available for any `MonadAttach`; the structural equations are gated behind
`ExactMonadAttach`. -/
def support [MonadAttach m] (x : m α) : Set α :=
  {a | CanReturn x a}

/-- Membership in `support` is `CanReturn`, definitionally.

Stated as a simp lemma because `Set.ofPred` and `Set.Mem` are `implicit_reducible`: `rfl`
and `exact` see through them, but `simp`'s reducible-transparency discharge does not. -/
@[simp]
theorem mem_support [MonadAttach m] {x : m α} {a : α} :
    a ∈ support x ↔ CanReturn x a :=
  Iff.rfl

section Laws

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

@[simp]
theorem support_pure (b : α) : support (pure b : m α) = {b} := by
  ext c
  refine ⟨fun h => (LawfulMonadAttach.eq_of_canReturn_pure h).symm, fun h => ?_⟩
  rw [Set.mem_singleton_iff] at h
  subst h
  exact ExactMonadAttach.canReturn_pure c

@[simp]
theorem support_bind (x : m α) (f : α → m β) :
    support (x >>= f) = ⋃ a ∈ support x, support (f a) := by
  ext b
  simp only [Set.mem_iUnion]
  refine ⟨fun h => ?_, fun ⟨a, ha, hb⟩ => ExactMonadAttach.canReturn_bind ha hb⟩
  obtain ⟨a, ha, hb⟩ := LawfulMonadAttach.canReturn_bind_imp' h
  exact ⟨a, ha, hb⟩

theorem mem_support_pure {a b : α} : a ∈ support (pure b : m α) ↔ a = b := by
  simp

theorem mem_support_bind {x : m α} {f : α → m β} {b : β} :
    b ∈ support (x >>= f) ↔ ∃ a ∈ support x, b ∈ support (f a) := by
  simp

@[simp]
theorem support_map (g : α → β) (x : m α) : support (g <$> x) = g '' support x := by
  rw [← bind_pure_comp, support_bind]
  ext b
  simp [eq_comm]

end Laws

/-! ## Always / some / never output judgments -/

/-- Every possible output of `x` satisfies `p` — the "always true" judgment.
Definitionally the bounded quantifier `∀ a ∈ support x, p a`. -/
def AllOutputs [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∀ a ∈ support x, p a

/-- Some possible output of `x` satisfies `p`.
Definitionally the bounded quantifier `∃ a ∈ support x, p a`. -/
def SomeOutput [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∃ a ∈ support x, p a

/-- No possible output of `x` satisfies `p` — the "never true" judgment. -/
def NoOutput [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  AllOutputs (fun a => ¬ p a) x

@[inherit_doc AllOutputs]
scoped notation:50 x:51 " ⊨ₐ " p:51 => MonadAttach.AllOutputs p x

@[inherit_doc SomeOutput]
scoped notation:50 x:51 " ⊨ₛ " p:51 => MonadAttach.SomeOutput p x

@[inherit_doc NoOutput]
scoped notation:50 x:51 " ⊭ " p:51 => MonadAttach.NoOutput p x

section Judgments

variable [MonadAttach m]

theorem allOutputs_iff_forall_support (p : α → Prop) (x : m α) :
    AllOutputs p x ↔ ∀ a ∈ support x, p a :=
  Iff.rfl

theorem someOutput_iff_exists_support (p : α → Prop) (x : m α) :
    SomeOutput p x ↔ ∃ a ∈ support x, p a :=
  Iff.rfl

theorem noOutput_iff_forall_support (p : α → Prop) (x : m α) :
    NoOutput p x ↔ ∀ a ∈ support x, ¬ p a :=
  Iff.rfl

theorem allOutputs_iff_forall_canReturn (p : α → Prop) (x : m α) :
    AllOutputs p x ↔ ∀ a, CanReturn x a → p a :=
  Iff.rfl

theorem not_someOutput_iff_noOutput (p : α → Prop) (x : m α) :
    ¬ SomeOutput p x ↔ NoOutput p x := by
  simp [SomeOutput, NoOutput, AllOutputs]

theorem allOutputs_and (p q : α → Prop) (x : m α) :
    AllOutputs (fun a => p a ∧ q a) x ↔ AllOutputs p x ∧ AllOutputs q x :=
  ⟨fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩,
    fun ⟨hp, hq⟩ a ha => ⟨hp a ha, hq a ha⟩⟩

theorem allOutputs_mono {p q : α → Prop} (h : ∀ a, p a → q a) {x : m α}
    (hx : AllOutputs p x) : AllOutputs q x :=
  fun a ha => h a (hx a ha)

theorem someOutput_mono {p q : α → Prop} (h : ∀ a, p a → q a) {x : m α}
    (hx : SomeOutput p x) : SomeOutput q x :=
  hx.imp fun a ⟨ha, hpa⟩ => ⟨ha, h a hpa⟩

theorem noOutput_mono {p q : α → Prop} (h : ∀ a, q a → p a) {x : m α}
    (hx : NoOutput p x) : NoOutput q x :=
  fun a ha hqa => hx a ha (h a hqa)

end Judgments

section JudgmentLaws

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

@[simp]
theorem allOutputs_pure (p : α → Prop) (a : α) :
    AllOutputs p (pure a : m α) ↔ p a := by
  simp [AllOutputs]

@[simp]
theorem allOutputs_bind (p : β → Prop) (x : m α) (f : α → m β) :
    AllOutputs p (x >>= f) ↔ ∀ a ∈ support x, AllOutputs p (f a) := by
  constructor
  · intro h a ha b hb
    exact h b (mem_support_bind.mpr ⟨a, ha, hb⟩)
  · intro h b hb
    obtain ⟨a, ha, hb⟩ := mem_support_bind.mp hb
    exact h a ha b hb

@[simp]
theorem someOutput_pure (p : α → Prop) (a : α) :
    SomeOutput p (pure a : m α) ↔ p a := by
  simp [SomeOutput]

@[simp]
theorem someOutput_bind (p : β → Prop) (x : m α) (f : α → m β) :
    SomeOutput p (x >>= f) ↔ ∃ a ∈ support x, SomeOutput p (f a) := by
  constructor
  · rintro ⟨b, hb, hp⟩
    obtain ⟨a, ha, hb⟩ := mem_support_bind.mp hb
    exact ⟨a, ha, b, hb, hp⟩
  · rintro ⟨a, ha, b, hb, hp⟩
    exact ⟨b, mem_support_bind.mpr ⟨a, ha, hb⟩, hp⟩

@[simp]
theorem noOutput_pure (p : α → Prop) (a : α) :
    NoOutput p (pure a : m α) ↔ ¬ p a := by
  simp [NoOutput]

@[simp]
theorem noOutput_bind (p : β → Prop) (x : m α) (f : α → m β) :
    NoOutput p (x >>= f) ↔ ∀ a ∈ support x, NoOutput p (f a) := by
  simp [NoOutput]

end JudgmentLaws

/-! ## Induced ordered monad algebras on `Prop`

`AllOutputs` is the demonic `Prop`-carrier ordered monad algebra: its induced
`MAlgOrdered.wp` is the support-based weakest precondition, and the trivial-precondition
triple is exactly the "always" judgment. The angelic companion built from `SomeOutput` is
provided as a plain definition rather than an instance, since the two share an instance
head. -/

section PropAlgebra

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
variable {α : Type}

/-- The demonic `Prop`-carrier ordered monad algebra of a monad with exact support:
`μ` asserts that every possible output is a true proposition. This is deliberately
not a global instance: for example, the existing `OptionT` algebra interprets
`none` as `⊥`, whereas exact-support partial correctness interprets its empty
support vacuously. Install this definition locally when support semantics is
intended. -/
@[instance_reducible]
def mAlgOrderedPropDemonic : MAlgOrdered m Prop where
  μ x := AllOutputs id x
  μ_pure x := propext (allOutputs_pure id x)
  μ_bind_mono f g hfg x := by
    simp only [allOutputs_bind]
    exact fun h a ha => hfg a (h a ha)

attribute [local instance] mAlgOrderedPropDemonic

/-- Support-based characterization of the demonic `Prop`-valued weakest precondition. -/
theorem wp_iff_forall_support (x : m α) (post : α → Prop) :
    MAlgOrdered.wp (l := Prop) x post ↔ ∀ a ∈ support x, post a := by
  change AllOutputs id (x >>= fun a => pure (post a)) ↔ _
  rw [allOutputs_bind]
  exact ⟨fun h a ha => (allOutputs_pure id (post a)).mp (h a ha),
    fun h a ha => (allOutputs_pure id (post a)).mpr (h a ha)⟩

/-- The demonic `Prop`-valued weakest precondition is the "always" judgment. -/
theorem wp_iff_allOutputs (x : m α) (post : α → Prop) :
    MAlgOrdered.wp (l := Prop) x post ↔ AllOutputs post x :=
  wp_iff_forall_support x post

/-- The trivial-precondition `Prop`-valued triple is exactly the "always" judgment:
`⊤`-precondition triples assert that every possible output satisfies `post`. -/
theorem triple_top_iff_allOutputs (x : m α) (post : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x post ↔ AllOutputs post x := by
  rw [MAlgOrdered.Triple, top_le_iff, ← wp_iff_allOutputs x post]
  exact ⟨fun h => h ▸ trivial, fun h => eq_true h⟩

/-- The trivial-precondition `Prop`-valued triple against a negated postcondition is
exactly the "never" judgment. -/
theorem triple_top_not_iff_noOutput (x : m α) (post : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x (fun a => ¬ post a) ↔ NoOutput post x :=
  triple_top_iff_allOutputs x fun a => ¬ post a

/-- The angelic `Prop`-carrier ordered monad algebra: `μ` asserts that some possible output
is a true proposition. Not an instance — it shares an instance head with the demonic
`mAlgOrderedPropDemonic`. -/
@[instance_reducible]
def mAlgOrderedPropAngelic : MAlgOrdered m Prop where
  μ x := SomeOutput id x
  μ_pure x := propext (someOutput_pure id x)
  μ_bind_mono f g hfg x := by
    simp only [someOutput_bind]
    exact fun ⟨a, ha, h⟩ => ⟨a, ha, hfg a h⟩

end PropAlgebra

/-! ## Recovering the `MonadLiftT` presentation

Downstream libraries that phrase support as a monad lift into the powerset monad can
register these; they are deliberately not instances, so that support reasoning does not
perturb monad-lift instance search. -/

/-- The support map as a monad lift into `SetM`. Not an instance. -/
@[instance_reducible]
def toMonadLiftT (m : Type u → Type v) [MonadAttach m] :
    MonadLiftT m SetM where
  monadLift x := (support x : SetM _)

/-- The support lift is lawful. Not an instance. -/
theorem toLawfulMonadLiftT (m : Type u → Type v) [Monad m] [LawfulMonad m] [MonadAttach m]
    [ExactMonadAttach m] :
    letI := toMonadLiftT m
    LawfulMonadLiftT m SetM :=
  letI := toMonadLiftT m
  { monadLift_pure := fun a => support_pure a
    monadLift_bind := fun x f => support_bind x f }

/-! ## Base instances

Core supplies `MonadAttach` and `LawfulMonadAttach` for `Id`, `Option`, `OptionT`,
`ExceptT`, `StateT`, and `ReaderT`; only the exactness fields are needed here. `Except` and
`SetM` have no core instance and are supplied below. -/

section Instances

/-- Core provides no `MonadAttach (Except ε)`, only the transformer version; this mirrors
core's `Option` instance. -/
instance instMonadAttachExcept {ε : Type u} : MonadAttach (Except ε) where
  CanReturn x a := x = Except.ok a
  attach
    | .ok a => .ok ⟨a, rfl⟩
    | .error e => .error e

instance instLawfulMonadAttachExcept {ε : Type u} : LawfulMonadAttach (Except ε) where
  map_attach {_ x} := by cases x <;> rfl
  canReturn_map_imp {_ _ x _} h := by
    cases x with
    | error e => cases h
    | ok z => cases h; exact z.2

/-- Core's `MonadAttach (ExceptT ε m)` is stated at `max`-joined universes, which blocks
synthesis in a universe-polymorphic context; this alias instantiates it at a single
universe. Delete once the upstream declaration is repaired. -/
instance instMonadAttachExceptT {ε : Type u} {m : Type u → Type v} [Monad m]
    [MonadAttach m] : MonadAttach (ExceptT ε m) :=
  instMonadAttachExceptTOfMonad.{u, u, v}

/-- The powerset monad is its own support. -/
instance instMonadAttachSetM : MonadAttach SetM where
  CanReturn s a := a ∈ SetM.run s
  attach _ := (Set.univ : Set _)

instance instLawfulMonadAttachSetM : LawfulMonadAttach SetM where
  map_attach {_ x} := by
    change Subtype.val '' (Set.univ : Set {a // a ∈ SetM.run x}) = x
    ext a
    simp [SetM.run]
  canReturn_map_imp {_ _ _ _} h := by
    obtain ⟨z, -, hz⟩ := h
    exact hz ▸ z.2

instance instExactMonadAttachId : ExactMonadAttach Id where
  canReturn_pure _ := rfl
  canReturn_bind h h' := by
    simp only [CanReturn, Id.run] at *
    subst h
    exact h'

instance instExactMonadAttachOption : ExactMonadAttach Option where
  canReturn_pure _ := rfl
  canReturn_bind {_ _ _ _ _ _} h h' := by
    simp only [CanReturn] at *
    subst h
    simpa using h'

instance instExactMonadAttachExcept {ε : Type u} : ExactMonadAttach (Except ε) where
  canReturn_pure _ := rfl
  canReturn_bind ha hb := by cases ha; exact hb

instance instExactMonadAttachSetM : ExactMonadAttach SetM where
  canReturn_pure _ := rfl
  canReturn_bind {_ _ _ _ a _} ha hb := Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hb⟩⟩

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

instance instExactMonadAttachOptionT : ExactMonadAttach (OptionT m) where
  canReturn_pure {α} a := by
    change CanReturn ((pure a : OptionT m α)).run (some a)
    rw [OptionT.run_pure]
    exact ExactMonadAttach.canReturn_pure _
  canReturn_bind {α β x f a b} h h' := by
    change CanReturn ((x >>= f : OptionT m β)).run (some b)
    have hrun : ((x >>= f : OptionT m β)).run = x.run >>= fun o =>
        match o with
        | some c => (f c).run
        | none => pure none := rfl
    rw [hrun]
    exact ExactMonadAttach.canReturn_bind (a := some a) h h'

instance instExactMonadAttachExceptT {ε : Type u} : ExactMonadAttach (ExceptT ε m) where
  canReturn_pure {α} a := by
    change CanReturn ((pure a : ExceptT ε m α)).run (Except.ok a)
    rw [ExceptT.run_pure]
    exact ExactMonadAttach.canReturn_pure _
  canReturn_bind {α β x f a b} h h' := by
    change CanReturn ((x >>= f : ExceptT ε m β)).run (Except.ok b)
    have hrun : ((x >>= f : ExceptT ε m β)).run = x.run >>= fun e =>
        match e with
        | Except.ok c => (f c).run
        | Except.error e => pure (Except.error e) := rfl
    rw [hrun]
    exact ExactMonadAttach.canReturn_bind (a := Except.ok a) h h'

/-! ### Stateful monads

`StateT` and `ReaderT` do have core `MonadAttach` instances, existentially quantified over
the initial state or environment, and those supports are canonical. They are *not*
`ExactMonadAttach`: possible outputs do not compose along `bind`, because the continuation
may observe a state the prefix never produced. Reason per run instead. -/

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

end Instances

end MonadAttach
