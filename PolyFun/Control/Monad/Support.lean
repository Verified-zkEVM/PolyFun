/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra
public import Mathlib.Data.Set.Functor
public import Mathlib.Control.Monad.Writer

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
for them: flattened premises may choose unrelated initial indices on the two sides of a
`bind`. For `StateT` this can let the continuation observe a state the prefix did not
produce; for `ReaderT` it can let the two premises use different environments. Reason about
those per run instead, via
`mem_support_stateT_iff` / `mem_support_readerT_iff`; `PolyFunTest` pins the failure with a
counterexample. Oracle- and state-relative supports belong at the specification layer
(`PolyFun.PFunctor.Free.WP`), which indexes the notion by a per-operation answer assignment.

A second limitation is inherited from `MonadAttach`: obtaining an instance requires
producing `attach`, which for continuation-passing monads is impossible to do
non-trivially. CPS encodings such as `PolyFun.Control.Monad.FreeContT` therefore cannot be
`ExactMonadAttach`, matching core's treatment of `StateCpsT` and `ExceptCpsT`.
-/

@[expose] public section

universe u v w

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
@[simp, grind =]
theorem mem_support [MonadAttach m] {x : m α} {a : α} :
    a ∈ support x ↔ CanReturn x a :=
  Iff.rfl

/-! ### Automation contract

Two normal forms, one per layer, chosen so the two do not fight:

* **Membership normalizes to `CanReturn`.** `mem_support` is `@[simp, grind =]`, so
  `a ∈ support x` becomes the atomic reachability predicate, and the per-monad
  `canReturn_iff` lemmas take it the rest of the way to a concrete equation. Those
  lemmas key on `CanReturn`, not on membership, precisely so that they extend the
  chain rather than race `mem_support` for the same left-hand side.
* **Set-level laws produce `support` terms.** `support_pure`, `support_bind`,
  `support_map` are `@[simp]`, so a structural goal is first decomposed at the set
  level and only then unfolded pointwise.

`grind` tags go on the *directed, single-variable* bridges only: membership
unfoldings and the closed-form supports of `pure`/`none`/`error`. The
characterizations that quantify over the support — `support_eq_empty_iff`,
`support_nonempty_iff`, and the `AllOutputs`/`SomeOutput` iffs — stay `@[simp]`-only.
Those are saturation hazards: `grind` case-splits the iff, Skolemizes the support
quantifier into a fresh witness, and the always-tagged `bind` expansions turn that
witness back into more `support` terms with no finite grounding. A proof that needs
one re-supplies it locally, as `grind [allOutputs_iff_forall_support]`.

### Emptiness and branching

These need no exactness: they are about the shape of the `Set`, not about how the
monad's operations act on it. -/

theorem support_eq_empty_iff [MonadAttach m] {x : m α} :
    support x = ∅ ↔ ∀ a, ¬ CanReturn x a := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact Iff.rfl

theorem support_nonempty_iff [MonadAttach m] {x : m α} :
    (support x).Nonempty ↔ ∃ a, CanReturn x a :=
  Iff.rfl

theorem not_mem_support_iff [MonadAttach m] {x : m α} {a : α} :
    a ∉ support x ↔ ¬ CanReturn x a :=
  Iff.rfl

@[simp]
theorem support_ite [MonadAttach m] (c : Prop) [Decidable c] (x y : m α) :
    support (if c then x else y) = if c then support x else support y := by
  split <;> rfl

@[simp]
theorem support_dite [MonadAttach m] (c : Prop) [Decidable c] (x : c → m α) (y : ¬ c → m α) :
    support (if h : c then x h else y h) = if h : c then support (x h) else support (y h) := by
  split <;> rfl

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

/-! #### The structural laws on `CanReturn`

The same three equations keyed on the reachability predicate rather than on set
membership. `support_pure`/`support_bind`/`support_map` decompose a goal at the set
level; these finish it pointwise, and they are what makes `CanReturn` a usable normal
form rather than a dead end. Core supplies only the elimination halves
(`eq_of_canReturn_pure`, `canReturn_bind_imp'`, `canReturn_map_imp'`); the
introduction halves are exactly `ExactMonadAttach`'s two fields, so the equivalences
need both classes.

Their orientation matches the corresponding `mem_support_*` lemmas, so the two routes
through the simp set — unfold membership first, or rewrite the set first — converge on
the same normal form instead of racing. -/

@[simp, grind =]
theorem canReturn_pure_iff {a b : α} : CanReturn (pure b : m α) a ↔ a = b :=
  ⟨fun h => (LawfulMonadAttach.eq_of_canReturn_pure h).symm,
    fun h => by subst h; exact ExactMonadAttach.canReturn_pure _⟩

@[simp, grind =]
theorem canReturn_bind_iff {x : m α} {f : α → m β} {b : β} :
    CanReturn (x >>= f) b ↔ ∃ a, CanReturn x a ∧ CanReturn (f a) b :=
  ⟨LawfulMonadAttach.canReturn_bind_imp',
    fun ⟨_, ha, hb⟩ => ExactMonadAttach.canReturn_bind ha hb⟩

@[simp, grind =]
theorem canReturn_map_iff {g : α → β} {x : m α} {b : β} :
    CanReturn (g <$> x) b ↔ ∃ a, CanReturn x a ∧ g a = b :=
  ⟨LawfulMonadAttach.canReturn_map_imp',
    fun ⟨a, ha, hab⟩ => hab ▸ by
      rw [← bind_pure_comp]
      exact ExactMonadAttach.canReturn_bind ha (ExactMonadAttach.canReturn_pure _)⟩

theorem mem_support_bind {x : m α} {f : α → m β} {b : β} :
    b ∈ support (x >>= f) ↔ ∃ a ∈ support x, b ∈ support (f a) := by
  simp

@[simp]
theorem support_map (g : α → β) (x : m α) : support (g <$> x) = g '' support x := by
  rw [← bind_pure_comp, support_bind]
  ext b
  simp [eq_comm]

@[simp]
theorem support_seq (f : m (α → β)) (x : m α) :
    support (f <*> x) = ⋃ g ∈ support f, g '' support x := by
  rw [seq_eq_bind_map, support_bind]
  simp only [support_map]


end Laws

/-! ## Always / some / never output judgments -/

/-- Every possible output of `x` satisfies `p` — the "always true" judgment.

Stated over `CanReturn` rather than as a bounded quantifier over `support`, because the
modality does not need to expose a `Set` in its interface. This makes the same shape easy
to index when a flattened set of values is too coarse, as for `StateT`; the indexed
carrier there is still the honest set of value/final-state pairs. The two unindexed
spellings are definitionally interchangeable — `allOutputs_iff_forall_support` and
`allOutputs_iff_forall_canReturn` are both `Iff.rfl` — so nothing downstream has to choose. -/
def AllOutputs [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∀ a, CanReturn x a → p a

/-- Some possible output of `x` satisfies `p`. The angelic half of the pair; see
`AllOutputs` for why it is stated over `CanReturn`. -/
def SomeOutput [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∃ a, CanReturn x a ∧ p a

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

/-- `support` is the *equality instance* of the angelic judgment: a value is a possible
output exactly when "some output equals it" holds.

The two presentations of the layer meet here. `support` is the `Set`-valued carrier and
`AllOutputs`/`SomeOutput` are the demonic and angelic modalities over it; this equation
says nothing is lost by reading the carrier off the modality instead. The modality is the
more flexible presentation: its shape can be indexed when a flattened set of values is
too coarse, as in the `StateT` section below. It is also what the weakest-precondition
bridge consumes: `MonadAttach.toWP` is built from `AllOutputs`, not from `support`. -/
theorem support_eq_setOf_someOutput (x : m α) :
    support x = {a | SomeOutput (· = a) x} :=
  Set.ext fun a => ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨_, hb, hba⟩ => hba ▸ hb⟩

/-- The angelic judgment at an equality predicate is membership in the support. The
pointwise form of `support_eq_setOf_someOutput`. -/
theorem someOutput_eq_iff_mem_support (x : m α) (a : α) :
    SomeOutput (· = a) x ↔ a ∈ support x :=
  ⟨fun ⟨_, hb, hba⟩ => hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

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

/-! #### Negation

Classically, the pair is dual: the demonic judgment is the negation of the angelic one
at the negated predicate, and conversely. Only one direction was available before. -/

theorem not_allOutputs_iff (p : α → Prop) (x : m α) :
    ¬ AllOutputs p x ↔ SomeOutput (fun a => ¬ p a) x := by
  simp only [AllOutputs, SomeOutput, not_forall]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, by simpa using ha⟩, fun ⟨a, ha, hna⟩ => ⟨a, by simp [ha, hna]⟩⟩

theorem not_noOutput_iff (p : α → Prop) (x : m α) :
    ¬ NoOutput p x ↔ SomeOutput p x := by
  rw [NoOutput, not_allOutputs_iff]
  exact ⟨fun h => h.imp fun _ ⟨ha, hp⟩ => ⟨ha, not_not.mp hp⟩,
    fun h => h.imp fun _ ⟨ha, hp⟩ => ⟨ha, not_not.mpr hp⟩⟩

theorem someOutput_iff_not_noOutput (p : α → Prop) (x : m α) :
    SomeOutput p x ↔ ¬ NoOutput p x :=
  (not_noOutput_iff p x).symm

theorem noOutput_iff_allOutputs_not (p : α → Prop) (x : m α) :
    NoOutput p x ↔ AllOutputs (fun a => ¬ p a) x :=
  Iff.rfl

/-! #### Disjunction, conjunction, and monotonicity in the computation

`allOutputs_and` was already available; these complete the square. Note the
directions: the demonic judgment distributes over `∧` and only absorbs `∨`, and the
angelic one is the mirror image. -/

theorem someOutput_or (p q : α → Prop) (x : m α) :
    SomeOutput (fun a => p a ∨ q a) x ↔ SomeOutput p x ∨ SomeOutput q x := by
  constructor
  · rintro ⟨a, ha, hp | hq⟩
    · exact Or.inl ⟨a, ha, hp⟩
    · exact Or.inr ⟨a, ha, hq⟩
  · rintro (⟨a, ha, hp⟩ | ⟨a, ha, hq⟩)
    · exact ⟨a, ha, Or.inl hp⟩
    · exact ⟨a, ha, Or.inr hq⟩

theorem allOutputs_or_of_left {p q : α → Prop} {x : m α} (h : AllOutputs p x) :
    AllOutputs (fun a => p a ∨ q a) x :=
  fun a ha => Or.inl (h a ha)

theorem someOutput_and_left {p q : α → Prop} {x : m α}
    (h : SomeOutput (fun a => p a ∧ q a) x) : SomeOutput p x :=
  h.imp fun _ ⟨ha, hpq⟩ => ⟨ha, hpq.1⟩

/-- Monotonicity in the *computation*, not the predicate: a demonic obligation
transfers to anything with a smaller support. `allOutputs_mono` varies only the
predicate. -/
theorem allOutputs_of_support_subset {p : α → Prop} {x y : m α}
    (hsub : support x ⊆ support y) (h : AllOutputs p y) : AllOutputs p x :=
  fun a ha => h a (hsub ha)

theorem someOutput_of_support_subset {p : α → Prop} {x y : m α}
    (hsub : support x ⊆ support y) (h : SomeOutput p x) : SomeOutput p y :=
  h.imp fun _ ⟨ha, hp⟩ => ⟨hsub ha, hp⟩

@[simp]
theorem allOutputs_true (x : m α) : AllOutputs (fun _ => True) x :=
  fun _ _ => trivial

@[simp]
theorem someOutput_false_iff (x : m α) : SomeOutput (fun _ => False) x ↔ False := by
  simp [SomeOutput]

theorem allOutputs_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) (x : m α) :
    AllOutputs p x ↔ AllOutputs q x :=
  ⟨allOutputs_mono fun a => (h a).mp, allOutputs_mono fun a => (h a).mpr⟩

theorem someOutput_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) (x : m α) :
    SomeOutput p x ↔ SomeOutput q x :=
  ⟨someOutput_mono fun a => (h a).mp, someOutput_mono fun a => (h a).mpr⟩

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

section Angelic

attribute [local instance] mAlgOrderedPropAngelic

/-- Support-based characterization of the angelic `Prop`-valued weakest precondition —
the mirror of `wp_iff_forall_support`. -/
theorem wp_angelic_iff_exists_support (x : m α) (post : α → Prop) :
    MAlgOrdered.wp (l := Prop) x post ↔ ∃ a ∈ support x, post a := by
  change SomeOutput id (x >>= fun a => pure (post a)) ↔ _
  rw [someOutput_bind]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, (someOutput_pure id (post a)).mp h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, (someOutput_pure id (post a)).mpr h⟩⟩

/-- The angelic `Prop`-valued weakest precondition is the "sometimes" judgment. -/
theorem wp_angelic_iff_someOutput (x : m α) (post : α → Prop) :
    MAlgOrdered.wp (l := Prop) x post ↔ SomeOutput post x :=
  wp_angelic_iff_exists_support x post

/-- The trivial-precondition angelic triple is exactly the "sometimes" judgment — the
mirror of `triple_top_iff_allOutputs`. -/
theorem triple_top_iff_someOutput (x : m α) (post : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x post ↔ SomeOutput post x := by
  rw [MAlgOrdered.Triple, top_le_iff, ← wp_angelic_iff_someOutput x post]
  exact ⟨fun h => h ▸ trivial, fun h => eq_true h⟩

/-- Against a negated postcondition the angelic triple says that the demonic guarantee
does not hold. -/
theorem triple_top_not_iff_not_allOutputs (x : m α) (post : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x (fun a => ¬ post a) ↔ ¬ AllOutputs post x := by
  rw [triple_top_iff_someOutput, ← not_allOutputs_iff]

end Angelic

end PropAlgebra

end MonadAttach
