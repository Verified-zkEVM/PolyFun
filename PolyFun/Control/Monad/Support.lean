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
modality does not need a `Set`: it is `Prop`-valued and survives settings where the set
of outputs is the wrong object, which is what happens for `StateT`. The two spellings
are definitionally interchangeable — `allOutputs_iff_forall_support` and
`allOutputs_iff_forall_canReturn` are both `Iff.rfl` — so nothing downstream has to
choose. -/
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
more general of the two — it is `Prop`-valued and so survives settings where a `Set` of
outputs is the wrong object, which is exactly what happens for `StateT` (see
`mem_support_stateT_iff` and the indexed section). It is also what the weakest-precondition
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

The pair is dual: the demonic judgment is the negation of the angelic one at the
negated predicate, and conversely. Only one direction of this was available before. -/

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

/-- Against a negated postcondition the angelic triple is the negation of "never". -/
theorem triple_top_not_iff_not_noOutput (x : m α) (post : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x (fun a => ¬ post a) ↔ ¬ AllOutputs post x := by
  rw [triple_top_iff_someOutput, ← not_allOutputs_iff]

end Angelic

end PropAlgebra

/-! ## Recovering the `MonadLiftT` presentation

`MonadAttach` is the canonical interface for reachability here: it is core's, it carries
a lawfulness hierarchy, and core supplies instances for the transformers this library
cares about. The `MonadLiftT m SetM` spelling below is a **compatibility shim for a
downstream still phrased that way**, not the recommended API — register it locally when
migrating, rather than building against it.

Two things this does *not* say. `SetM` remains perfectly good as a **carrier**:
`support : Set α` is unchanged, and `PFunctor.FreeM.support_eq_liftM_univ` — which
genuinely folds into `SetM` as a monad — stays. What is being demoted is the lift as an
*interface*. And unlike the probability layer's `PMF` retirement, there is no upstream
force here: `SetM` is not being deprecated by Mathlib. This is a project standardizing
on core's vocabulary, nothing more.

One concrete argument for the direction, which is otherwise recorded nowhere:
`support_eq_liftM_univ` is restricted to `{γ : Type uB}`, because `FreeM.liftM` pins the
payload universe to the *direction* universe. `MonadAttach.support` on `FreeM P` carries
no such restriction. The attach-based presentation is strictly more universe-polymorphic
than the fold.

The two declarations are deliberately not instances, so that support reasoning does not
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

/-! ## Transport along a monad lift

Core proves the elimination half — lifting cannot *create* possible outputs — so a
lift can only shrink the support, and a demonic obligation therefore transfers along
it for free.

The introduction half is **not** available generically, and cannot be: nothing in
`MonadLiftT` or its lawfulness class says the lift preserves reachability, and a lift
into a monad whose `CanReturn` is uniformly `False` satisfies every law while losing
every output. A caller that needs `support (liftM x) = support x` must supply that
equation for its particular lift; `FreeM`'s powerset fold
(`PFunctor.FreeM.support_eq_liftM_univ`) is the worked instance. -/

section Transport

variable {m : Type u → Type v} {n : Type u → Type w} {α : Type u}
variable [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
variable [Monad n] [LawfulMonad n] [MonadAttach n] [LawfulMonadAttach n]
variable [MonadLiftT m n] [LawfulMonadLiftT m n]

/-- Lifting cannot create possible outputs. The set form of core's
`LawfulMonadAttach.canReturn_liftM_imp'`. -/
theorem support_liftM_subset (x : m α) : support (liftM x : n α) ⊆ support x :=
  fun _ h => LawfulMonadAttach.canReturn_liftM_imp' h

/-- A demonic guarantee survives lifting: the lifted computation has no outputs the
original did not have, so a property of all of the original's outputs holds of all of
the lift's. -/
theorem allOutputs_liftM {p : α → Prop} {x : m α} (h : AllOutputs p x) :
    AllOutputs p (liftM x : n α) :=
  fun a ha => h a (support_liftM_subset x ha)

/-- Dually, an angelic fact about the lift transfers back to the original. -/
theorem someOutput_of_someOutput_liftM {p : α → Prop} {x : m α}
    (h : SomeOutput p (liftM x : n α)) : SomeOutput p x :=
  h.imp fun _ ⟨ha, hp⟩ => ⟨support_liftM_subset x ha, hp⟩

/-- And a "never" guarantee survives lifting. -/
theorem noOutput_liftM {p : α → Prop} {x : m α} (h : NoOutput p x) :
    NoOutput p (liftM x : n α) :=
  fun a ha => h a (support_liftM_subset x ha)

end Transport

/-! ## Base instances

Core supplies `MonadAttach` and `LawfulMonadAttach` for `Id`, `Option`, `OptionT`,
`ExceptT`, `StateT`, and `ReaderT`; only the exactness fields are needed here. `Except` and
`SetM` have no core instance and are supplied below. -/

section Instances

/-- Core provides no `MonadAttach (Except ε)` at this pin, only the transformer version; this
mirrors core's `Option` instance. An identical declaration has landed upstream and ships in
Lean v4.35, so delete this instance and the one below it at that toolchain bump. -/
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

/-! ### Per-monad unfoldings

Each base monad's `CanReturn` is a concrete predicate, so membership in its support
has a concrete spelling. Every one of these is `Iff.rfl`; naming them keeps callers
from reaching through `support` and `CanReturn` with `change`. -/

section Unfoldings

variable {α : Type u}

@[simp, grind =]
theorem Id.canReturn_iff {x : Id α} {a : α} : CanReturn x a ↔ x.run = a :=
  Iff.rfl

@[simp]
theorem Id.support_eq_singleton (x : Id α) : support x = {x.run} := by
  ext a
  rw [mem_support, Id.canReturn_iff, Set.mem_singleton_iff]
  exact eq_comm

@[simp, grind =]
theorem Option.canReturn_iff {x : Option α} {a : α} : CanReturn x a ↔ x = some a :=
  Iff.rfl

@[simp, grind =]
theorem Option.support_some (a : α) : support (some a) = {a} := by
  ext b
  rw [mem_support, Option.canReturn_iff, Set.mem_singleton_iff]
  exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩

@[simp, grind =]
theorem Option.support_none : support (none : Option α) = ∅ := by
  ext b
  rw [mem_support, Option.canReturn_iff]
  simp

@[simp, grind =]
theorem Except.canReturn_iff {ε : Type u} {x : Except ε α} {a : α} :
    CanReturn x a ↔ x = Except.ok a :=
  Iff.rfl

@[simp, grind =]
theorem Except.support_ok {ε : Type u} (a : α) : support (Except.ok a : Except ε α) = {a} := by
  ext b
  rw [mem_support, Except.canReturn_iff, Set.mem_singleton_iff]
  exact ⟨fun h => (Except.ok.inj h).symm, fun h => by rw [h]⟩

@[simp, grind =]
theorem Except.support_error {ε : Type u} (e : ε) :
    support (Except.error e : Except ε α) = ∅ := by
  ext b
  rw [mem_support, Except.canReturn_iff]
  simp

@[simp, grind =]
theorem SetM.canReturn_iff {x : SetM α} {a : α} : CanReturn x a ↔ a ∈ SetM.run x :=
  Iff.rfl

@[simp]
theorem SetM.support_eq_run (x : SetM α) : support x = SetM.run x :=
  Set.ext fun _ => Iff.rfl

variable {m : Type u → Type v} [Monad m] [MonadAttach m]

@[simp, grind =]
theorem OptionT.canReturn_iff {x : OptionT m α} {a : α} :
    CanReturn x a ↔ some a ∈ support x.run :=
  Iff.rfl

@[simp, grind =]
theorem ExceptT.canReturn_iff {ε : Type u} {x : ExceptT ε m α} {a : α} :
    CanReturn x a ↔ Except.ok a ∈ support x.run :=
  Iff.rfl

end Unfoldings

/-! ### The writer transformer

`WriterT ω m` accumulates an output alongside the value, so the honest reading of its
support is the one that keeps that output: a value is possible exactly when it is
returned *together with some accumulator*. This is the same rule the measure semantics
uses for the same transformer — a writer computation denotes the underlying `m (α × ω)`
rather than discarding `ω` — and unlike `StateT` it costs nothing, because there is no
*input* index to choose. Both introduction rules survive: `pure` writes the unit, and
two composable outputs compose with their accumulators multiplied. -/

section WriterT

variable {ω : Type u} [Monoid ω]

instance instMonadAttachWriterT : MonadAttach (WriterT ω m) where
  CanReturn x a := ∃ w, CanReturn x.run (a, w)
  attach x := WriterT.mk <|
    (fun p => (⟨p.1.1, ⟨p.1.2, p.2⟩⟩, p.1.2)) <$> MonadAttach.attach x.run

omit [LawfulMonad m] [ExactMonadAttach m] [Monoid ω] in
theorem mem_support_writerT_iff {x : WriterT ω m α} {a : α} :
    a ∈ support x ↔ ∃ w, (a, w) ∈ support x.run :=
  Iff.rfl

omit [LawfulMonad m] [ExactMonadAttach m] [Monoid ω] in
theorem mem_support_of_run_writerT {x : WriterT ω m α} {a : α} {w : ω}
    (h : (a, w) ∈ support x.run) : a ∈ support x :=
  ⟨w, h⟩

instance instWeaklyLawfulMonadAttachWriterT :
    WeaklyLawfulMonadAttach (WriterT ω m) where
  map_attach {α x} := by
    refine WriterT.ext _ _ ?_
    rw [WriterT.run_map]
    have hrun : (MonadAttach.attach x : WriterT ω m (Subtype (CanReturn x))).run
        = (fun p : Subtype (CanReturn x.run) =>
            ((⟨p.1.1, ⟨p.1.2, p.2⟩⟩ : Subtype (CanReturn x)), p.1.2))
          <$> MonadAttach.attach x.run := rfl
    rw [hrun, Functor.map_map]
    simpa [Function.comp_def] using WeaklyLawfulMonadAttach.map_attach (m := m) (x := x.run)

instance instLawfulMonadAttachWriterT : LawfulMonadAttach (WriterT ω m) where
  canReturn_map_imp {α P x a} h := by
    obtain ⟨w, hw⟩ := h
    rw [WriterT.run_map] at hw
    obtain ⟨q, -, hqa⟩ := LawfulMonadAttach.canReturn_map_imp' hw
    obtain ⟨⟨v, hv⟩, w'⟩ := q
    cases hqa
    exact hv

/-- Both introduction rules hold: `pure` writes the unit accumulator, and composable
outputs compose with their accumulators multiplied. This is what `StateT` cannot have —
there is no input index to quantify over, so nothing is flattened away. -/
instance instExactMonadAttachWriterT : ExactMonadAttach (WriterT ω m) where
  canReturn_pure {α} a := ⟨1, ExactMonadAttach.canReturn_pure _⟩
  canReturn_bind {α β x f a b} h h' := by
    obtain ⟨w₁, hw₁⟩ := h
    obtain ⟨w₂, hw₂⟩ := h'
    refine ⟨w₁ * w₂, ?_⟩
    change CanReturn (x.run >>= fun p => (fun q => (q.1, p.2 * q.2)) <$> (f p.1).run) (b, w₁ * w₂)
    refine ExactMonadAttach.canReturn_bind (a := (a, w₁)) hw₁ ?_
    have hmem : ((b, w₂) : β × ω) ∈ support (f a).run := hw₂
    have himg := Set.mem_image_of_mem (fun q : β × ω => (q.1, w₁ * q.2)) hmem
    rwa [← support_map] at himg

end WriterT

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
/-- Indexed demonic implies flattened demonic: if `p` holds of every outcome from every
initial state, it holds of every possible output. The converse fails, which is the
content of the `StateT` counterexamples. -/
theorem StateT.allOutputs_of_allOutputsFrom {σ : Type u} {p : α → Prop} {x : StateT σ m α}
    (h : ∀ s, StateT.AllOutputsFrom s (fun a _ => p a) x) : AllOutputs p x :=
  fun _ ⟨s, s', hs⟩ => h s (_, s') hs

end Instances

end MonadAttach
