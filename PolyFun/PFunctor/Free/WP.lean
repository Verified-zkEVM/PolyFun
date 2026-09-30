/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Support
public import PolyFun.PFunctor.Handler
public import PolyFun.Control.Monad.Algebra

/-!
# Weakest Preconditions Over the Free Monad

This file provides the extrinsic verification-condition substrate for `FreeM P`,
in two coupled layers:

* **Syntactic wp.** An `OpSpec P l` assigns each operation `a : P.A` a predicate
  transformer `(P.B a → l) → l` over an ordered carrier `l`, saying what one call
  to `a` guarantees. `FreeM.wpFold Φ` folds these per-operation specs over a free
  tree, leaving the operations uninterpreted. Every monotone spec induces an
  ordered monad algebra `OpSpec.toMAlgOrdered`, whose image of a program with a mapped output
  is the fold (`toMAlgOrdered_μ_bind_pure`); `PolyFun.PFunctor.Free.WP.Upstream` installs it as
  the exact core interpretation `OpSpec.toWPMonad`.

* **Semantic wp.** The weakest precondition of the program *interpreted* through a handler
  `s : Handler m P` is core's `wp` of `x.liftM s`; `PolyFun.PFunctor.Free.WP.Upstream` states the
  soundness of per-operation specs against it (`wpFold_le_wp_liftM`, `wpFold_eq_wp_liftM`) and
  its support consequences for the interpreted program.

The canonical `Prop`-carrier specs `OpSpec.demonic` ("every response") and
`OpSpec.angelic` ("some response") recover the support-based judgments of
`PolyFun.PFunctor.Free.Support`: `wpFold_demonic_iff_allOutputs` and
`wpFold_angelic_iff_someOutput` identify their folds with `AllOutputs` and
`SomeOutput`, so trivial-precondition ("always" / "never") triples and the
syntactic wp theory agree.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uX uY v w

namespace PFunctor

/-! ## Per-operation specifications -/

/-- A per-operation predicate-transformer specification for the interface `P` over
an ordered carrier `l`: at each position `a`, transform a postcondition on the
directions of `a` into a precondition. -/
def OpSpec (P : PFunctor.{uA, uB}) (l : Type w) : Type max uA uB w :=
  (a : P.A) → (P.B a → l) → l

namespace OpSpec

variable {P : PFunctor.{uA, uB}} {l : Type w}

/-- Monotonicity of a per-operation spec in its continuation. -/
def Mono [Preorder l] (Φ : OpSpec P l) : Prop :=
  ∀ (a : P.A) ⦃k k' : P.B a → l⦄, (∀ b, k b ≤ k' b) → Φ a k ≤ Φ a k'

/-- The demonic ("all responses") spec on the `Prop` carrier: a call to `a`
guarantees only that *every* response satisfies the continuation. -/
def demonic (P : PFunctor.{uA, uB}) : OpSpec P Prop :=
  fun _ k => ∀ b, k b

/-- The demonic specification restricted to admitted responses: a call to `a`
guarantees that every response satisfying `allows a` satisfies the continuation.

This specification is intentionally a partial-correctness condition. If no
response is admitted at a position, its obligation is vacuous; progress or
non-vacuity must be supplied separately by an operational layer. -/
def demonicUnder (allows : (a : P.A) → P.B a → Prop) : OpSpec P Prop :=
  fun a k => ∀ b, allows a b → k b

/-- The angelic ("some response") spec on the `Prop` carrier: a call to `a`
guarantees that *some* response satisfies the continuation. -/
def angelic (P : PFunctor.{uA, uB}) : OpSpec P Prop :=
  fun _ k => ∃ b, k b

/-- The angelic specification restricted to admitted responses: a call can continue
along any response satisfying `allows`. -/
def angelicUnder (allows : (a : P.A) → P.B a → Prop) : OpSpec P Prop :=
  fun a k => ∃ b, allows a b ∧ k b

theorem demonic_mono : (demonic P).Mono :=
  fun _ _ _ h hk b => h b (hk b)

theorem demonicUnder_mono (allows : (a : P.A) → P.B a → Prop) :
    (demonicUnder allows).Mono :=
  fun _ _ _ h hk b hb => h b (hk b hb)

theorem angelic_mono : (angelic P).Mono :=
  fun _ _ _ h => fun ⟨b, hb⟩ => ⟨b, h b hb⟩

theorem angelicUnder_mono (allows : (a : P.A) → P.B a → Prop) :
    (angelicUnder allows).Mono :=
  fun _ _ _ h => fun ⟨b, hb, hk⟩ => ⟨b, hb, h b hk⟩

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {l : Type w} {α β : Type v}

/-! ## Syntactic weakest precondition -/

/-- Fold a per-operation spec over a free tree: the syntactic weakest
precondition of `x` for postcondition `post`, with operations uninterpreted. -/
def wpFold (Φ : OpSpec P l) : FreeM P α → (α → l) → l
  | .pure x, post => post x
  | .liftBind a r, post => Φ a fun b => (r b).wpFold Φ post

@[simp, freeM_unfold]
theorem wpFold_pure (Φ : OpSpec P l) (x : α) (post : α → l) :
    wpFold Φ (pure x : FreeM P α) post = post x :=
  rfl

@[freeM_unfold]
theorem wpFold_liftBind (Φ : OpSpec P l) (a : P.A) (r : P.B a → FreeM P α)
    (post : α → l) :
    wpFold Φ (FreeM.liftBind a r) post = Φ a fun b => wpFold Φ (r b) post :=
  rfl

@[simp]
theorem wpFold_lift (Φ : OpSpec P l) (a : P.A) (post : P.B a → l) :
    wpFold (α := no_index (P.B a)) Φ (FreeM.lift (P := P) a) post = Φ a post :=
  rfl

/-- Weakest preconditions compose through sequencing across result universes. -/
theorem wpFold_bind' {X : Type uX} {Y : Type uY} (Φ : OpSpec P l)
    (x : FreeM P X) (f : X → FreeM P Y) (post : Y → l) :
    wpFold Φ (x.bind f) post = wpFold Φ x fun a => wpFold Φ (f a) post := by
  induction x with
  | pure x => rfl
  | lift_bind a r ih => exact congrArg (Φ a) (funext fun b => ih b)

theorem wpFold_bind (Φ : OpSpec P l) (x : FreeM P α) (f : α → FreeM P β)
    (post : β → l) :
    wpFold Φ (x >>= f) post = wpFold Φ x fun a => wpFold Φ (f a) post :=
  wpFold_bind' Φ x f post
/-! ### The rest of the `do` fragment

`wpFold` is a fold, so every combinator `do`-notation elaborates to reduces to `wpFold_bind` and
`wpFold_pure`; the equations below state the results directly so `simp` need not rediscover
them. -/

@[simp]
theorem wpFold_map (Φ : OpSpec P l) (f : α → β) (x : FreeM P α) (post : β → l) :
    wpFold Φ (f <$> x) post = wpFold Φ x fun a => post (f a) := by
  induction x with
  | pure a => rfl
  | lift_bind a r ih => exact congrArg (Φ a) (funext fun b => ih b)

@[simp]
theorem wpFold_seq (Φ : OpSpec P l) (f : FreeM P (α → β)) (x : FreeM P α) (post : β → l) :
    wpFold Φ (f <*> x) post = wpFold Φ f fun g => wpFold Φ x fun a => post (g a) := by
  induction f with
  | pure g => exact wpFold_map Φ g x post
  | lift_bind a r ih => exact congrArg (Φ a) (funext fun b => ih b)

@[simp]
theorem wpFold_seqLeft (Φ : OpSpec P l) (x : FreeM P α) (y : FreeM P β) (post : α → l) :
    wpFold Φ (x <* y) post = wpFold Φ x fun a => wpFold Φ y fun _ => post a := by
  rw [seqLeft_eq_bind, wpFold_bind]
  simp only [wpFold_bind, wpFold_pure]

@[simp]
theorem wpFold_seqRight (Φ : OpSpec P l) (x : FreeM P α) (y : FreeM P β) (post : β → l) :
    wpFold Φ (x *> y) post = wpFold Φ x fun _ => wpFold Φ y post := by
  rw [seqRight_eq_bind, wpFold_bind]

@[simp]
theorem wpFold_ite (Φ : OpSpec P l) (c : Prop) [Decidable c] (x y : FreeM P α) (post : α → l) :
    wpFold Φ (if c then x else y) post = if c then wpFold Φ x post else wpFold Φ y post := by
  split <;> rfl

@[simp]
theorem wpFold_dite (Φ : OpSpec P l) (c : Prop) [Decidable c] (x : c → FreeM P α)
    (y : ¬ c → FreeM P α) (post : α → l) :
    wpFold Φ (if h : c then x h else y h) post =
      if h : c then wpFold Φ (x h) post else wpFold Φ (y h) post := by
  split <;> rfl

@[simp]
theorem wpFold_option_elim {γ : Type uX} (Φ : OpSpec P l) (o : Option γ) (x : FreeM P α)
    (f : γ → FreeM P α) (post : α → l) :
    wpFold Φ (o.elim x f) post = o.elim (wpFold Φ x post) fun c => wpFold Φ (f c) post := by
  cases o <;> rfl

@[simp]
theorem wpFold_sum_elim {γ : Type uX} {δ : Type uY} (Φ : OpSpec P l) (s : γ ⊕ δ)
    (f : γ → FreeM P α) (g : δ → FreeM P α) (post : α → l) :
    wpFold Φ (s.elim f g) post =
      s.elim (fun c => wpFold Φ (f c) post) fun d => wpFold Φ (g d) post := by
  cases s <;> rfl

theorem wpFold_mono [Preorder l] {Φ : OpSpec P l} (hΦ : Φ.Mono) (x : FreeM P α)
    {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    wpFold Φ x post ≤ wpFold Φ x post' := by
  induction x with
  | pure x => exact h x
  | lift_bind a r ih => exact hΦ a fun b => ih b

/-! ## Reachable outputs under an operationalization -/

/-- Outputs reachable when each operation may return exactly the responses admitted by
`allows`. This is the set view of the angelic predicate transformer, not a generic
interpretation of `MonadAttach.CanReturn`. -/
def reachableUnder (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) : Set α :=
  {result | x.wpFold (OpSpec.angelicUnder allows) (· = result)}

/-- Structural reachability when every typed response is admitted. -/
def reachable (x : FreeM P α) : Set α :=
  x.reachableUnder (fun _ _ => True)

@[simp]
theorem reachableUnder_pure (allows : (a : P.A) → P.B a → Prop) (result : α) :
    reachableUnder allows (pure result : FreeM P α) = {result} := by
  ext a
  simp [reachableUnder, eq_comm]

theorem reachableUnder_liftBind (allows : (a : P.A) → P.B a → Prop)
    (position : P.A) (next : P.B position → FreeM P α) :
    reachableUnder allows (FreeM.liftBind position next) =
      ⋃ direction ∈ {direction | allows position direction},
        reachableUnder allows (next direction) := by
  ext result
  simp only [reachableUnder, Set.mem_ofPred_eq, wpFold_liftBind,
    OpSpec.angelicUnder, Set.mem_iUnion, exists_prop]

@[simp]
theorem reachableUnder_lift (allows : (a : P.A) → P.B a → Prop)
    (position : P.A) :
    reachableUnder (α := no_index (P.B position)) allows (FreeM.lift position) =
      {direction | allows position direction} := by
  rw [FreeM.lift, reachableUnder_liftBind]
  ext direction
  simp

/-- The angelic fold is existential quantification over reachable outputs. -/
theorem wpFold_angelicUnder_iff_exists_reachable
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → Prop) :
    x.wpFold (OpSpec.angelicUnder allows) post ↔
      ∃ result ∈ x.reachableUnder allows, post result := by
  induction x with
  | pure result =>
      simp [reachableUnder]
  | lift_bind position next ih =>
      rw [wpFold_bind', wpFold_lift, ← FreeM.liftBind_eq, reachableUnder_liftBind]
      simp only [OpSpec.angelicUnder, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨direction, hallowed, hpost⟩
        obtain ⟨result, hreach, hresult⟩ := (ih direction).mp hpost
        exact ⟨result, ⟨direction, hallowed, hreach⟩, hresult⟩
      · rintro ⟨result, ⟨direction, hallowed, hreach⟩, hresult⟩
        exact ⟨direction, hallowed,
          (ih direction).mpr ⟨result, hreach, hresult⟩⟩

@[simp]
theorem reachableUnder_bind (allows : (a : P.A) → P.B a → Prop)
    (x : FreeM P α) (next : α → FreeM P β) :
    (x >>= next).reachableUnder allows =
      ⋃ result ∈ x.reachableUnder allows, (next result).reachableUnder allows := by
  ext result
  change wpFold (OpSpec.angelicUnder allows) (x >>= next) (· = result) ↔ _
  rw [wpFold_bind, wpFold_angelicUnder_iff_exists_reachable]
  simp only [Set.mem_iUnion, exists_prop]
  exact exists_congr fun a => and_congr_right fun _ => Iff.rfl

/-- Reachability through sequencing with independent result universes. -/
@[simp]
theorem reachableUnder_bind' {X : Type uX} {Y : Type uY}
    (allows : (a : P.A) → P.B a → Prop) (program : FreeM P X)
    (next : X → FreeM P Y) :
    (FreeM.bind program next).reachableUnder allows =
      ⋃ result ∈ program.reachableUnder allows, (next result).reachableUnder allows := by
  ext result
  change wpFold (OpSpec.angelicUnder allows) (program.bind next) (· = result) ↔ _
  rw [wpFold_bind', wpFold_angelicUnder_iff_exists_reachable]
  simp only [Set.mem_iUnion, exists_prop]
  exact exists_congr fun a => and_congr_right fun _ => Iff.rfl

theorem reachableUnder_mono {allows₁ allows₂ : (a : P.A) → P.B a → Prop}
    (h : ∀ position direction, allows₁ position direction → allows₂ position direction)
    (x : FreeM P α) : x.reachableUnder allows₁ ⊆ x.reachableUnder allows₂ := by
  intro result hresult
  induction x with
  | pure value => simpa using hresult
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq, reachableUnder_liftBind] at hresult ⊢
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hresult ⊢
      obtain ⟨direction, hallowed, hchild⟩ := hresult
      exact ⟨direction, h position direction hallowed, ih direction hchild⟩

/-- Mapping leaf values maps the set of outputs reachable under the same responses. -/
@[simp]
theorem reachableUnder_map {X : Type uX} {Y : Type uY}
    (allows : (a : P.A) → P.B a → Prop) (function : X → Y)
    (program : FreeM P X) :
    (FreeM.map function program).reachableUnder allows =
      function '' program.reachableUnder allows := by
  rw [← FreeM.bind_pure_comp, reachableUnder_bind']
  ext result
  simp [Set.mem_image, eq_comm]

theorem reachableUnder_liftObj {X : Type uX}
    (allows : (a : P.A) → P.B a → Prop) (object : P.Obj X) :
    (FreeM.liftObj object).reachableUnder allows =
      object.2 '' {direction | allows object.1 direction} := by
  simp [FreeM.liftObj]

/-- Functor mapping preserves the admitted response policy and maps reachable results. -/
@[simp]
theorem reachableUnder_functorMap (allows : (a : P.A) → P.B a → Prop)
    (function : α → β) (program : FreeM P α) :
    (function <$> program).reachableUnder allows = function '' program.reachableUnder allows :=
  reachableUnder_map allows function program

/-- A path is admitted when every direction on it is admitted at its operation. -/
def Path.AllowedUnder (allows : (a : P.A) → P.B a → Prop) :
    (x : FreeM P α) → Path x → Prop
  | .pure _, _ => True
  | .liftBind position next, ⟨direction, path⟩ =>
      allows position direction ∧ AllowedUnder allows (next direction) path

/-- The terminal path has no response constraints. -/
@[simp]
theorem Path.allowedUnder_pure (allows : (a : P.A) → P.B a → Prop)
    (value : α) (path : Path (pure value : FreeM P α)) :
    Path.AllowedUnder allows (pure value) path := trivial

/-- An admitted node path takes an admitted response and an admitted continuation path. -/
theorem Path.allowedUnder_liftBind (allows : (a : P.A) → P.B a → Prop)
    (position : P.A) (next : P.B position → FreeM P α)
    (direction : P.B position) (path : Path (next direction)) :
    Path.AllowedUnder allows (FreeM.liftBind position next) ⟨direction, path⟩ ↔
      allows position direction ∧ Path.AllowedUnder allows (next direction) path := Iff.rfl

/-- Reachability is witnessed by an admitted root-to-leaf path. -/
theorem mem_reachableUnder_iff_exists_path
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (result : α) :
    result ∈ x.reachableUnder allows ↔
      ∃ path : Path x, Path.AllowedUnder allows x path ∧ x.output path = result := by
  induction x with
  | pure value =>
      change (value = result) ↔
        ∃ path : Path (pure value : FreeM P α),
          Path.AllowedUnder allows (pure value) path ∧ value = result
      constructor
      · intro h
        exact ⟨⟨⟩, trivial, h⟩
      · rintro ⟨_, _, h⟩
        exact h
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq, reachableUnder_liftBind]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨direction, hallowed, hchild⟩
        obtain ⟨path, hpath, hresult⟩ := (ih direction).mp hchild
        exact ⟨⟨direction, path⟩, ⟨hallowed, hpath⟩, hresult⟩
      · rintro ⟨⟨direction, path⟩, ⟨hallowed, hpath⟩, hresult⟩
        exact ⟨direction, hallowed,
          (ih direction).mpr ⟨path, hpath, hresult⟩⟩

/-- Running the powerset handler gives the same reachable outputs. -/
theorem reachableUnder_eq_liftM
    {γ : Type uB} (allows : (a : P.A) → P.B a → Prop) (x : FreeM P γ) :
    x.reachableUnder allows =
      SetM.run (x.liftM (fun position =>
        ({direction | allows position direction} : SetM _))) := by
  induction x with
  | pure result =>
      rw [reachableUnder_pure]
      change {result} = SetM.run (pure result : SetM γ)
      rfl
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq, reachableUnder_liftBind]
      change _ = ⋃ direction ∈ {direction | allows position direction},
        SetM.run ((next direction).liftM (fun position =>
          ({direction | allows position direction} : SetM _)))
      exact iSup_congr fun direction => iSup_congr fun _ => ih direction

/-- Full-response reachability agrees with the free tree's attachment predicate. -/
theorem reachable_eq_support (x : FreeM P α) :
    x.reachable = MonadAttach.support x := by
  induction x with
  | pure result => simp [reachable, reachableUnder_pure]
  | lift_bind position next ih =>
      rw [reachable, ← FreeM.liftBind_eq, reachableUnder_liftBind, support_liftBind]
      simp only [Set.ofPred_true, Set.biUnion_univ]
      exact iSup_congr fun direction => ih direction

theorem mem_reachable_iff_canReturn (x : FreeM P α) (result : α) :
    result ∈ x.reachable ↔ MonadAttach.CanReturn x result := by
  rw [reachable_eq_support]
  rfl

/-! ## Admitted-response leaf contracts -/

/-- Every leaf reachable by choosing admitted responses satisfies `accept`.

This is the relation-restricted demonic weakest precondition, not a termination
or progress assertion. In particular, a query with no admitted response
satisfies every leaf contract vacuously. -/
def LeavesSatisfyUnder (allows : (a : P.A) → P.B a → Prop) (accept : α → Prop) :
    FreeM P α → Prop :=
  fun program => wpFold (OpSpec.demonicUnder allows) program accept

@[simp]
theorem leavesSatisfyUnder_pure (allows : (a : P.A) → P.B a → Prop)
    (accept : α → Prop) (result : α) :
    (pure result : FreeM P α).LeavesSatisfyUnder allows accept ↔ accept result :=
  Iff.rfl

theorem leavesSatisfyUnder_liftBind (allows : (a : P.A) → P.B a → Prop)
    (accept : α → Prop) (position : P.A) (next : P.B position → FreeM P α) :
    (FreeM.liftBind position next).LeavesSatisfyUnder allows accept ↔
      ∀ direction, allows position direction →
        (next direction).LeavesSatisfyUnder allows accept :=
  Iff.rfl

/-- Weakening the required leaf predicate preserves whole-tree conformance. -/
theorem LeavesSatisfyUnder.mono {allows : (a : P.A) → P.B a → Prop}
    {accept accept' : α → Prop} (haccept : ∀ result, accept result → accept' result)
    {program : FreeM P α} (h : program.LeavesSatisfyUnder allows accept) :
    program.LeavesSatisfyUnder allows accept' :=
  wpFold_mono (OpSpec.demonicUnder_mono allows) program haccept h

/-- Mapping a function changes only the predicate imposed on returned leaves. -/
theorem leavesSatisfyUnder_map_iff (allows : (a : P.A) → P.B a → Prop)
    {X : Type uX} {Y : Type uY} (accept : Y → Prop) (function : X → Y)
    (program : FreeM P X) :
    (FreeM.map function program).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows (accept ∘ function) := by
  induction program with
  | pure result => rfl
  | lift_bind position next ih =>
      change
        (∀ direction, allows position direction →
          (FreeM.map function (next direction)).LeavesSatisfyUnder allows accept) ↔
        ∀ direction, allows position direction →
          (next direction).LeavesSatisfyUnder allows (accept ∘ function)
      exact forall_congr' fun direction =>
        imp_congr_right fun _ => ih direction

/-- Whole-tree result conformance composes through monadic sequencing. -/
theorem leavesSatisfyUnder_bind_iff (allows : (a : P.A) → P.B a → Prop)
    {X : Type uX} {Y : Type uY} (accept : Y → Prop) (program : FreeM P X)
    (next : X → FreeM P Y) :
    (FreeM.bind program next).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows
        (fun result => (next result).LeavesSatisfyUnder allows accept) := by
  induction program with
  | pure result => rfl
  | lift_bind position continuation ih =>
      change
        (∀ direction, allows position direction →
          (FreeM.bind (continuation direction) next).LeavesSatisfyUnder allows accept) ↔
        ∀ direction, allows position direction →
          (continuation direction).LeavesSatisfyUnder allows
            (fun result => (next result).LeavesSatisfyUnder allows accept)
      exact forall_congr' fun direction =>
        imp_congr_right fun _ => ih direction

/-- The relation-restricted demonic WP quantifies over the reachable outputs. -/
theorem leavesSatisfyUnder_iff_forall_reachable
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → Prop) :
    x.LeavesSatisfyUnder allows post ↔
      ∀ result ∈ x.reachableUnder allows, post result := by
  induction x with
  | pure result =>
      simp [LeavesSatisfyUnder, reachableUnder]
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq, leavesSatisfyUnder_liftBind, reachableUnder_liftBind]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro h result ⟨direction, hallowed, hchild⟩
        exact (ih direction).mp (h direction hallowed) result hchild
      · intro h direction hallowed
        apply (ih direction).mpr
        intro result hchild
        exact h result ⟨direction, hallowed, hchild⟩

section FreeHandler

variable {Q : PFunctor.{uA₂, uB₂}} {α : Type uB}

/-- Interpreting a finite free program through leaf-conforming free handlers
preserves its admitted-response leaf contract.

Unlike the map and bind laws above, the program result type shares the source
interface's direction universe. This is exactly the homogeneous result
constraint of the upstream `FreeM.liftM`; the target interface's position and
direction universes remain independent. -/
theorem leavesSatisfyUnder_liftM
    (handler : (position : P.A) → FreeM Q (P.B position))
    (outerAllows : (position : P.A) → P.B position → Prop)
    (innerAllows : (position : Q.A) → Q.B position → Prop)
    (accept : α → Prop)
    (hhandler : ∀ position,
      (handler position).LeavesSatisfyUnder innerAllows (outerAllows position))
    (program : FreeM P α)
    (hprogram : program.LeavesSatisfyUnder outerAllows accept) :
    (program.liftM handler).LeavesSatisfyUnder innerAllows accept := by
  induction program with
  | pure result => exact hprogram
  | lift_bind position next ih =>
      change
        (handler position >>= fun direction =>
          (next direction).liftM handler).LeavesSatisfyUnder innerAllows accept
      change
        (FreeM.bind (handler position)
          (fun direction => (next direction).liftM handler)).LeavesSatisfyUnder
          innerAllows accept
      rw [leavesSatisfyUnder_bind_iff]
      exact (hhandler position).mono fun direction hdirection =>
        ih direction (hprogram direction hdirection)

/-- A free handler whose admitted outputs respect the source response constraint
cannot introduce new reachable results. This is the operational counterpart of
`leavesSatisfyUnder_liftM`. -/
theorem reachableUnder_liftM_subset
    (handler : (position : P.A) → FreeM Q (P.B position))
    (outerAllows : (position : P.A) → P.B position → Prop)
    (innerAllows : (position : Q.A) → Q.B position → Prop)
    (hhandler : ∀ position,
      (handler position).LeavesSatisfyUnder innerAllows (outerAllows position))
    (program : FreeM P α) :
    (program.liftM handler).reachableUnder innerAllows ⊆
      program.reachableUnder outerAllows := by
  have hprogram : program.LeavesSatisfyUnder outerAllows
      (fun result => result ∈ program.reachableUnder outerAllows) :=
    (leavesSatisfyUnder_iff_forall_reachable outerAllows _ _).mpr
      (fun _ hresult => hresult)
  have hlift := leavesSatisfyUnder_liftM handler outerAllows innerAllows _
    hhandler program hprogram
  exact (leavesSatisfyUnder_iff_forall_reachable innerAllows _ _).mp hlift

/-- Interpreting free operations by free programs cannot create new leaf values. -/
theorem reachable_liftM_subset
    (handler : (position : P.A) → FreeM Q (P.B position))
    (program : FreeM P α) :
    (program.liftM handler).reachable ⊆ program.reachable := by
  exact reachableUnder_liftM_subset handler (fun _ _ => True) (fun _ _ => True)
    (by
      intro position
      exact (leavesSatisfyUnder_iff_forall_reachable _ _ _).mpr
        (fun _ _ => trivial)) program

end FreeHandler

/-! ## The induced ordered monad algebra -/

/-- Every monotone per-operation spec over a complete lattice induces an ordered
monad algebra on `FreeM P`: the fold at the identity postcondition. -/
@[instance_reducible]
def _root_.PFunctor.OpSpec.toMAlgOrdered {l : Type v} [CompleteLattice l]
    (Φ : OpSpec P l) (hΦ : Φ.Mono) : MAlgOrdered (FreeM P) l where
  μ x := wpFold Φ x id
  μ_pure _ := rfl
  μ_bind_mono f g hfg x := by
    rw [wpFold_bind, wpFold_bind]
    exact wpFold_mono hΦ x hfg

/-- The algebra induced by a per-operation spec sends a program with a mapped output to its
syntactic fold. -/
theorem toMAlgOrdered_μ_bind_pure {l : Type v} [CompleteLattice l]
    (Φ : OpSpec P l) (hΦ : Φ.Mono) (x : FreeM P α) (post : α → l) :
    letI := Φ.toMAlgOrdered hΦ
    MAlgOrdered.μ (x >>= fun a => pure (post a)) = wpFold Φ x post := by
  change wpFold Φ (x >>= fun a => pure (post a)) id = _
  rw [wpFold_bind]
  rfl

/-! ## Coherence with the canonical support -/

section Support

open MonadAttach

variable {α : Type v}

/-- With every response admitted, the restricted leaf contract is the
canonical all-outputs judgment. -/
theorem leavesSatisfyUnder_all_iff_allOutputs (x : FreeM P α) (post : α → Prop) :
    x.LeavesSatisfyUnder (fun _ _ => True) post ↔ AllOutputs post x := by
  induction x with
  | pure x => simp
  | lift_bind a r ih =>
      rw [← FreeM.liftBind_eq, leavesSatisfyUnder_liftBind, allOutputs_liftBind]
      simp only [true_implies]
      exact forall_congr' fun b => ih b

/-- The demonic fold is the "always" judgment over the canonical support. -/
theorem wpFold_demonic_iff_allOutputs (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.demonic P) x post ↔ AllOutputs post x := by
  induction x with
  | pure x => simp
  | lift_bind a r ih =>
      rw [wpFold_bind', wpFold_lift, ← FreeM.liftBind_eq, allOutputs_liftBind]
      exact forall_congr' fun b => ih b

/-- The angelic fold is the "some output" judgment over the canonical support. -/
theorem wpFold_angelic_iff_someOutput (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.angelic P) x post ↔ SomeOutput post x := by
  induction x with
  | pure x => simp
  | lift_bind a r ih =>
      rw [wpFold_bind', wpFold_lift, ← FreeM.liftBind_eq, someOutput_liftBind]
      exact exists_congr fun b => ih b

/-- The demonic fold of a negated postcondition is the "never" judgment. -/
theorem wpFold_demonic_not_iff_noOutput (x : FreeM P α) (post : α → Prop) :
    wpFold (OpSpec.demonic P) x (fun a => ¬ post a) ↔ NoOutput post x :=
  wpFold_demonic_iff_allOutputs x fun a => ¬ post a

end Support

end FreeM

end PFunctor
