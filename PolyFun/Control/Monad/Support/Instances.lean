/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support

/-!
# Exact Support: Instances and Lift Transport

The instance side of the exact-support layer: the `MonadLiftT m SetM` compatibility shim,
transport of the judgments along a lawful monad lift, the `MonadAttach` / `ExactMonadAttach`
instances core lacks (`Except`, `SetM`) or leaves inexact (`WriterT`), the exactness instances
for `Id`, `Option`, `OptionT`, and `ExceptT`, and the per-monad `CanReturn` unfoldings. The
judgments and their structural laws live in `PolyFun.Control.Monad.Support`; the per-run
support of `StateT` and `ReaderT` lives in `PolyFun.Control.Monad.Support.Indexed`.
-/

@[expose] public section

universe u v w

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u}

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

end Instances

end MonadAttach
