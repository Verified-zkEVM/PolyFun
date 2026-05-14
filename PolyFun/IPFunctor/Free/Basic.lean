/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic
public import PolyFun.PFunctor.Free.Basic

/-!
# State-Indexed Free Monad on an `IPFunctor`

This file defines `IPFunctor.FreeM P : I → Type v → Type _`, the free monad over a state-indexed
polynomial functor. Pure return values are allowed in any ambient state; the available head
shapes at each `roll` are gated by the current state, and the state for each continuation is
determined by `P.st`.

Because the post-state of each branch can depend on the chosen response, `FreeM P s α` is **not**
a `Monad` — its bind takes a state-polymorphic continuation. For a variant that tracks the
post-state statically and is therefore an `IndexedMonad` in the sense of Atkey, see
[`PolyFun/IPFunctor/Free/Indexed.lean`](Indexed.lean).

When the index type is a `Unique`, the forgetful map `IPFunctor.FreeM.erase` collapses
`FreeM P s α` into `PFunctor.FreeM P.toPFunctor α`.
-/

@[expose] public section

universe uI uA uB v w

namespace IPFunctor

variable {I : Type uI}

/-- The free monad on a state-indexed polynomial functor.
Analogous to `PFunctor.FreeM`, but the available shapes at each step depend on the ambient
state, and the state for each continuation branch is updated by `P.st`. -/
inductive FreeM (P : IPFunctor.{uI, uA, uB} I) :
    I → Type v → Type (max uI uA uB (v + 1))
  /-- A pure return value of `x`, available at any state `s`. -/
  | pure (s : I) {α} (x : α) : FreeM P s α
  /-- Roll a value in the shapes available at `s` into a continuation, with the state for each
  branch determined by `P.st`. -/
  | roll (s : I) {α} (x : P.A s)
      (r : (b : P.B s x) → FreeM P (P.st s x b) α) : FreeM P s α

namespace FreeM

variable {P : IPFunctor.{uI, uA, uB} I} {α β γ : Type v}

instance (s : I) : Pure (FreeM P s) where
  pure := .pure s

/-! ## Lifting -/

/-- Lift an object of the base `IPFunctor` at state `s` into the free monad. -/
@[always_inline, inline, reducible]
def lift (s : I) (x : P.Obj α s) : FreeM P s α :=
  FreeM.roll s x.1 (fun b => FreeM.pure (P.st s x.1 b) (x.2 b))

/-- Lift a shape `a : P.A s` into the free monad, returning its response. -/
@[always_inline, inline, reducible]
def liftA (s : I) (a : P.A s) : FreeM P s (P.B s a) :=
  FreeM.roll s a (fun b => FreeM.pure (P.st s a b) b)

/-! ## Bind

`bind` here is not the `Monad.bind` shape: the continuation `g` must accept the leaf state
explicitly because different branches of the tree end at different states. -/

/-- State-polymorphic bind on `FreeM P`. -/
@[always_inline, inline]
protected def bind : {s : I} → FreeM P s α → ((s' : I) → α → FreeM P s' β) → FreeM P s β
  | _, FreeM.pure s x,   g => g s x
  | _, FreeM.roll s x r, g => FreeM.roll s x (fun b => FreeM.bind (r b) g)

@[simp]
lemma bind_pure (s : I) (x : α) (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.pure (P := P) s x) g = g s x := rfl

@[simp]
lemma bind_roll (s : I) (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α)
    (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.roll s x r) g = FreeM.roll s x (fun b => FreeM.bind (r b) g) := rfl

@[simp]
lemma bind_lift (s : I) (x : P.Obj α s) (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.lift s x) g =
      FreeM.roll s x.1 (fun b => g (P.st s x.1 b) (x.2 b)) := rfl

/-! ## Injectivity -/

lemma pure_inj (s : I) (x y : α) :
    FreeM.pure (P := P) s x = FreeM.pure s y ↔ x = y := by
  refine ⟨?_, fun h => by rw [h]⟩
  intro h; cases h; rfl

@[simp]
lemma roll_inj (s : I) (x x' : P.A s)
    (r : (b : P.B s x) → FreeM P (P.st s x b) α)
    (r' : (b : P.B s x') → FreeM P (P.st s x' b) α) :
    FreeM.roll s x r = FreeM.roll s x' r' ↔ ∃ h : x = x', h ▸ r = r' := by
  by_cases hx : x = x'
  · subst hx; simp
  · refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h hx⟩
    cases h; exact (hx rfl).elim

/-! ## Functor / LawfulFunctor -/

/-- Functor map on `FreeM P s`. The state is unchanged because mapping only rewrites leaves;
the state argument tracks the current position. -/
protected def map (s : I) (f : α → β) : P.FreeM s α → P.FreeM s β
  | .pure _ x   => .pure s (f x)
  | .roll _ x r => .roll s x (fun b => FreeM.map (P.st s x b) f (r b))

@[simp]
lemma map_pure (s : I) (f : α → β) (x : α) :
    FreeM.map (P := P) s f (FreeM.pure s x) = FreeM.pure s (f x) := rfl

@[simp]
lemma map_roll (s : I) (f : α → β) (x : P.A s)
    (r : (b : P.B s x) → FreeM P (P.st s x b) α) :
    FreeM.map s f (FreeM.roll s x r) =
      FreeM.roll s x (fun b => FreeM.map (P.st s x b) f (r b)) := rfl

@[simp]
lemma map_lift (s : I) (f : α → β) (x : P.Obj α s) :
    FreeM.map s f (FreeM.lift s x) =
      FreeM.lift s ⟨x.1, fun b => f (x.2 b)⟩ := rfl

/-- While `FreeM P s` is not a `Monad` (because `roll`'s continuation can change state),
mapping leaves a tree at the same state, so the `Functor` instance is well-defined. -/
instance (s : I) : Functor (P.FreeM s) where
  map := FreeM.map s
  mapConst b x := FreeM.map s (fun _ => b) x

instance (s : I) : LawfulFunctor (P.FreeM s) where
  map_const := rfl
  id_map x := by
    change FreeM.map s id x = x
    induction x with
    | pure s' x => rfl
    | roll s' a r ih => exact congrArg (FreeM.roll s' a) (funext ih)
  comp_map f g x := by
    change FreeM.map s (g ∘ f) x = FreeM.map s g (FreeM.map s f x)
    induction x with
    | pure s' x => rfl
    | roll s' a r ih => exact congrArg (FreeM.roll s' a) (funext (fun b => ih b f))

/-! ## Induction principles

The motive must be state-indexed (`∀ s, FreeM P s α → Prop`) because the continuation in `roll`
lands at a different state than its parent. -/

/-- Induction principle for `FreeM P` with a state-indexed motive (Prop-valued).
The `roll` case may use the inductive hypothesis at each successor state. -/
@[elab_as_elim]
protected def inductionOn {C : ∀ s, FreeM P s α → Prop}
    (pure : ∀ s x, C s (FreeM.pure s x))
    (roll : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α),
      (∀ b, C (P.st s x b) (r b)) → C s (FreeM.roll s x r)) :
    ∀ {s} (oa : FreeM P s α), C s oa
  | _, FreeM.pure s x   => pure s x
  | _, FreeM.roll s x r => roll s x r (fun b => FreeM.inductionOn pure roll (r b))

/-- Dependent recursor (`Type*`-valued) for `FreeM P` with state-indexed motive. -/
@[elab_as_elim]
protected def construct {C : ∀ s, FreeM P s α → Type*}
    (pure : ∀ s (x : α), C s (FreeM.pure s x))
    (roll : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α),
      (∀ b, C (P.st s x b) (r b)) → C s (FreeM.roll s x r)) :
    ∀ {s} (oa : FreeM P s α), C s oa
  | _, .pure s x   => pure s x
  | _, .roll s x r => roll s x r (fun b => FreeM.construct pure roll (r b))

section construct

variable {C : ∀ s, FreeM P s α → Type*}
  (h_pure : ∀ s (x : α), C s (FreeM.pure s x))
  (h_roll : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α),
      (∀ b, C (P.st s x b) (r b)) → C s (FreeM.roll s x r))

@[simp]
lemma construct_pure (s : I) (x : α) :
    FreeM.construct h_pure h_roll (FreeM.pure (P := P) s x) = h_pure s x := rfl

@[simp]
lemma construct_roll (s : I) (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α) :
    (FreeM.construct h_pure h_roll (FreeM.roll s x r) : C s (FreeM.roll s x r)) =
      h_roll s x r (fun b => FreeM.construct h_pure h_roll (r b)) := rfl

@[simp]
lemma construct_lift (s : I) (x : P.Obj α s) :
    (FreeM.construct h_pure h_roll (FreeM.lift s x) : C s (FreeM.lift s x)) =
      h_roll s x.1 (fun b => FreeM.pure (P.st s x.1 b) (x.2 b))
        (fun b => h_pure (P.st s x.1 b) (x.2 b)) := rfl

end construct

/-! ## `mapM`: interpreting `FreeM` into a monad

The responses `P.B s a` live in `Type uB`, so the target monad `m` is constrained to
`Type uB → Type w` and the value type `α` to `Type uB`. -/

section mapM

variable {m : Type uB → Type w} {α β : Type uB}

/-- Interpret a `FreeM P` into an arbitrary monad `m`, given for each state `s` and shape
`a : P.A s` a way to produce a response `m (P.B s a)`. The leaf state is erased on the
target side; if you need it, package the leaf state into the response or use `FreeM₂`. -/
protected def mapM [Pure m] [Bind m] (h : (s : I) → (a : P.A s) → m (P.B s a)) :
    {s : I} → FreeM P s α → m α
  | _, .pure _ x   => Pure.pure x
  | _, .roll s a r => h s a >>= fun b => (r b).mapM h

variable [Monad m] (h : (s : I) → (a : P.A s) → m (P.B s a))

@[simp]
lemma mapM_pure (s : I) (x : α) :
    (FreeM.pure (P := P) s x).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_pure' (s : I) (x : α) :
    (Pure.pure x : FreeM P s α).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_roll (s : I) (a : P.A s) (r : (b : P.B s a) → FreeM P (P.st s a b) α) :
    (FreeM.roll s a r).mapM h = h s a >>= fun b => (r b).mapM h := rfl

@[simp]
lemma mapM_lift [LawfulMonad m] (s : I) (x : P.Obj α s) :
    (FreeM.lift s x).mapM h = h s x.1 >>= fun b => Pure.pure (x.2 b) := by
  simp [FreeM.mapM]

variable [LawfulMonad m]

@[simp]
lemma mapM_liftA (s : I) (a : P.A s) :
    (FreeM.liftA s a).mapM h = h s a := by
  simp [FreeM.mapM]

@[simp]
lemma mapM_map (s : I) (x : FreeM P s α) (f : α → β) :
    (f <$> x).mapM h = f <$> x.mapM h := by
  change (FreeM.map s f x).mapM h = f <$> x.mapM h
  induction x with
  | pure s' x => simp [FreeM.map, FreeM.mapM]
  | roll s' a r ih =>
      simp only [FreeM.map, FreeM.mapM, map_bind]
      exact congrArg _ (funext (fun b => ih b f))

end mapM

/-! ## Forgetful map to `PFunctor.FreeM`

When the index type has at most one element, the state information carries no content and an
`IPFunctor` collapses to a `PFunctor`. We provide a forgetful map `erase` from
`IPFunctor.FreeM P s α` to `PFunctor.FreeM P.toPFunctor α` (at any `s : I`). The reverse
direction would require transport gymnastics through `P.st`'s data-dependent post-state; we
do not provide it. -/

section erase

variable [Unique I]

/-- Remove all indexing information from an `IPFunctor.FreeM` to obtain a `PFunctor.FreeM`,
when the index type is `Unique`. -/
def erase (P : IPFunctor I) (s : I) : {α : Type v} → P.FreeM s α → P.toPFunctor.FreeM α
  | _, .pure _ x   => PFunctor.FreeM.pure x
  | _, .roll _ x r =>
      PFunctor.FreeM.roll
        (show P.A default from Unique.eq_default s ▸ x)
        (fun b => erase P (P.st s _ _) (r (Unique.eq_default s ▸ b)))

@[simp]
lemma erase_pure (P : IPFunctor I) (s : I) (x : α) :
    erase P s (FreeM.pure s x) = PFunctor.FreeM.pure x := rfl

/-- Unfolding lemma for `erase` on a `roll` constructor at an arbitrary `[Unique I]` index.
Not marked `@[simp]` because the resulting transports keep simp's syntactic matcher from
firing reliably; for the practically useful `I = PUnit` case see `erase_roll_punit`. The
equation is `rfl`, so callers needing it can use `unfold erase` or invoke it directly. -/
lemma erase_roll (P : IPFunctor I) (s : I) (x : P.A s)
    (r : (b : P.B s x) → P.FreeM (P.st s x b) α) :
    erase P s (FreeM.roll s x r) =
      PFunctor.FreeM.roll
        (show P.A default from Unique.eq_default s ▸ x)
        (fun b => erase P (P.st s _ _) (r (Unique.eq_default s ▸ b))) := rfl

end erase

/-! ### `PUnit`-specialized `erase` simp lemmas

When the index type is literally `PUnit`, the `Unique.eq_default` transports collapse
definitionally and simp can fire cleanly. These specializations cover the practically common
case where one wants to use `IPFunctor.FreeM` as a state-aware wrapper over `PFunctor.FreeM`
without any actual state content. -/

section erasePUnit

variable {Q : IPFunctor PUnit} {α : Type v}

@[simp]
lemma erase_punit_pure (x : α) :
    erase Q PUnit.unit (FreeM.pure PUnit.unit x : Q.FreeM PUnit.unit α) =
      PFunctor.FreeM.pure x := rfl

@[simp]
lemma erase_punit_roll (x : Q.A PUnit.unit)
    (r : (b : Q.B PUnit.unit x) → Q.FreeM (Q.st PUnit.unit x b) α) :
    erase Q PUnit.unit (FreeM.roll PUnit.unit x r) =
      PFunctor.FreeM.roll x (fun b => erase Q (Q.st PUnit.unit x b) (r b)) := rfl

@[simp]
lemma erase_punit_lift (x : Q.Obj α PUnit.unit) :
    erase Q PUnit.unit (FreeM.lift PUnit.unit x) =
      PFunctor.FreeM.lift (P := Q.toPFunctor) x := rfl

end erasePUnit

end FreeM

end IPFunctor
