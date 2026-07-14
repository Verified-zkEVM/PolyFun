/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Family

/-!
# State-Indexed Free Monad on an `IPFunctor.Endo`

`IPFunctor.FreeM P s α` is the *constant-family* specialization of the primitive
[`IPFunctor.IFreeM`](Family.lean): `FreeM P s α := IFreeM P (fun _ => α) s`. Pure return values
are allowed in any ambient state; the available head shapes at each `liftBind` are gated by the
current state, and the state for each continuation is determined by `P.src`.

Because the source index of each branch can depend on the chosen response, `FreeM P s α` is
**not** a `Monad` — its bind takes a state-polymorphic continuation. For a variant that tracks
the post-state statically and is therefore an `IndexedMonad` in the sense of Atkey, see
[`PolyFun/IPFunctor/Free/Indexed.lean`](Indexed.lean) (`FreeM₂`).

When the index type is `Unique`, the forgetful map `IPFunctor.FreeM.erase` collapses
`FreeM P s α` into `PFunctor.FreeM P.toPFunctor α`.
-/

@[expose] public section

universe uI uA uB v w

namespace IPFunctor

variable {I : Type uI}

/-- The state-indexed free monad on an endomorphic `IPFunctor`, as the constant-family
specialization of [`IPFunctor.IFreeM`](Family.lean). Different branches of a `FreeM P s α`
tree can end at different leaf states because `liftBind`'s source map `P.src` may produce different
results for different responses; all leaves carry values of the same type `α`.

Defined as a plain `def` (not `@[reducible]`) so that the `do`-notation elaborator's
reducible-transparency `whnf` does not unfold the head — keeping `IPFunctor.FreeM` visible as
the dispatch handle. The body is `IFreeM P (fun _ => α) s`, and at default transparency the
two are definitionally equal, which is what the equation-lemma `rfl` proofs in this file rely
on. -/
def FreeM (P : Endo.{uI, uA, uB} I) (s : I) (α : Type v) :
    Type (max uI uA uB (v + 1)) :=
  IFreeM P (fun _ => α) s

namespace FreeM

variable {P : Endo.{uI, uA, uB} I} {α β γ : Type v}

/-- A pure return value of `x`, available at any state `s`. Tagged `@[match_pattern]` so it
can appear in `match`/`induction` constructor-style patterns. Kept as a plain `def` so the
notation elaborator's `.reducible` `whnf` does not unfold the head. -/
@[match_pattern]
def pure (s : I) {α} (x : α) : FreeM P s α := IFreeM.pure (s := s) (X := fun _ => α) x

/-- Roll a value in the shapes available at `s` into a continuation, with the source index
for each branch determined by `P.src`. Tagged `@[match_pattern]`; plain `def` (same reasoning
as `FreeM.pure`). -/
@[match_pattern]
def liftBind (s : I) {α} (a : P.A s) (r : (b : P.B s a) → FreeM P (P.src s a b) α) :
    FreeM P s α :=
  IFreeM.liftBind (X := fun _ => α) a r

instance (s : I) : Pure (FreeM P s) where
  pure := FreeM.pure s

/-! ## Lifting -/

/-- Lift an object of the base `IPFunctor` at state `s` into the free monad. -/
@[always_inline, inline, reducible]
def liftObj (s : I) (x : P.Obj (fun _ => α) s) : FreeM P s α :=
  FreeM.liftBind s x.1 (fun b => FreeM.pure (P.src s x.1 b) (x.2 b))

/-- Lift a shape `a : P.A s` into the free monad, returning its response. -/
@[always_inline, inline, reducible]
def lift (s : I) (a : P.A s) : FreeM P s (P.B s a) :=
  FreeM.liftBind s a (fun b => FreeM.pure (P.src s a b) b)

/-! ## Bind

`FreeM.bind` is not the `Monad.bind` shape: the continuation `g` must accept the leaf state
explicitly because different branches of the tree end at different states. The implementation
is `IFreeM.bind` specialized to the constant family. -/

/-- State-polymorphic bind on `FreeM P`. Specializes `IFreeM.bind` to the constant family. -/
@[always_inline, inline]
protected def bind {s : I} (x : FreeM P s α) (g : (s' : I) → α → FreeM P s' β) :
    FreeM P s β :=
  IFreeM.bind x g

@[simp]
lemma bind_pure (s : I) (x : α) (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.pure (P := P) s x) g = g s x := rfl

@[simp]
lemma bind_liftBind (s : I) (x : P.A s) (r : (b : P.B s x) → FreeM P (P.src s x b) α)
    (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.liftBind s x r) g = FreeM.liftBind s x (fun b => FreeM.bind (r b) g) := rfl

@[simp]
lemma bind_liftObj (s : I) (x : P.Obj (fun _ => α) s) (g : (s' : I) → α → FreeM P s' β) :
    FreeM.bind (FreeM.liftObj s x) g =
      FreeM.liftBind s x.1 (fun b => g (P.src s x.1 b) (x.2 b)) := rfl

@[simp]
lemma bind_lift {β : Type uB} (s : I) (a : P.A s)
    (g : (s' : I) → P.B s a → FreeM P s' β) :
    FreeM.bind (FreeM.lift s a) g =
      FreeM.liftBind s a (fun b => g (P.src s a b) b) := rfl

/-! ## Specialized bind under deterministic transitions

When `P` has [`DeterministicTransitions`](../Basic.lean), a single `lift s a` step lands at
a single concrete source index `det.next s a`, and `FreeM.bind` can be specialized to a
non-polymorphic continuation. -/

/-- Specialized bind for a single `lift`-style step under `DeterministicTransitions`. The
continuation receives the response `b` at the *concrete* source index `det.next s a` (no
universal quantification over leaf states), unlike the general `FreeM.bind`. -/
@[always_inline, inline]
def bindLiftA [det : IPFunctor.DeterministicTransitions P]
    {s : I} (a : P.A s) (g : P.B s a → FreeM P (det.next s a) β) :
    FreeM P s β :=
  FreeM.liftBind s a (fun b => (det.spec s a b).symm ▸ g b)

@[simp]
lemma bindLiftA_eq [det : IPFunctor.DeterministicTransitions P]
    {s : I} (a : P.A s) (g : P.B s a → FreeM P (det.next s a) β) :
    bindLiftA a g = FreeM.liftBind s a (fun b => (det.spec s a b).symm ▸ g b) :=
  rfl

/-! ## Injectivity -/

lemma pure_inj (s : I) (x y : α) :
    FreeM.pure (P := P) s x = FreeM.pure s y ↔ x = y :=
  IFreeM.pure_inj (P := P) (X := fun _ => α) (s := s) x y

@[simp]
lemma liftBind_inj (s : I) (x x' : P.A s)
    (r : (b : P.B s x) → FreeM P (P.src s x b) α)
    (r' : (b : P.B s x') → FreeM P (P.src s x' b) α) :
    FreeM.liftBind s x r = FreeM.liftBind s x' r' ↔ ∃ h : x = x', h ▸ r = r' :=
  IFreeM.liftBind_inj (P := P) (X := fun _ => α) (s := s) x x' r r'

/-! ## Functor / LawfulFunctor -/

/-- Functor map on `FreeM P s`. The state is unchanged because mapping only rewrites leaves;
the state argument tracks the current position. Specializes `IFreeM.imap` at the constant
family. -/
protected def map (s : I) (f : α → β) : FreeM P s α → FreeM P s β :=
  IFreeM.imap (fun _ => f)

@[simp]
lemma map_pure (s : I) (f : α → β) (x : α) :
    FreeM.map (P := P) s f (FreeM.pure s x) = FreeM.pure s (f x) := rfl

@[simp]
lemma map_liftBind (s : I) (f : α → β) (x : P.A s)
    (r : (b : P.B s x) → FreeM P (P.src s x b) α) :
    FreeM.map s f (FreeM.liftBind s x r) =
      FreeM.liftBind s x (fun b => FreeM.map (P.src s x b) f (r b)) := rfl

lemma map_liftObj (s : I) (f : α → β) (x : P.Obj (fun _ => α) s) :
    FreeM.map s f (FreeM.liftObj s x) =
      FreeM.liftObj s ⟨x.1, fun b => f (x.2 b)⟩ := rfl

/-- While `FreeM P s` is not a `Monad` (because `liftBind`'s continuation can change state),
mapping leaves a tree at the same state, so the `Functor` instance is well-defined. -/
instance (s : I) : Functor (P.FreeM s) where
  map := FreeM.map s
  mapConst b x := FreeM.map s (fun _ => b) x

instance (s : I) : LawfulFunctor (P.FreeM s) where
  map_const := rfl
  id_map x := by
    induction x using IFreeM.inductionOn with
    | pure _ _ => rfl
    | liftBind _ _ _ ih => exact congrArg _ (funext ih)
  comp_map f g x := by
    induction x using IFreeM.inductionOn with
    | pure _ _ => rfl
    | liftBind _ _ _ ih => exact congrArg _ (funext (fun b => ih b))

/-! ## Induction principles -/

/-- Induction principle for `FreeM P` with a state-indexed motive (Prop-valued).
Wraps `IFreeM.inductionOn` at the constant family so downstream `induction x using
FreeM.inductionOn` calls continue to work. -/
@[elab_as_elim]
protected theorem inductionOn {C : ∀ s, FreeM P s α → Prop}
    (pure : ∀ s x, C s (FreeM.pure s x))
    (liftBind : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.src s x b) α),
      (∀ b, C (P.src s x b) (r b)) → C s (FreeM.liftBind s x r))
    {s : I} (oa : FreeM P s α) : C s oa :=
  IFreeM.inductionOn (C := C) pure liftBind oa

/-- Dependent recursor (`Type*`-valued) for `FreeM P` with state-indexed motive. -/
@[elab_as_elim]
protected def construct {C : ∀ s, FreeM P s α → Type*}
    (pure : ∀ s (x : α), C s (FreeM.pure s x))
    (liftBind : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.src s x b) α),
      (∀ b, C (P.src s x b) (r b)) → C s (FreeM.liftBind s x r))
    {s : I} (oa : FreeM P s α) : C s oa :=
  IFreeM.construct (C := C) pure liftBind oa

section construct

variable {C : ∀ s, FreeM P s α → Type*}
  (h_pure : ∀ s (x : α), C s (FreeM.pure s x))
  (h_liftBind : ∀ s (x : P.A s) (r : (b : P.B s x) → FreeM P (P.src s x b) α),
      (∀ b, C (P.src s x b) (r b)) → C s (FreeM.liftBind s x r))

@[simp]
lemma construct_pure (s : I) (x : α) :
    FreeM.construct h_pure h_liftBind (FreeM.pure (P := P) s x) = h_pure s x := rfl

@[simp]
lemma construct_liftBind (s : I) (x : P.A s) (r : (b : P.B s x) → FreeM P (P.src s x b) α) :
    (FreeM.construct h_pure h_liftBind (FreeM.liftBind s x r) : C s (FreeM.liftBind s x r)) =
      h_liftBind s x r (fun b => FreeM.construct h_pure h_liftBind (r b)) := rfl

@[simp]
lemma construct_liftObj (s : I) (x : P.Obj (fun _ => α) s) :
    (FreeM.construct h_pure h_liftBind (FreeM.liftObj s x) : C s (FreeM.liftObj s x)) =
      h_liftBind s x.1 (fun b => FreeM.pure (P.src s x.1 b) (x.2 b))
        (fun b => h_pure (P.src s x.1 b) (x.2 b)) := rfl

end construct

/-! ## `mapM`: interpreting `FreeM` into a monad

The responses `P.B s a` live in `Type uB`, so the target monad `m` is constrained to
`Type uB → Type w` and the value type `α` to `Type uB`. -/

section mapM

variable {m : Type uB → Type w} {α β : Type uB}

/-- Interpret a `FreeM P` into an arbitrary monad `m`, given for each state `s` and shape
`a : P.A s` a way to produce a response `m (P.B s a)`. The leaf state is erased on the
target side. Wraps `IFreeM.mapM` with the trivial leaf interpretation. -/
protected def mapM [Pure m] [Bind m] (h : (s : I) → (a : P.A s) → m (P.B s a))
    {s : I} (x : FreeM P s α) : m α :=
  IFreeM.mapM h (fun _ a => Pure.pure a) x

variable [Monad m] (h : (s : I) → (a : P.A s) → m (P.B s a))

@[simp]
lemma mapM_pure (s : I) (x : α) :
    (FreeM.pure (P := P) s x).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_pure' (s : I) (x : α) :
    (Pure.pure x : FreeM P s α).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_liftBind (s : I) (a : P.A s) (r : (b : P.B s a) → FreeM P (P.src s a b) α) :
    (FreeM.liftBind s a r).mapM h = h s a >>= fun b => (r b).mapM h := rfl

lemma mapM_liftObj [LawfulMonad m] (s : I) (x : P.Obj (fun _ => α) s) :
    (FreeM.liftObj s x).mapM h = h s x.1 >>= fun b => Pure.pure (x.2 b) := by
  simp [FreeM.mapM, IFreeM.mapM]

variable [LawfulMonad m]

lemma mapM_lift (s : I) (a : P.A s) :
    (FreeM.lift s a).mapM h = h s a := by
  simp [FreeM.mapM, IFreeM.mapM]

@[simp]
lemma mapM_map (s : I) (x : FreeM P s α) (f : α → β) :
    (f <$> x).mapM h = f <$> x.mapM h := by
  change (FreeM.map s f x).mapM h = f <$> x.mapM h
  induction x using IFreeM.inductionOn with
  | pure _ _ => simp [FreeM.map, FreeM.mapM, IFreeM.imap, IFreeM.mapM]
  | liftBind _ _ _ ih =>
    simp only [FreeM.map, IFreeM.imap, FreeM.mapM, IFreeM.mapM, map_bind]
    congr 1
    funext b
    exact ih b

end mapM

/-! ## Forgetful map to `PFunctor.FreeM`

When the index type has at most one element, the state information carries no content and an
`IPFunctor.Endo` collapses to a `PFunctor`. We provide a forgetful map `erase` from
`FreeM P s α` to `PFunctor.FreeM P.toPFunctor α` (at any `s : I`). The reverse direction would
require transport gymnastics through `P.src`'s data-dependent source index; we do not provide
it.

For a variant that works on *any* index type by Σ-bundling the state into each position,
see `toSigmaFreeM` below. -/

section erase

variable [Unique I]

/-- Remove all indexing information from a `FreeM` to obtain a `PFunctor.FreeM`, when the
index type is `Unique`. Defined via `IFreeM.construct` to sidestep the equation compiler's
difficulty matching against reducible-`def` wrappers; the `pure`/`liftBind` simp lemmas below are
each `rfl` through the `IFreeM.construct_pure`/`construct_liftBind` reductions. -/
def erase (P : Endo I) (s : I) {α : Type v} (x : P.FreeM s α) :
    P.toPFunctor.FreeM α :=
  IFreeM.construct (P := P) (X := fun _ => α)
    (C := fun _ _ => P.toPFunctor.FreeM α)
    (fun _ a => PFunctor.FreeM.pure a)
    (fun s' a _ ih =>
      PFunctor.FreeM.liftBind
        (show P.A default from Unique.eq_default s' ▸ a)
        (fun b => ih (Unique.eq_default s' ▸ b)))
    (s := s) x

@[simp]
lemma erase_pure (P : Endo I) (s : I) (x : α) :
    erase P s (FreeM.pure s x) = PFunctor.FreeM.pure x := rfl

end erase

/-! ### `PUnit`-specialized `erase` simp lemmas

When the index type is literally `PUnit`, the `Unique.eq_default` transports collapse
definitionally and simp can fire cleanly. These specializations cover the practically common
case where one wants to use `FreeM` as a state-aware wrapper over `PFunctor.FreeM` without
any actual state content. -/

section erasePUnit

variable {Q : Endo PUnit} {α : Type v}

@[simp]
lemma erase_punit_pure (x : α) :
    erase Q PUnit.unit (FreeM.pure PUnit.unit x : Q.FreeM PUnit.unit α) =
      PFunctor.FreeM.pure x := rfl

@[simp]
lemma erase_punit_liftBind (x : Q.A PUnit.unit)
    (r : (b : Q.B PUnit.unit x) → Q.FreeM (Q.src PUnit.unit x b) α) :
    erase Q PUnit.unit (FreeM.liftBind PUnit.unit x r) =
      PFunctor.FreeM.liftBind x (fun b => erase Q (Q.src PUnit.unit x b) (r b)) := rfl

lemma erase_punit_liftObj (x : Q.Obj (fun _ => α) PUnit.unit) :
    erase Q PUnit.unit (FreeM.liftObj PUnit.unit x) =
      x.2 <$> PFunctor.FreeM.lift (P := Q.toPFunctor) x.1 := rfl

lemma erase_punit_lift (a : Q.A PUnit.unit) :
    erase Q PUnit.unit (FreeM.lift PUnit.unit a) =
      PFunctor.FreeM.lift (P := Q.toPFunctor) a := rfl

end erasePUnit

/-! ## Σ-bundled forgetful map

`toSigmaFreeM` is the unrestricted analog of `erase`: it converts a `FreeM P s α` into a plain
`PFunctor.FreeM` over the Σ-bundled `P.sigmaPFunctor`, with the originating state recorded in
each position. No `[Unique I]` assumption is needed, but the target's positions live in
`Σ s : I, P.A s` rather than the flat `P.A default`.

Specializes `IFreeM.toSigmaFreeM` at the constant family and post-composes with
`PFunctor.FreeM.map Sigma.snd` to drop the leaf-state component from leaves. -/

section toSigmaFreeM

/-- Forget the state-indexing on each step by Σ-bundling the originating state into the
position, yielding a `PFunctor.FreeM` over `P.sigmaPFunctor`. Works for any index type.
Defined via `IFreeM.construct` so the simp lemmas below reduce by `rfl`. -/
def toSigmaFreeM (P : Endo I) {s : I} {α : Type v} (x : P.FreeM s α) :
    P.sigmaPFunctor.FreeM α :=
  IFreeM.construct (P := P) (X := fun _ => α)
    (C := fun _ _ => P.sigmaPFunctor.FreeM α)
    (fun _ a => PFunctor.FreeM.pure a)
    (fun s' a _ ih => PFunctor.FreeM.liftBind (⟨s', a⟩ : P.sigmaPFunctor.A) ih)
    x

@[simp]
lemma toSigmaFreeM_pure (P : Endo I) (s : I) (x : α) :
    toSigmaFreeM P (FreeM.pure s x) = PFunctor.FreeM.pure x := rfl

@[simp]
lemma toSigmaFreeM_liftBind (P : Endo I) (s : I) (a : P.A s)
    (r : (b : P.B s a) → P.FreeM (P.src s a b) α) :
    toSigmaFreeM P (FreeM.liftBind s a r) =
      PFunctor.FreeM.liftBind (⟨s, a⟩ : P.sigmaPFunctor.A)
        (fun b => toSigmaFreeM P (r b)) := rfl

lemma toSigmaFreeM_liftObj (P : Endo I) (s : I) (x : P.Obj (fun _ => α) s) :
    toSigmaFreeM P (FreeM.liftObj s x) =
      x.2 <$> PFunctor.FreeM.lift (P := P.sigmaPFunctor) ⟨s, x.1⟩ := rfl

lemma toSigmaFreeM_lift (P : Endo I) (s : I) (a : P.A s) :
    toSigmaFreeM P (FreeM.lift s a) =
      PFunctor.FreeM.lift (P := P.sigmaPFunctor) ⟨s, a⟩ := rfl

end toSigmaFreeM

end FreeM

end IPFunctor
