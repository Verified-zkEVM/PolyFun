/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Control.Monad.Basic

/-!
# Morphisms Between Monads

A morphism of monads is a family `m α → n α`, natural in `α`, preserving `pure`
and `bind`.  There are two useful presentations, and this file is deliberate
about which one it owns.

## Unbundled: Lean core

When the morphism is *canonical* for the pair `(m, n)` and should be found by
instance search, it belongs to core's lifting hierarchy: `MonadLift` /
`MonadLiftT` supply the map and `LawfulMonadLift` / `LawfulMonadLiftT`
(`Init/Control/Lawful/MonadLift/`) supply exactly the two laws above.  Core
carries instances for the standard transformer stack and a `liftM_*` simp set,
so nothing of that shape should be re-derived here.

## Bundled: this file

When the morphism is *data* — chosen at the call site, passed around, composed,
or mapped over — instance search is the wrong mechanism and a first-class arrow
is needed.  Core has no bundled form, so `MonadHom` (notation `m →ᵐ n`) is that
arrow, with `MonadHom.comp` (`∘ₘ`), `MonadHom.id`, and `StateT.mapHom` for
transporting one along a transformer.  `NatHom` is the underlying natural
transformation without the laws; `PFunctor.FreeM.liftMHom'` consumes it
directly.

`MonadHom.ofLift` is the bridge: any lawful lift induces a bundled morphism.
There is deliberately no converse instance — turning an arbitrary `MonadHom`
into a `MonadLift` would make instance search pick between morphisms that are
genuinely different maps.

## Why there is no `PureHom` / `BindHom` hierarchy

Mathlib splits `OneHom` from `MulHom` (and `ZeroHom` from `AddHom`) because those
component morphisms are useful independently, and because many richer morphism
types share their laws through the corresponding `HomClass` hierarchy.  The
old sketches in this file proposed the analogous `PureHom`, `BindHom`, and
`MonadHomClass`, but PolyFun, VCVio, and ArkLib have no consumer of either
partial morphism.  A `PureHom` would only preserve a pointing; a `BindHom`
would only become meaningful after choosing laws for a non-unital semimonad.
Neither abstraction exists in this stack.

The neighbouring upstream APIs make the same atomic choice.  Lean v4.34's
`LawfulMonadLift(T)` packages the `pure` and `bind` laws together, and mathlib's
categorical `MonadHom` packages compatibility with both the unit and
multiplication.  Batteries adds orthogonal preservation laws, such as
`LawfulAlternativeLift`, alongside a monad lift rather than splitting its two
monad laws.

A family-aware analogue of `FunLike` may become worthwhile once multiple
bundled morphism types need common lemmas.  The previous
`(α : Type u) → FunLike F (m α) (n α)` sketch did not provide one coherent
function-like view of the whole polymorphic family, and there is only one such
arrow type today.  The decision is therefore to keep `MonadHom` atomic and not
add speculative component structures or hom classes.  A real pointed-functor,
semimonad, or second bundled-morphism consumer should reopen that decision and
arrive with the corresponding laws and generic tests.

The unused `MonadEquiv` module is omitted for the same reason.  If a consumer
needs monad equivalences, the minimal design is two inverse `MonadHom`s, not a
parallel hierarchy of unused `PureEquiv` and `BindEquiv` structures.

Mathlib's `CategoryTheory.MonadHom` is a third presentation, at restricted
universes and in the categorical idiom; the `Type`-level form here is what the
free-monad and interaction layers actually consume.
-/

@[expose] public section

universe u v w x y

variable {m : Type u → Type v} {n : Type u → Type w}

/-- A `NatHom m n` for two functors `m` and `n` is a map `m α → n α` for each possible type `α`.
This is exactly an element of the category `m ⟶ n`, but that has more restricted universes -/
structure NatHom (m : Type u → Type v) (n : Type u → Type w) where
  /-- The underlying family of maps `m α → n α`, one for each type `α`. -/
  toFun : (α : Type u) → m α → n α

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance : CoeFun (NatHom m n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

/-- A `MonadHom m n` bundles a monad map `m ⟶ n` (represented as a `NatHom`) with proofs that
it respects the `bind` and `pure` operations in the underlying monad. -/
@[ext] structure MonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] extends NatHom m n where
  toFun_pure' {α} (x : α) : toFun α (pure x) = pure x
  toFun_bind' {α β} (x : m α) (y : α → m β) :
    toFun β (x >>= y) = toFun α x >>= fun x => toFun β (y x)

@[inherit_doc] infixr:25 " →ᵐ " => MonadHom

attribute [simp, grind =] MonadHom.toFun_pure' MonadHom.toFun_bind'

/-- `F mx` notation for `m →ᵐ n` applied to an element of `m α`, with implicit `α` inferred. -/
instance {m : Type u → Type v} [Pure m] [Bind m] {n : Type u → Type w} [Pure n] [Bind n] :
    CoeFun (m →ᵐ n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

namespace MonadHom

variable {m : Type u → Type v} [Monad m]
  {n : Type u → Type w} [Monad n]
  {n' : Type u → Type x} [Monad n']
  {n'' : Type u → Type y} [Monad n'']
  {α β γ : Type u}

/-- Extensionality for monad homomorphisms: two morphisms agreeing on every argument at every
type are equal. -/
@[ext] protected theorem ext' {F G : m →ᵐ n}
    (h : ∀ α (x : m α), F x = G x) : F = G :=
  MonadHom.ext (funext fun α => funext fun x => h α x)

@[grind =] lemma mmap_pure (F : m →ᵐ n) (x : α) : F (pure x) = pure x := by grind

@[grind =] lemma mmap_bind (F : m →ᵐ n) (mx : m α) (my : α → m β) :
    F (mx >>= my) = F mx >>= fun x => F (my x) := by grind

@[simp, grind =] lemma mmap_map [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (g : α → β) :
    F (g <$> x) = g <$> F x := by simp [monad_norm]

@[simp] lemma mmap_seq [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m (α → β)) (y : m α) :
    F (x <*> y) = F x <*> F y := by simp [seq_eq_bind_map, F.mmap_bind, F.mmap_map]

@[simp] lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (y : m β) :
    F (x <* y) = F x <* F y := by simp [seqLeft_eq]

@[simp] lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (y : m β) :
    F (x *> y) = F x *> F y := by simp [seqRight_eq]

/-- Construct a `MonadHom` from a lawful monad lift. -/
def ofLift (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] : m →ᵐ n where
  toFun _ mx := liftM mx
  toFun_pure' := by simp
  toFun_bind' := by simp

@[simp, grind =] lemma ofLift_apply [MonadLiftT m n] [LawfulMonadLiftT m n] {α : Type u} (x : m α) :
    ofLift m n x = liftM x := rfl

/-- The identity morphism between a monad and itself. -/
def id (m : Type u → Type v) [Monad m] : m →ᵐ m where
  toFun _ mx := mx
  toFun_pure' _ := by simp
  toFun_bind' _ _ := by simp

@[simp, grind =] lemma id_apply (mx : m α) : MonadHom.id m mx = mx := rfl

/-- Compose two `MonadHom`s together by applying them in sequence. -/
protected def comp (G : n →ᵐ n') (F : m →ᵐ n) : m →ᵐ n' where
  toFun _ := G.toFun _ ∘ F.toFun _
  toFun_pure' := by simp
  toFun_bind' := by simp

/-- Infix notation for composition of monad homomorphisms, `G ∘ₘ F`. -/
infixr:90 " ∘ₘ "  => MonadHom.comp

@[simp, grind =] lemma comp_apply (G : n →ᵐ n') (F : m →ᵐ n) (x : m α) :
    (G ∘ₘ F) x = G (F x) := rfl

@[simp, grind =] lemma comp_id (F : m →ᵐ n) : F.comp (MonadHom.id m) = F := rfl

@[simp, grind =] lemma id_comp (F : m →ᵐ n) : (MonadHom.id n).comp F = F := rfl

@[grind =] lemma comp_assoc (H : n' →ᵐ n'') (G : n →ᵐ n') (F : m →ᵐ n) :
    (H ∘ₘ G) ∘ₘ F = H ∘ₘ (G ∘ₘ F) := rfl

/-- `pure`/`return` lawfully embed the `Id` monad into any lawful monad. -/
protected def pure (m) [Monad m] [LawfulMonad m] : Id →ᵐ m where
  toFun _ mx := pure mx.run
  toFun_pure' x := by simp
  toFun_bind' mx my := by simp

@[simp, grind =] lemma pure_apply (m) [Monad m] [LawfulMonad m] (x : Id α) :
    MonadHom.pure m x = pure x.run := rfl

end MonadHom

namespace StateT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {σ α : Type u}

/-- `StateT σ` is functorial on monad morphisms: a monad morphism `φ : m →ᵐ n` lifts to a monad
morphism `StateT σ m →ᵐ StateT σ n`, acting on the underlying state-run and threading the state
unchanged. This transports the naturality of a fold (for example,
`FreeM.liftM_natural`) through a *stateful*
handler — the form a `StateT`-threaded semantic morphism (such as an evaluation-distribution map)
needs. -/
def mapHom (φ : m →ᵐ n) : StateT σ m →ᵐ StateT σ n where
  toFun _ x := StateT.mk fun s => φ (x.run s)
  toFun_pure' a := by ext s; simp
  toFun_bind' x y := by ext s; simp

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : StateT σ m α) (s : σ) :
    (StateT.mapHom φ x).run s = φ (x.run s) := rfl

omit [LawfulMonad m] in
@[simp] theorem mapHom_id :
    StateT.mapHom (σ := σ) (MonadHom.id m) = MonadHom.id (StateT σ m) := by
  apply MonadHom.ext'
  intro α x
  rfl

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

omit [LawfulMonad m] [LawfulMonad n] [LawfulMonad n'] in
@[simp] theorem mapHom_comp (G : n →ᵐ n') (F : m →ᵐ n) :
    StateT.mapHom (σ := σ) (G ∘ₘ F) =
      StateT.mapHom (σ := σ) G ∘ₘ StateT.mapHom (σ := σ) F := by
  apply MonadHom.ext'
  intro α x
  rfl

end StateT

namespace ReaderT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ρ α : Type u}

/-- `ReaderT ρ` is functorial on monad morphisms, acting under the environment. -/
def mapHom (φ : m →ᵐ n) : ReaderT ρ m →ᵐ ReaderT ρ n where
  toFun _ x := ReaderT.mk fun r => φ (x.run r)
  toFun_pure' a := by ext r; simp
  toFun_bind' x y := by ext r; simp

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : ReaderT ρ m α) (r : ρ) :
    (ReaderT.mapHom φ x).run r = φ (x.run r) := rfl

omit [LawfulMonad m] in
@[simp] theorem mapHom_id :
    ReaderT.mapHom (ρ := ρ) (MonadHom.id m) = MonadHom.id (ReaderT ρ m) := by
  apply MonadHom.ext'
  intro α x
  rfl

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

omit [LawfulMonad m] [LawfulMonad n] [LawfulMonad n'] in
@[simp] theorem mapHom_comp (G : n →ᵐ n') (F : m →ᵐ n) :
    ReaderT.mapHom (ρ := ρ) (G ∘ₘ F) =
      ReaderT.mapHom (ρ := ρ) G ∘ₘ ReaderT.mapHom (ρ := ρ) F := by
  apply MonadHom.ext'
  intro α x
  rfl

end ReaderT

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {α : Type u}

/-- `OptionT` is functorial on monad morphisms. The failure branch is preserved because a
monad morphism commutes with `pure`, so `none` is carried to `none`. -/
def mapHom (φ : m →ᵐ n) : OptionT m →ᵐ OptionT n where
  toFun _ x := OptionT.mk (φ x.run)
  toFun_pure' a := by
    apply OptionT.ext
    simp [OptionT.run_pure]
  toFun_bind' x y := by
    apply OptionT.ext
    have h : ∀ a : Option _, φ (a.elim (pure none) fun b => (y b).run)
        = a.elim (pure none) fun b => φ ((y b).run) := by
      intro a; cases a <;> simp
    simp only [OptionT.run_bind, OptionT.mk, Option.elimM, MonadHom.mmap_bind, h]
    rfl

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : OptionT m α) :
    (OptionT.mapHom φ x).run = φ x.run := rfl

omit [LawfulMonad m] in
@[simp] theorem mapHom_id :
    OptionT.mapHom (MonadHom.id m) = MonadHom.id (OptionT m) := by
  apply MonadHom.ext'
  intro α x
  rfl

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

omit [LawfulMonad m] [LawfulMonad n] [LawfulMonad n'] in
@[simp] theorem mapHom_comp (G : n →ᵐ n') (F : m →ᵐ n) :
    OptionT.mapHom (G ∘ₘ F) = OptionT.mapHom G ∘ₘ OptionT.mapHom F := by
  apply MonadHom.ext'
  intro α x
  rfl

end OptionT

namespace ExceptT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ε α : Type u}

/-- `ExceptT ε` is functorial on monad morphisms. As for `OptionT`, the error branch
survives because a monad morphism preserves `pure`. -/
def mapHom (φ : m →ᵐ n) : ExceptT ε m →ᵐ ExceptT ε n where
  toFun _ x := ExceptT.mk (φ x.run)
  toFun_pure' a := by
    apply ExceptT.ext
    simp [ExceptT.run_pure]
  toFun_bind' x y := by
    apply ExceptT.ext
    simp only [ExceptT.run_bind, ExceptT.mk, MonadHom.mmap_bind]
    exact bind_congr fun a => by cases a with
      | error e => simp
      | ok b => rfl

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : ExceptT ε m α) :
    (ExceptT.mapHom φ x).run = φ x.run := rfl

omit [LawfulMonad m] in
@[simp] theorem mapHom_id :
    ExceptT.mapHom (ε := ε) (MonadHom.id m) = MonadHom.id (ExceptT ε m) := by
  apply MonadHom.ext'
  intro α x
  rfl

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

omit [LawfulMonad m] [LawfulMonad n] [LawfulMonad n'] in
@[simp] theorem mapHom_comp (G : n →ᵐ n') (F : m →ᵐ n) :
    ExceptT.mapHom (ε := ε) (G ∘ₘ F) =
      ExceptT.mapHom (ε := ε) G ∘ₘ ExceptT.mapHom (ε := ε) F := by
  apply MonadHom.ext'
  intro α x
  rfl

end ExceptT
