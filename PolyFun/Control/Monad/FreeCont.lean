/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Monad.Free
public import Mathlib.Control.Monad.Cont

/-!
# Continuation-passing free monad transformer

`FreeContT f m` is the Church / CPS encoding of the freer monad transformer
over an effect signature `f` and base monad `m`. It stores its universal
continuation-based eliminator rather than an inspectable syntax tree:

```lean
{r : Type u} →
  ({x : Type z} → f x → (x → m r) → m r) →
  (α → m r) → m r
```

The one-field structure keeps the CPS representation abstract enough for Lean
to recognize `FreeContT f m` as a monad application. `FreeContT.liftBind` and
`FreeContT.liftF` inject signature operations, while `MonadLift` injects base
monad computations. This makes the representation useful for direct
composition and interpretation; use `Cslib.FreeM` when programs must instead
be inspected or analyzed structurally.

Lean does not supply the parametricity principle needed to prove that every
inhabitant of this rank-2 type comes from inductive free syntax. Accordingly,
the conversions with `Cslib.FreeM` below form only an inductive-to-CPS-to-
inductive round trip, not an equivalence.
-/

@[expose] public section

universe u v w y z

/-- Church-encoded freer monad transformer.

An inhabitant interprets effect requests and pure results into `ContT r m` for
every result type `r`. Bind is therefore continuation composition and does not
traverse an intermediate syntax tree. -/
structure FreeContT (f : Type z → Type y) (m : Type u → Type v) (α : Type w) :
    Type (max (u + 1) v w y (z + 1)) where
  /-- Eliminate a Church-encoded computation with an effect handler and final
  continuation. -/
  run : {r : Type u} → ({x : Type z} → f x → ContT r m x) → ContT r m α

/-- Church-encoded freer monad, obtained by specializing the base monad to
`Id`. -/
abbrev FreeContM (f : Type z → Type y) (α : Type w) := FreeContT f Id.{u} α

namespace FreeContT

variable {f : Type z → Type y} {m : Type u → Type v} {α β : Type w}

/-- Church-encoded computations are equal when all their eliminations agree. -/
@[ext]
theorem ext {x y : FreeContT f m α}
    (h : ∀ (r : Type u) (handleEff : {x : Type z} → f x → ContT r m x)
      (handlePure : α → m r), x.run handleEff handlePure = y.run handleEff handlePure) :
    x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      congr
      funext r handleEff handlePure
      exact h r handleEff handlePure

/-- Feed a pure value directly to the final continuation. -/
@[inline]
def pure (a : α) : FreeContT f m α :=
  ⟨fun _ handlePure => handlePure a⟩

/-- Inject an effect request together with its continuation.

Unlike monadic bind, the request result and final result may live in different
universes. This mirrors `Cslib.FreeM.liftBind`. -/
@[inline]
def liftBind {ι : Type z} (op : f ι) (next : ι → FreeContT f m α) : FreeContT f m α :=
  ⟨fun handleEff handlePure =>
    handleEff op fun result => (next result).run handleEff handlePure⟩

/-- Inject one effect request into the Church-encoded transformer. -/
@[inline]
def liftF {ι : Type z} (op : f ι) : FreeContT f m ι :=
  ⟨fun handleEff handlePure => handleEff op handlePure⟩

/-- Sequence two Church-encoded computations by composing their final
continuations. -/
@[inline]
def bind (x : FreeContT f m α) (g : α → FreeContT f m β) : FreeContT f m β :=
  ⟨fun handleEff handlePure =>
    x.run handleEff fun a => (g a).run handleEff handlePure⟩

/-- Lift a base-monad computation by sequencing it with the final
continuation. -/
@[inline]
def lift [Bind m] {α : Type u} (x : m α) : FreeContT f m α :=
  ⟨fun _ handlePure => x >>= handlePure⟩

/-- `FreeContT f m` is a monad for arbitrary `f` and `m`. -/
instance instMonad : Monad (FreeContT f m) where
  pure := pure
  bind := bind

/-- `FreeContT f m` is a lawful monad for arbitrary `f` and `m`. -/
instance instLawfulMonad : LawfulMonad (FreeContT f m) := LawfulMonad.mk'
  (id_map := by intros; apply ext; intros; rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intros; rfl)

/-- Lift computations from the base monad into the Church-encoded
transformer. -/
instance instMonadLift [Bind m] : MonadLift m (FreeContT f m) where
  monadLift := lift

/-- Base-monad lifting preserves `pure` and `bind`. -/
instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (FreeContT f m) where
  monadLift_pure := by
    intro α a
    apply ext
    intro r handleEff handlePure
    change ((Pure.pure a : m α) >>= handlePure) = handlePure a
    simp
  monadLift_bind := by
    intro α β ma g
    apply ext
    intro r handleEff handlePure
    change (ma >>= g) >>= handlePure = ma >>= fun x => g x >>= handlePure
    exact LawfulMonad.bind_assoc (m := m) (x := ma) (f := g) (g := handlePure)

/-- In a common result universe, `liftBind` is effect injection followed by
monadic bind. -/
@[simp]
theorem liftBind_eq {ι β : Type z} (op : f ι) (next : ι → FreeContT f m β) :
    liftBind op next = bind (liftF op) next :=
  rfl

@[simp]
theorem run_pure {r : Type u} (a : α)
    (handleEff : {x : Type z} → f x → ContT r m x) (handlePure : α → m r) :
    (pure a : FreeContT f m α).run handleEff handlePure = handlePure a :=
  rfl

@[simp]
theorem run_liftBind {r : Type u} {ι : Type z} (op : f ι)
    (next : ι → FreeContT f m α) (handleEff : {x : Type z} → f x → ContT r m x)
    (handlePure : α → m r) :
    (liftBind op next).run handleEff handlePure =
      handleEff op fun result => (next result).run handleEff handlePure :=
  rfl

@[simp]
theorem run_liftF {r : Type u} {ι : Type z} (op : f ι)
    (handleEff : {x : Type z} → f x → ContT r m x) (handlePure : ι → m r) :
    (liftF op : FreeContT f m ι).run handleEff handlePure = handleEff op handlePure :=
  rfl

@[simp]
theorem run_bind {r : Type u} (x : FreeContT f m α) (g : α → FreeContT f m β)
    (handleEff : {x : Type z} → f x → ContT r m x) (handlePure : β → m r) :
    (x >>= g).run handleEff handlePure =
      x.run handleEff fun a => (g a).run handleEff handlePure :=
  rfl

@[simp]
theorem run_lift [Bind m] {r α : Type u} (x : m α)
    (handleEff : {x : Type z} → f x → ContT r m x) (handlePure : α → m r) :
    (lift x : FreeContT f m α).run handleEff handlePure = x >>= handlePure :=
  rfl

end FreeContT

variable {f : Type z → Type y} {α : Type w}

/-- Convert inductive free syntax to continuation-passing form. -/
def Cslib.FreeM.toFreeContM : Cslib.FreeM f α → FreeContM f α
  | .pure a => FreeContT.pure a
  | .liftBind op next =>
      FreeContT.liftBind op fun result => Cslib.FreeM.toFreeContM (next result)

/-- Reify a Church-encoded free monad into inductive `Cslib.FreeM` syntax. -/
def FreeContM.toFreeM : FreeContM f α → Cslib.FreeM f α :=
  fun x => x.run Cslib.FreeM.liftBind Cslib.FreeM.pure

@[simp]
theorem Cslib.FreeM.toFreeContM_pure (a : α) :
    Cslib.FreeM.toFreeContM (pure a : Cslib.FreeM f α) = FreeContT.pure a :=
  rfl

@[simp]
theorem Cslib.FreeM.toFreeContM_liftBind {ι : Type z} (op : f ι)
    (next : ι → Cslib.FreeM f α) :
    Cslib.FreeM.toFreeContM ((Cslib.FreeM.lift op).bind next) =
      FreeContT.liftBind op fun result => Cslib.FreeM.toFreeContM (next result) :=
  rfl

@[simp]
theorem FreeContM.toFreeM_pure (a : α) :
    FreeContM.toFreeM
        (FreeContT.pure a : FreeContM.{max (max y (z + 1)) w} f α) =
      Cslib.FreeM.pure a :=
  rfl

@[simp]
theorem FreeContM.toFreeM_liftBind {ι : Type z} (op : f ι)
    (next : ι → FreeContM.{max (max y (z + 1)) w} f α) :
    FreeContM.toFreeM (FreeContT.liftBind op next) =
      Cslib.FreeM.liftBind op fun result => FreeContM.toFreeM (next result) :=
  rfl

/-- Reifying inductive syntax after Church encoding recovers the original
tree. The reverse composite is intentionally not claimed without a
parametricity hypothesis. -/
@[simp]
theorem Cslib.FreeM.toFreeM_toFreeContM (x : Cslib.FreeM f α) :
    FreeContM.toFreeM (Cslib.FreeM.toFreeContM x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op next ih =>
      rw [← Cslib.FreeM.liftBind_eq]
      dsimp only [Cslib.FreeM.toFreeContM, FreeContM.toFreeM, FreeContT.liftBind]
      congr
      exact funext ih
