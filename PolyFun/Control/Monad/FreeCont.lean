/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Control.Monad.Free
public import PolyFun.PFunctor.Free.Basic
public import Mathlib.Control.Monad.Cont
public import Mathlib

@[expose] public section

universe u v w y z

/-- Church-encoded freer monad transformer, expressed as interpreter for continuation.

When unfolded (recall that `ContT r m α = (α → m r) → m r`), it takes the form:
```
{r : Type u} → (handleEff : {x : Type z} → f x → (x → m r) → m r) → (handlePure : α → m r) → m r
```

Compare this to the inductive definition, which has two constructors:
- `pure : α → FreeMonad f α`
- `roll : f β → (β → FreeMonad f α) → FreeMonad f α`
-/
def FreeContT (f : Type z → Type y) (m : Type u → Type v) (α : Type w) :
    Type (max (u + 1) v w y (z + 1)) :=
  {r : Type u} → ({x : Type z} → f x → ContT r m x) → ContT r m α

/-- Church-encoded freer monad, expressed as interpreter for continuation.

When unfolded, it takes the form:
```
{r : Type u} → (handleEff : {x : Type z} → f x → (x → r) → r) → (handlePure : α → r) → r
```

Compare this to the inductive definition, which has two constructors:
- `pure : α → FreeMonad f α`
- `roll : f β → (β → FreeMonad f α) → FreeMonad f α` -/
def FreeContM (f : Type z → Type y) (α : Type w) : Type (max (u + 1) w y (z + 1)) :=
  FreeContT f Id.{u} α

/-- Church-encoded freer monad transformer from a polynomial functor.
Does not raise universe levels. -/
def PFunctor.FreeContT (P : PFunctor.{z, y}) (m : Type u → Type v) (α : Type w) :
    Type (max (u + 1) v w y z) :=
  {r : Type u} → ((a : P.A) → ContT r m (P.B a)) → ContT r m α

/-- Church-encoded freer monad from a polynomial functor. -/
def PFunctor.FreeContM (P : PFunctor.{z, y}) (α : Type w) : Type _ :=
  FreeContT P Id.{u} α

variable {f : Type z → Type y} {m : Type u → Type v} {α β : Type w}

namespace FreeContT

@[simp]
lemma def_eq : FreeContT f m α =
    ({r : Type u} → ({x : Type z} → f x → (x → m r) → m r) → (α → m r) → m r) := rfl

@[simp]
lemma FreeContM.def_eq : FreeContM.{u, w, y, z} f α =
    ({r : Type u} → ({x : Type z} → f x → (x → r) → r) → (α → r) → r) := rfl

inductive FreeM (f : Type v → Type w) (α : Type u) where
  | pure (a : α) : FreeM f α
  | roll {β : Type v} (x : f β) (k : β → FreeM f α) : FreeM f α

/-- `pure` just feeds the value to the pure continuation. -/
@[inline] def pure (a : α) : FreeContT f m α :=
  fun _ handlePure => handlePure a

/-- `bind` runs the first computation; when it produces a value, we run the second computation
    with the *same* effect handler and *same* final continuation. -/
@[inline] def bind (x : FreeContT f m α) (g : α → FreeContT f m β) :
    FreeContT f m β :=
  fun handleEff handlePure => x handleEff (fun a => g a handleEff handlePure)

/-- Lift a monadic computation to the free transformer monad, via sequencing with the pure
  continuation. -/
@[inline] def lift [Bind m] {α : Type u} (x : m α) : FreeContT f m α :=
  fun _ handlePure => x >>= handlePure

/-- `FreeContT f m` is a monad for arbitrary `f` and `m`. -/
instance instMonad : Monad (FreeContT f m) where
  pure := pure
  bind := bind

/-- `FreeContT f m` is a lawful monad for arbitrary `f` and `m`. -/
instance instLawfulMonad : LawfulMonad (FreeContT f m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intros; rfl)

/-- We can always lift a monadic computation to the free transformer monad. -/
instance instMonadLift [Bind m] : MonadLift m (FreeContT f m) where
  monadLift := lift

/-- The lift from `m` to `FreeContT f m` is a lawful monad lift, assuming `m` is a lawful monad. -/
instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (FreeContT f m) where
  monadLift_pure := by
    intro α a
    dsimp [instMonadLift, instMonad]
    funext r _ handlePure
    change ((Pure.pure a : m α) >>= handlePure) = handlePure a
    simp
  monadLift_bind := by
    intros α β ma g
    dsimp [instMonadLift, instMonad]
    funext r _ handlePure
    change (ma >>= g) >>= handlePure = ma >>= fun x => g x >>= handlePure
    exact LawfulMonad.bind_assoc (m := m) (x := ma) (f := g) (g := handlePure)

end FreeContT

/-- Convert free monads from inductive style to continuation-passing style. -/
def FreeMonad.toFreeContM : FreeMonad f α → FreeContM f α :=
  fun x => match x with
    | FreeMonad.pure a => fun _ handlePure => handlePure a
    | FreeMonad.roll x k => fun handleEff handlePure =>
      handleEff x (fun a => FreeMonad.toFreeContM (k a) handleEff handlePure)

/-- Convert free monads from continuation-passing style to inductive style. -/
def FreeContM.toFreeMonad : FreeContM f α → FreeMonad f α :=
  fun x => x FreeMonad.roll FreeMonad.pure

@[simp]
lemma FreeMonad.toFreeMonad_toFreeContM (x : FreeMonad f α) :
    FreeContM.toFreeMonad (FreeMonad.toFreeContM x) = x := by
  induction x with
    | pure a => rfl
    | roll x k ih =>
      dsimp [FreeMonad.toFreeContM, FreeContM.toFreeMonad]
      congr
      funext b
      exact ih b

/-- `FreeMonad.toFreeContM` is a section of `FreeContM.toFreeMonad`. -/
lemma FreeMonad.toFreeContM_leftInverse :
    Function.LeftInverse
      (fun x : FreeContM.{max (max y (z + 1)) w, w, y, z} f α => FreeContM.toFreeMonad x)
      (fun x : FreeMonad f α =>
        (FreeMonad.toFreeContM x : FreeContM.{max (max y (z + 1)) w, w, y, z} f α)) := by
  intro x
  exact FreeMonad.toFreeMonad_toFreeContM x

/-- The inductive-to-Church map is injective. -/
lemma FreeMonad.toFreeContM_injective :
    Function.Injective
      (fun x : FreeMonad f α =>
        (FreeMonad.toFreeContM x : FreeContM.{max (max y (z + 1)) w, w, y, z} f α)) :=
  (FreeMonad.toFreeContM_leftInverse (f := f) (α := α)).injective

/-- The Church-to-inductive map is surjective. -/
lemma FreeContM.toFreeMonad_surjective :
    Function.Surjective
      (fun x : FreeContM.{max (max y (z + 1)) w, w, y, z} f α => FreeContM.toFreeMonad x) :=
by
  intro x
  exact ⟨FreeMonad.toFreeContM x, FreeMonad.toFreeMonad_toFreeContM x⟩
