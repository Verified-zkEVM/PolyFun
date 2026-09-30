/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Iter

/-!
# Iteration through monad transformers

A state, reader, exception, or option transformer over an iterative monad is iterative: the
loop runs in the base monad with the transformer's data threaded through the loop state
(`StateT`), fixed for the whole loop (`ReaderT`), or turned into an early exit (`ExceptT`,
`OptionT`). These are Rocq's `MonadIter_stateT`, `MonadIter_readerT`, `MonadIter_eitherT`, and
`MonadIter_optionT` (`theories/Basics/Basics.v`); over `ITree F` they make
`StateT σ (ITree F)`, `ReaderT ρ (ITree F)`, `ExceptT ε (ITree F)`, and `OptionT (ITree F)`
iterative.

The base loop bodies are named (`StateT.stateBody`, `ExceptT.exceptBody`,
`OptionT.optionBody`), and the `run_iterM` equations, which hold by definition, state each loop
through them. `StateT` and `ReaderT` are lawful whenever the base is, with the base equivalence
taken pointwise in the state or environment; the exception and option transformers carry no
`LawfulMonadIter` instance.
-/

@[expose] public section

universe u v

/-! ## State -/

namespace StateT

variable {m : Type u → Type v} {σ : Type u} [Monad m]

/-- A state-monadic loop body paired with the state: the body of the base loop that
`StateT.instMonadIter` runs. -/
def stateBody {α β γ : Type u} (f : β → StateT σ m (γ ⊕ α)) (p : β × σ) :
    m ((γ × σ) ⊕ (α × σ)) :=
  (fun q => Sum.map (·, q.2) (·, q.2) q.1) <$> (f p.1).run p.2

/-- Run the loop in the base monad, threading the state through the loop state. -/
instance instMonadIter [MonadIter m] : MonadIter (StateT σ m) where
  iterM f init := fun s => iterM (stateBody f) (init, s)

@[simp] theorem run_iterM [MonadIter m] {α β : Type u} (f : β → StateT σ m (β ⊕ α)) (init : β)
    (s : σ) : (iterM f init).run s = iterM (stateBody f) (init, s) :=
  rfl

end StateT

/-! ## Reader -/

namespace ReaderT

variable {m : Type u → Type v} {ρ : Type u}

/-- Run the loop in the base monad with the environment fixed. -/
instance instMonadIter [MonadIter m] : MonadIter (ReaderT ρ m) where
  iterM f init := fun r => iterM (fun b => (f b).run r) init

@[simp] theorem run_iterM [MonadIter m] {α β : Type u} (f : β → ReaderT ρ m (β ⊕ α)) (init : β)
    (r : ρ) :
    (iterM f init).run r = iterM (fun b => (f b).run r) init :=
  rfl

end ReaderT

/-! ## Exceptions -/

namespace ExceptT

variable {m : Type u → Type v} {ε : Type u} [Monad m]

/-- An exception-monadic loop body as the body of the base loop that `ExceptT.instMonadIter`
runs: an exception ends the loop with that exception. -/
def exceptBody {α β : Type u} (f : β → ExceptT ε m (β ⊕ α)) (b : β) : m (β ⊕ Except ε α) :=
  (fun
    | .error e => .inr (.error e)
    | .ok (.inl next) => .inl next
    | .ok (.inr result) => .inr (.ok result)) <$> (f b).run

/-- Run the loop in the base monad; an exception ends the loop with that exception. -/
instance instMonadIter [MonadIter m] : MonadIter (ExceptT ε m) where
  iterM f init := ExceptT.mk <| iterM (exceptBody f) init

@[simp] theorem run_iterM [MonadIter m] {α β : Type u} (f : β → ExceptT ε m (β ⊕ α)) (init : β) :
    (iterM f init).run = iterM (exceptBody f) init :=
  rfl

end ExceptT

/-! ## Option -/

namespace OptionT

variable {m : Type u → Type v} [Monad m]

/-- An option-monadic loop body as the body of the base loop that `OptionT.instMonadIter` runs:
failure ends the loop with `none`. -/
def optionBody {α β : Type u} (f : β → OptionT m (β ⊕ α)) (b : β) : m (β ⊕ Option α) :=
  (fun
    | none => .inr none
    | some (.inl next) => .inl next
    | some (.inr result) => .inr (some result)) <$> (f b).run

/-- Run the loop in the base monad; failure ends the loop with `none`. -/
instance instMonadIter [MonadIter m] : MonadIter (OptionT m) where
  iterM f init := OptionT.mk <| iterM (optionBody f) init

@[simp] theorem run_iterM [MonadIter m] {α β : Type u} (f : β → OptionT m (β ⊕ α)) (init : β) :
    (iterM f init).run = iterM (optionBody f) init :=
  rfl

end OptionT

/-! ## Lawfulness

Both instances take the base equivalence pointwise in the environment or state. Each law is the
base law at the run bodies, followed by an equality in the base monad that reassociates the
`match` under `run`. The `ReaderT` equalities hold case by case on the loop step; the `StateT`
ones also use the base monad's laws. -/

namespace ReaderT

variable {m : Type u → Type v} {ρ : Type u} [Monad m] [LawfulMonad m] [MonadIter m]
  [LawfulMonadIter m]

open LawfulMonadIter in
instance instLawfulMonadIter : LawfulMonadIter (ReaderT ρ m) where
  Eqv x y := ∀ r, Eqv (x.run r) (y.run r)
  eqv_refl _ _ := eqv_refl _
  eqv_symm h r := eqv_symm (h r)
  eqv_trans h₁ h₂ r := eqv_trans (h₁ r) (h₂ r)
  bind_eqv hxy hfg r := bind_eqv (hxy r) fun a => hfg a r
  iter_eqv hfg init r := iter_eqv (fun b => hfg b r) init
  iter_unfold body init r :=
    eqv_trans (iter_unfold (fun b => (body b).run r) init)
      (eqv_of_eq (bind_congr fun v => by cases v <;> rfl))
  iter_natural body k init r :=
    eqv_trans (iter_natural (fun b => (body b).run r) (fun a => (k a).run r) init)
      (eqv_of_eq (congrArg (iterM · init) (funext fun b =>
        bind_congr fun v => by cases v <;> rfl)))
  iter_dinatural f g init r :=
    eqv_trans
      (eqv_of_eq (congrArg (iterM · init) (funext fun a =>
        bind_congr fun v => by cases v <;> rfl)))
      (eqv_trans (iter_dinatural (fun a => (f a).run r) (fun b => (g b).run r) init)
        (eqv_of_eq (bind_congr fun v => by
          cases v with
          | inl b =>
            exact congrArg (iterM · b) (funext fun b => bind_congr fun v => by cases v <;> rfl)
          | inr result => rfl)))
  iter_codiagonal body init r :=
    eqv_trans (iter_codiagonal (fun a => (body a).run r) init)
      (eqv_of_eq (congrArg (iterM · init) (funext fun a =>
        bind_congr fun v => by rcases v with _ | _ | _ <;> rfl)))
  iter_uniform φ f g h init r :=
    iter_uniform φ (fun b => (f b).run r) (fun c => (g c).run r) (fun b => h b r) init

end ReaderT

namespace StateT

variable {m : Type u → Type v} {σ : Type u} [Monad m] [LawfulMonad m]

/-- Unfolded form of the paired loop body. -/
theorem stateBody_eq {α β γ : Type u} (f : β → StateT σ m (γ ⊕ α)) (p : β × σ) :
    stateBody f p = (f p.1).run p.2 >>= fun q => pure (Sum.map (·, q.2) (·, q.2) q.1) :=
  map_eq_pure_bind _ _

variable [MonadIter m] [LawfulMonadIter m]

open LawfulMonadIter in
instance instLawfulMonadIter : LawfulMonadIter (StateT σ m) where
  Eqv x y := ∀ s, Eqv (x.run s) (y.run s)
  eqv_refl _ _ := eqv_refl _
  eqv_symm h s := eqv_symm (h s)
  eqv_trans h₁ h₂ s := eqv_trans (h₁ s) (h₂ s)
  bind_eqv hxy hfg s := by
    simp only [StateT.run_bind]
    exact bind_eqv (hxy s) fun p => hfg p.1 p.2
  iter_eqv {α β} {f g} hfg init s := by
    rw [run_iterM, run_iterM]
    exact iter_eqv (fun p => map_eqv _ (hfg p.1 p.2)) (init, s)
  iter_unfold body init s := by
    rw [run_iterM]
    refine eqv_trans (iter_unfold (stateBody body) (init, s)) (eqv_of_eq ?_)
    simp only [stateBody_eq, StateT.run_bind, bind_assoc, pure_bind]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | _, s'⟩ <;> simp only [Sum.map_inl, Sum.map_inr, StateT.run_pure,
      run_iterM]
  iter_natural body k init s := by
    rw [StateT.run_bind, run_iterM, run_iterM]
    refine eqv_trans (iter_natural (stateBody body) (fun q => (k q.1).run q.2) (init, s))
      (eqv_of_eq (congrArg (iterM · (init, s)) (funext fun p => ?_)))
    simp only [stateBody_eq, StateT.run_bind, bind_assoc, pure_bind]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | _, s'⟩ <;> simp only [Sum.map_inl, Sum.map_inr, StateT.run_pure,
      StateT.run_bind, bind_assoc, pure_bind]
  iter_dinatural f g init s := by
    rw [StateT.run_bind, run_iterM]
    refine eqv_trans (eqv_of_eq (congrArg (iterM · (init, s)) (funext fun p => ?_)))
      (eqv_trans (iter_dinatural (stateBody f) (stateBody g) (init, s)) (eqv_of_eq ?_))
    · simp only [stateBody_eq, StateT.run_bind, bind_assoc, pure_bind]
      refine bind_congr fun q => ?_
      rcases q with ⟨_ | _, s'⟩ <;> simp only [Sum.map_inl, Sum.map_inr, StateT.run_pure, pure_bind]
    · simp only [stateBody_eq, bind_assoc, pure_bind]
      refine bind_congr fun q => ?_
      rcases q with ⟨_ | _, s'⟩
      · rw [run_iterM]
        refine congrArg (iterM · _) (funext fun p => ?_)
        simp only [stateBody_eq, StateT.run_bind, bind_assoc]
        refine bind_congr fun q => ?_
        rcases q with ⟨_ | _, s'⟩ <;>
          simp only [Sum.map_inl, Sum.map_inr, StateT.run_pure, pure_bind]
      · simp only [Sum.map_inr, StateT.run_pure]
  iter_codiagonal {α β} body init s := by
    let inner : α × σ → m ((α × σ) ⊕ ((α × σ) ⊕ (β × σ))) := fun p =>
      (fun q => Sum.map (·, q.2) (Sum.map (·, q.2) (·, q.2)) q.1) <$> (body p.1).run p.2
    rw [run_iterM, run_iterM]
    refine eqv_trans (iter_eqv (fun p => ?_) (init, s))
      (eqv_trans (iter_codiagonal inner (init, s))
        (eqv_of_eq (congrArg (iterM · (init, s)) (funext fun p => ?_))))
    · change Eqv ((fun q : (α ⊕ β) × σ => Sum.map (·, q.2) (·, q.2) q.1) <$>
        iterM (stateBody body) (p.1, p.2)) (iterM inner p)
      rw [map_eq_pure_bind]
      refine eqv_trans (iter_natural (stateBody body) _ (p.1, p.2))
        (eqv_of_eq (congrArg (iterM · _) (funext fun r => ?_)))
      simp only [inner, stateBody_eq, map_eq_pure_bind, bind_assoc, pure_bind]
      refine bind_congr fun q => ?_
      rcases q with ⟨_ | _ | _, s'⟩ <;> simp
    · simp only [inner, stateBody_eq, StateT.run_bind, bind_assoc, pure_bind, map_eq_pure_bind]
      refine bind_congr fun q => ?_
      rcases q with ⟨_ | _ | _, s'⟩ <;> simp
  iter_uniform φ f g h init s := by
    rw [run_iterM, run_iterM]
    refine iter_uniform (Prod.map φ id) (stateBody f) (stateBody g) (fun p => ?_) (init, s)
    refine eqv_trans (map_eqv _ (h p.1 p.2)) (eqv_of_eq ?_)
    simp only [stateBody, StateT.run_map, Functor.map_map]
    exact congrArg (· <$> _) (funext fun q => by rcases q with ⟨_ | _, s'⟩ <;> rfl)

end StateT
