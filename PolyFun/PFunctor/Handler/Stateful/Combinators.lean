/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful
public import PolyFun.PFunctor.Handler.Sum

/-!
# Combinators for stateful handlers

Stateful handlers `Handler.Stateful m S P` (transparently `Handler (StateT S m) P`) compose in
the ways an effect stack composes:

* `mapBase` interprets the base free monad of a stateful handler through an outer handler, so a
  handler answering in `StateT S (FreeM Q)` becomes one answering in `StateT S m`;
* `parallel` runs two stateful handlers on the two summands of `P + Q` with a product state;
* `pi` runs an indexed family of stateful handlers on `PFunctor.sigma P` with a dependent
  product state, updating one component per request;
* `flatten` reassociates a stateful handler over a stateful base into one product state;
* `extend` and `extendLeft` add a passive auxiliary state component, and `fixSnd` projects one
  away.

The run laws relate `Stateful.run` through each combinator to the runs of its parts. Their
common core is `run_map_eq_of_apply_map_eq`: a state projection that commutes with every
single request commutes with every run. Support-based invariant variants (a projection that
only agrees on reachable states) belong to the layer that supplies the support semantics.
-/

@[expose] public section

universe u v uA uA'

namespace PFunctor

namespace Handler

namespace Stateful

variable {m : Type u → Type v} {S S₁ S₂ T : Type u}
variable {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}

/-! ### State projections -/

/-- A state projection that commutes with every request commutes with every run: if answering
`a` from `s` under `h₁` and then projecting the state equals answering under `h₂` from
`proj s`, the same holds for whole programs. -/
theorem run_map_eq_of_apply_map_eq [Monad m] [LawfulMonad m]
    (h₁ : Stateful m S₁ P) (h₂ : Stateful m S₂ P) (proj : S₁ → S₂)
    (hproj : ∀ a s, Prod.map _root_.id proj <$> (h₁ a).run s = (h₂ a).run (proj s)) {α : Type u} :
    ∀ (x : FreeM P α) (s : S₁), Prod.map _root_.id proj <$> h₁.run x s = h₂.run x (proj s)
  | .pure a, s => by simp
  | .liftBind a k, s => by
    rw [run_liftBind, run_liftBind, map_bind, ← hproj a s, bind_map_left]
    exact bind_congr fun r => run_map_eq_of_apply_map_eq h₁ h₂ proj hproj (k r.1) r.2

/-- The value-only form of `run_map_eq_of_apply_map_eq`. -/
theorem map_fst_run_eq_of_apply_map_eq [Monad m] [LawfulMonad m]
    (h₁ : Stateful m S₁ P) (h₂ : Stateful m S₂ P) (proj : S₁ → S₂)
    (hproj : ∀ a s, Prod.map _root_.id proj <$> (h₁ a).run s = (h₂ a).run (proj s)) {α : Type u}
    (x : FreeM P α) (s : S₁) :
    Prod.fst <$> h₁.run x s = Prod.fst <$> h₂.run x (proj s) := by
  rw [← run_map_eq_of_apply_map_eq h₁ h₂ proj hproj x s, Functor.map_map]
  rfl

/-- A stateful handler over the same interface whose answers, ignoring the state, are the
requests themselves leaves every program's value unchanged. -/
theorem map_fst_run_eq_self (h : Stateful (FreeM P) S P)
    (hh : ∀ a s, Prod.fst <$> (h a).run s = FreeM.lift a) {α : Type u} :
    ∀ (x : FreeM P α) (s : S), Prod.fst <$> h.run x s = x
  | .pure a, s => by simp
  | .liftBind a k, s => by
    rw [run_liftBind, map_bind, FreeM.liftBind_eq, FreeM.bind_eq_bind, ← hh a s,
      bind_map_left]
    exact bind_congr fun r => map_fst_run_eq_self h hh (k r.1) r.2

/-! ### Changing the base monad -/

/-- Interpret the base free monad of a stateful handler through an outer handler. -/
def mapBase [Monad m] (outer : Handler m Q) (inner : Stateful (FreeM Q) S P) :
    Stateful m S P :=
  fun a => StateT.mk fun s => ((inner a).run s).liftM outer

@[simp] theorem mapBase_apply_run [Monad m] (outer : Handler m Q)
    (inner : Stateful (FreeM Q) S P) (a : P.A) (s : S) :
    (mapBase outer inner a).run s = ((inner a).run s).liftM outer := rfl

/-- Running a program through the inner handler and interpreting the result through the outer
handler is running it through the composite. -/
theorem run_mapBase [Monad m] [LawfulMonad m] (outer : Handler m Q)
    (inner : Stateful (FreeM Q) S P) {α : Type u} :
    ∀ (x : FreeM P α) (s : S), (inner.run x s).liftM outer = (mapBase outer inner).run x s
  | .pure a, s => by simp
  | .liftBind a k, s => by
    rw [run_liftBind, run_liftBind, FreeM.liftM_bind, mapBase_apply_run]
    exact bind_congr fun r => run_mapBase outer inner (k r.1) r.2

/-! ### Product states -/

/-- Run two stateful handlers on the two summands of `P + Q`, each on its own component of a
product state. -/
def parallel [Functor m] (f : Stateful m S P) (g : Stateful m T Q) :
    Stateful m (S × T) (P + Q : PFunctor.{max uA uA', u})
  | .inl a => StateT.mk fun st => Prod.map _root_.id (·, st.2) <$> (f a).run st.1
  | .inr b => StateT.mk fun st => Prod.map _root_.id (st.1, ·) <$> (g b).run st.2

@[simp] theorem parallel_inl_run [Functor m] (f : Stateful m S P) (g : Stateful m T Q)
    (a : P.A) (st : S × T) :
    (parallel f g (.inl a)).run st = Prod.map _root_.id (·, st.2) <$> (f a).run st.1 := rfl

@[simp] theorem parallel_inr_run [Functor m] (f : Stateful m S P) (g : Stateful m T Q)
    (b : Q.A) (st : S × T) :
    (parallel f g (.inr b)).run st = Prod.map _root_.id (st.1, ·) <$> (g b).run st.2 := rfl

/-- Run an indexed family of stateful handlers on the indexed sum, each member on its own
component of a dependent product state. -/
def pi {I : Type u} [DecidableEq I] [Functor m] {P : I → PFunctor.{uA, u}} {S : I → Type u}
    (f : (i : I) → Stateful m (S i) (P i)) :
    Stateful m ((i : I) → S i) (PFunctor.sigma P) :=
  fun x => StateT.mk fun s =>
    Prod.map _root_.id (Function.update s (PFunctor.sigma.fst x)) <$>
      (f (PFunctor.sigma.fst x) (PFunctor.sigma.snd x)).run (s (PFunctor.sigma.fst x))

@[simp] theorem pi_mk_run {I : Type u} [DecidableEq I] [Functor m] {P : I → PFunctor.{uA, u}}
    {S : I → Type u} (f : (i : I) → Stateful m (S i) (P i)) (i : I) (a : (P i).A)
    (s : (i : I) → S i) :
    (pi f (PFunctor.sigma.mk i a)).run s =
      Prod.map _root_.id (Function.update s i) <$> (f i a).run (s i) :=
  rfl

/-- Reassociate a stateful handler over a stateful base into one product state; the outer state
is the first component. -/
def flatten [Monad m] (h : Stateful (StateT T m) S P) : Stateful m (S × T) P :=
  fun a => StateT.mk fun st =>
    (fun r : (P.B a × S) × T => (r.1.1, (r.1.2, r.2))) <$> ((h a).run st.1).run st.2

@[simp] theorem flatten_apply_run [Monad m] (h : Stateful (StateT T m) S P) (a : P.A)
    (st : S × T) :
    (flatten h a).run st =
      (fun r : (P.B a × S) × T => (r.1.1, (r.1.2, r.2))) <$> ((h a).run st.1).run st.2 := rfl

/-- Flattening a handler that ignores the outer state runs the inner handler and reinserts the
outer state. -/
theorem flatten_lift_apply_run [Monad m] [LawfulMonad m] (h : Stateful m T P) (a : P.A)
    (st : S × T) :
    (flatten (Stateful.lift (S := S) h) a).run st =
      (fun r : P.B a × T => (r.1, (st.1, r.2))) <$> (h a).run st.2 := by
  simp [Stateful.lift, StateT.run_lift, Functor.map_map]

/-- Running a program through a flattened handler is running it through the nested handler
and reassociating the final states. -/
theorem run_flatten [Monad m] [LawfulMonad m] (h : Stateful (StateT T m) S P) {α : Type u} :
    ∀ (x : FreeM P α) (st : S × T),
      (flatten h).run x st =
        (fun r : (α × S) × T => (r.1.1, (r.1.2, r.2))) <$> ((h.run x st.1).run st.2)
  | .pure a, st => by simp
  | .liftBind a k, st => by
    rw [run_liftBind, run_liftBind, flatten_apply_run, StateT.run_bind, map_bind, bind_map_left]
    exact bind_congr fun r => run_flatten h (k r.1.1) (r.1.2, r.2)

/-! ### Auxiliary state components -/

/-- Extend a stateful handler with a passive auxiliary component on the right. The update may
inspect the request, the previous state, the answer, the next state, and the previous
auxiliary value. -/
def extend [Monad m] (h : Stateful m S P) (aux : (a : P.A) → S → P.B a → S → T → T) :
    Stateful m (S × T) P :=
  fun a => StateT.mk fun st => do
    let r ← (h a).run st.1
    pure (r.1, (r.2, aux a st.1 r.1 r.2 st.2))

@[simp] theorem extend_apply_run [Monad m] (h : Stateful m S P)
    (aux : (a : P.A) → S → P.B a → S → T → T) (a : P.A) (st : S × T) :
    (extend h aux a).run st =
      (h a).run st.1 >>= fun r => pure (r.1, (r.2, aux a st.1 r.1 r.2 st.2)) := rfl

/-- Extend a stateful handler with a passive auxiliary component on the left. -/
def extendLeft [Monad m] (h : Stateful m S P) (aux : (a : P.A) → S → P.B a → S → T → T) :
    Stateful m (T × S) P :=
  fun a => StateT.mk fun ts => do
    let r ← (h a).run ts.2
    pure (r.1, (aux a ts.2 r.1 r.2 ts.1, r.2))

@[simp] theorem extendLeft_apply_run [Monad m] (h : Stateful m S P)
    (aux : (a : P.A) → S → P.B a → S → T → T) (a : P.A) (ts : T × S) :
    (extendLeft h aux a).run ts =
      (h a).run ts.2 >>= fun r => pure (r.1, (aux a ts.2 r.1 r.2 ts.1, r.2)) := rfl

/-- The auxiliary component is passive: forgetting it after a run gives the base run. -/
theorem run_extend_map_fst [Monad m] [LawfulMonad m] (h : Stateful m S P)
    (aux : (a : P.A) → S → P.B a → S → T → T) {α : Type u} (x : FreeM P α) (s : S) (t : T) :
    Prod.map _root_.id Prod.fst <$> (extend h aux).run x (s, t) = h.run x s :=
  run_map_eq_of_apply_map_eq (extend h aux) h Prod.fst
    (fun a st => by simp [Functor.map_map]) x (s, t)

/-- The left auxiliary component is passive. -/
theorem run_extendLeft_map_snd [Monad m] [LawfulMonad m] (h : Stateful m S P)
    (aux : (a : P.A) → S → P.B a → S → T → T) {α : Type u} (x : FreeM P α) (s : S) (t : T) :
    Prod.map _root_.id Prod.snd <$> (extendLeft h aux).run x (t, s) = h.run x s :=
  run_map_eq_of_apply_map_eq (extendLeft h aux) h Prod.snd
    (fun a ts => by simp [Functor.map_map]) x (t, s)

/-- Fix the second component of a product state and project a stateful handler to the first. -/
def fixSnd [Functor m] (h : Stateful m (S × T) P) (t₀ : T) : Stateful m S P :=
  fun a => StateT.mk fun s => Prod.map _root_.id Prod.fst <$> (h a).run (s, t₀)

@[simp] theorem fixSnd_apply_run [Functor m] (h : Stateful m (S × T) P) (t₀ : T) (a : P.A)
    (s : S) :
    (fixSnd h t₀ a).run s = Prod.map _root_.id Prod.fst <$> (h a).run (s, t₀) := rfl

end Stateful

end Handler

end PFunctor
