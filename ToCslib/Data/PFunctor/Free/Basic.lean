/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Extensions of the free monad on a polynomial functor

Additions to cslib's `PFunctor.FreeM` API staged for upstreaming: a case-analysis principle in
the same `(lift a).bind cont` normal form as cslib's induction principle, the functor equations
`map_pure` / `map_bind` together with their constructor spellings, the catamorphism `foldFreeM`
with its universal property (the polynomial counterpart of `Cslib.FreeM.foldFreeM`), handler
fusion `liftM_comp`, the identity fold `liftM_lift_eq_self`, and naturality of `liftM` along any
function that preserves `pure` and `bind` (`map_liftM`).

Every declaration lives in the upstream namespace `PFunctor.FreeM` and uses no vocabulary beyond
cslib's. A lemma that duplicates an open cslib pull request carries an `upstream:` comment naming
it and is deleted when that request lands.
-/

public section

universe u v w uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type*}

/-! ## Case analysis in simp normal form -/

/-- Case analysis on a free polynomial tree, presenting the node case as `(lift a).bind cont`:
the simp normal form that cslib's induction principle `FreeM.induction` also uses, so that
`cases x using FreeM.cases with | pure a => _ | lift_bind a cont => _` produces goals `simp` can
continue on without unfolding `liftBind`. -/
-- upstream: cslib#731 supplies a `cases_eliminator` for the W-type presentation.
protected def cases {motive : P.FreeM α → Sort u}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α), motive ((FreeM.lift a).bind cont)) :
    ∀ x, motive x
  | .pure a => pure a
  | .liftBind a cont => lift_bind a cont

/-! ## Bind and functor equations -/

/-- The monad `>>=` of `FreeM` is `FreeM.bind`, pointwise; the function-level form is
`bind_eq_bind`. -/
theorem bind_eq {α β : Type v} (x : P.FreeM α) (g : α → P.FreeM β) : x >>= g = x.bind g := rfl

-- upstream: cslib#716
@[simp]
theorem map_pure (f : α → β) (x : α) : map f (pure x : P.FreeM α) = pure (f x) := rfl

-- upstream: cslib#716
@[simp]
theorem map_bind (f : β → γ) (x : P.FreeM α) (cont : α → P.FreeM β) :
    map f (x.bind cont) = x.bind fun a => (cont a).map f := by
  simp_rw [← bind_pure_comp, FreeM.bind_assoc]

/-- Mapping through a node maps every continuation, in constructor spelling. -/
theorem map_liftBind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f (FreeM.liftBind a cont) = FreeM.liftBind a fun b => map f (cont b) :=
  rfl

/-- Mapping through a node maps every continuation, in simp normal form. -/
theorem map_lift_bind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f ((FreeM.lift a).bind cont) = (FreeM.lift a).bind fun b => map f (cont b) :=
  rfl

/-! ## The catamorphism

`FreeM P α` is the initial algebra of `β ↦ α ⊕ Σ a, (P.B a → β)`. An algebra is a value handler
`onValue : α → β` together with a node handler `onEffect : (a : P.A) → (P.B a → β) → β`, and
`foldFreeM` is the unique algebra morphism out of the free tree. -/

/-- Fold a free polynomial tree into any algebra of its signature. -/
@[expose]
def foldFreeM (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) : P.FreeM α → β
  | .pure a => onValue a
  | .liftBind a cont => onEffect a fun b => foldFreeM onValue onEffect (cont b)

@[simp]
theorem foldFreeM_pure (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) (a : α) :
    foldFreeM onValue onEffect (pure a) = onValue a :=
  rfl

@[simp]
theorem foldFreeM_lift_bind (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

/-- `foldFreeM_lift_bind` with the node spelled through `>>=`, the form `simp` normalizes to
when the leaf and response types share a universe. -/
@[simp]
theorem foldFreeM_lift_bind' {α : Type uB} {β : Type w} (onValue : α → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (FreeM.lift a >>= cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

theorem foldFreeM_liftBind (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (FreeM.liftBind a cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

@[simp]
theorem foldFreeM_lift (a : P.A) (onValue : P.B a → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) :
    foldFreeM onValue onEffect (FreeM.lift a) = onEffect a onValue :=
  rfl

/-- **Universal property of the fold**: a function agreeing with the algebra on leaves and on
nodes is the fold. -/
theorem foldFreeM_unique (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (h : P.FreeM α → β) (h_pure : ∀ a, h (pure a) = onValue a)
    (h_lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α),
      h ((FreeM.lift a).bind cont) = onEffect a fun b => h (cont b)) :
    h = foldFreeM onValue onEffect := by
  funext x
  induction x with
  | pure a => rw [foldFreeM_pure, h_pure]
  | lift_bind a cont ih => rw [foldFreeM_lift_bind, h_lift_bind]; simp only [ih]

/-! ## Interpretation -/

section liftM

variable {m : Type uB → Type v} [Monad m]

-- upstream: cslib#716
/-- Folding a free polynomial tree by lifting each operation back into `FreeM` is the identity. -/
@[simp]
theorem liftM_lift_eq_self {α : Type uB} (x : P.FreeM α) : FreeM.liftM FreeM.lift x = x := by
  induction x with
  | pure _ => simp
  | lift_bind _ _ ih => simp [ih]

/-- **Naturality of interpretation**: a function `F` between monads that preserves `pure` and
`bind` commutes with `liftM`, sending the interpretation through `s` to the interpretation
through `F ∘ s`. The hypotheses are the fields of a monad-morphism predicate, stated inline so
that both bundled and unbundled morphisms instantiate them. -/
theorem map_liftM {n : Type uB → Type w} [Monad n]
    (F : ∀ {β : Type uB}, m β → n β)
    (hpure : ∀ {β : Type uB} (b : β), F (pure b) = pure b)
    (hbind : ∀ {β γ : Type uB} (x : m β) (g : β → m γ),
      F (x >>= g) = F x >>= fun b => F (g b))
    (s : (a : P.A) → m (P.B a)) {α : Type uB} (x : P.FreeM α) :
    F (FreeM.liftM s x) = FreeM.liftM (fun a => F (s a)) x := by
  induction x with
  | pure a => exact hpure a
  | lift_bind a cont ih => simp only [bind_eq_bind, FreeM.liftM_lift_bind, hbind, ih]

/-- **Handler fusion**: interpreting into a free monad and then into `m` is interpreting once
through the pointwise Kleisli composite of the two handlers. -/
theorem liftM_comp [LawfulMonad m] {Q : PFunctor.{u, uB}} {α : Type uB} (x : P.FreeM α)
    (first : (a : P.A) → Q.FreeM (P.B a)) (second : (a : Q.A) → m (Q.B a)) :
    (x.liftM first).liftM second = x.liftM fun a => (first a).liftM second := by
  induction x with
  | pure _ => rfl
  | lift_bind a cont ih =>
    change ((first a >>= fun b => (cont b).liftM first).liftM second) =
      (first a).liftM second >>= fun b => (cont b).liftM fun a => (first a).liftM second
    rw [FreeM.liftM_bind]
    exact congrArg (fun k => (first a).liftM second >>= k) (funext ih)

end liftM

end PFunctor.FreeM
