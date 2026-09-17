/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Extensions of the free monad on a polynomial functor

Additions to cslib's `PFunctor.FreeM` API staged for upstreaming: the two elaborators that spell
an operation node in its simp normal form with the direction type unindexed, a case-analysis
principle in the same `(lift a).bind cont` normal form as cslib's induction principle, the functor
equations `map_pure` / `map_bind` and the node equations `map_lift_bind` /
`functorMap_lift_bind` together with their constructor spellings, the catamorphism `foldFreeM`
with its universal property (the polynomial counterpart of `Cslib.FreeM.foldFreeM`), handler
fusion `liftM_comp`, and the identity fold `liftM_lift_eq_self`. Naturality of `liftM` along a
monad morphism is upstream's `Cslib.IsMonadHom.map_pfunctorFreeMLiftM`.

Every declaration lives in the upstream namespace `PFunctor.FreeM` and uses no vocabulary beyond
cslib's. A lemma that duplicates an open cslib pull request carries an `upstream:` comment naming
it and is deleted when that request lands; the rest are marked `upstream candidate`.

## The simp normal form of an operation node

cslib's `FreeM.liftBind_eq` is a `simp` lemma, so simplification presents an operation node
`FreeM.liftBind a k` as `(FreeM.lift a).bind k` — and, when results and directions share a
universe, `FreeM.bind_eq_bind` takes it on to `FreeM.lift a >>= k`. Downstream `simp` equations
are stated on those two spellings (suffixes `_lift_bind` and `_lift_bind'`), keeping the
constructor spelling (suffix `_liftBind`) for `rw` on `match`-shaped goals.

Both normal forms carry the direction type `P.B a` as an implicit type argument of the bind, and
the simplifier indexes implicit type arguments. On a concrete polynomial that type reduces (to
`D a` for `⟨I, D⟩`), so a lemma indexed on `P.B a` would never match there. The elaborators
`lift_bind%` and `lift_bind'%` produce the normal forms with that argument marked `no_index`;
normal-form `simp` lemmas are stated through them.
-/

public section

/-- The simp normal form `(FreeM.lift a).bind k` of an operation node, with the direction type
left unindexed so lemmas stated with it also match nodes over concrete polynomials. -/
macro "lift_bind% " a:term:max k:term:max : term =>
  `(@PFunctor.FreeM.bind _ (no_index _) _ (PFunctor.FreeM.lift $a) $k)

/-- The simp normal form `FreeM.lift a >>= k` of an operation node whose results and directions
share a universe, with the direction type left unindexed. -/
macro "lift_bind'% " a:term:max k:term:max : term =>
  `(@Bind.bind _ _ (no_index _) _ (PFunctor.FreeM.lift $a) $k)

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

-- upstream candidate (cslib#716 proposed it and was closed without merging)
@[simp]
theorem map_pure (f : α → β) (x : α) : map f (pure x : P.FreeM α) = pure (f x) := rfl

-- upstream candidate (cslib#716)
@[simp]
theorem map_bind (f : β → γ) (x : P.FreeM α) (cont : α → P.FreeM β) :
    map f (x.bind cont) = x.bind fun a => (cont a).map f := by
  simp_rw [← bind_pure_comp, FreeM.bind_assoc]

/-- Mapping through a node maps every continuation, in simp normal form. -/
@[simp]
theorem map_lift_bind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f (lift_bind% a cont) = (FreeM.lift a).bind fun b => map f (cont b) :=
  rfl

/-- Mapping through a node maps every continuation, in constructor spelling. -/
theorem map_liftBind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    map f (FreeM.liftBind a cont) = FreeM.liftBind a fun b => map f (cont b) :=
  rfl

/-- `Functor.map` through an operation node whose result type lives in a universe other than
the direction universe. When the universes agree the node normalises to `FreeM.lift a >>= cont`
instead and the generic `map_bind` applies. -/
@[simp]
theorem functorMap_lift_bind {α β : Type v} (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    f <$> lift_bind% a cont = (FreeM.lift a).bind fun b => f <$> cont b :=
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
    foldFreeM onValue onEffect (lift_bind% a cont) =
      onEffect a fun b => foldFreeM onValue onEffect (cont b) :=
  rfl

/-- `foldFreeM_lift_bind` with the node spelled through `>>=`, the form `simp` normalizes to
when the leaf and response types share a universe. -/
@[simp]
theorem foldFreeM_lift_bind' {α : Type uB} {β : Type w} (onValue : α → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (lift_bind'% a cont) =
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
    foldFreeM (α := no_index (P.B a)) onValue onEffect (FreeM.lift a) = onEffect a onValue :=
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

-- upstream candidate (cslib#716)
/-- Folding a free polynomial tree by lifting each operation back into `FreeM` is the identity. -/
@[simp]
theorem liftM_lift_eq_self {α : Type uB} (x : P.FreeM α) : FreeM.liftM FreeM.lift x = x := by
  induction x with
  | pure _ => simp
  | lift_bind _ _ ih => simp [ih]

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
