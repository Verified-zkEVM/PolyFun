/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Indexed
public import PolyFun.IPFunctor.Free.Basic

/-!
# Two-Index Free Monad on an `IPFunctor` — the `IndexedMonad` Variant

This file defines `IPFunctor.FreeM₂ P : I → I → Type v → Type _`, the two-index variant of the
indexed free monad. Unlike `IPFunctor.FreeM`, every leaf of an `IPFunctor.FreeM₂ P s t α` tree is
required to sit at the post-state `t`, so `IPFunctor.FreeM₂.bind` chains pre- and post-indices
positionally and the type carries a `LawfulIndexedMonad I (IPFunctor.FreeM₂ P)` instance.

`IPFunctor.FreeM₂` is strictly more restrictive than `IPFunctor.FreeM`: an
`IPFunctor.FreeM₂ P s t α` tree corresponds to an `IPFunctor.FreeM P s α` tree whose leaves are
uniformly at state `t`. The forgetful coercion `IPFunctor.FreeM₂.toFreeM` makes this explicit.

## Limitations

There is no general `lift : P.Obj α s → IPFunctor.FreeM₂ P s t α` because `lift`'s post-state
varies with the response (`P.st s a b`); an `IPFunctor.FreeM₂` instead requires a statically
chosen post-state. Where this matters, use `IPFunctor.FreeM` and `IPFunctor.FreeM.lift` directly,
then convert if/when the post-state is known to be uniform.
-/

@[expose] public section

universe uI uA uB v

namespace IPFunctor

variable {I : Type uI}

/-- The two-index variant of the state-indexed free monad. Carries both a pre- and a post-state:
`FreeM₂ P s t α` is a tree starting at state `s`, with all leaves at state `t`, producing
values of type `α`. -/
inductive FreeM₂ (P : IPFunctor.{uI, uA, uB} I) :
    I → I → Type v → Type (max uI uA uB (v + 1))
  /-- A pure leaf, available when pre- and post-states agree. -/
  | pure {s : I} {α} (x : α) : FreeM₂ P s s α
  /-- Roll a shape into a continuation whose branches all terminate at the same post-state `t`. -/
  | roll {s t : I} {α} (a : P.A s)
      (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α) : FreeM₂ P s t α

namespace FreeM₂

variable {P : IPFunctor.{uI, uA, uB} I} {α β γ : Type v} {s t u v : I}

/-! ## Bind chaining indices positionally -/

/-- Bind on `FreeM₂`. The intermediate index `t` is the post-state of `x` and the pre-state of
`g`'s output. -/
@[always_inline, inline]
protected def bind : {s t u : I} →
    FreeM₂ P s t α → (α → FreeM₂ P t u β) → FreeM₂ P s u β
  | _, _, _, .pure x,   g => g x
  | _, _, _, .roll a r, g => .roll a (fun b => (r b).bind g)

@[simp]
lemma bind_pure (x : α) (g : α → FreeM₂ P s u β) :
    (FreeM₂.pure (P := P) (s := s) x).bind g = g x := rfl

@[simp]
lemma bind_roll (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α)
    (g : α → FreeM₂ P t u β) :
    (FreeM₂.roll a r).bind g = FreeM₂.roll a (fun b => (r b).bind g) := rfl

/-! ## Functor map -/

/-- Functor map on `FreeM₂`. -/
protected def map (f : α → β) : {s t : I} → FreeM₂ P s t α → FreeM₂ P s t β
  | _, _, .pure x   => .pure (f x)
  | _, _, .roll a r => .roll a (fun b => (r b).map f)

@[simp]
lemma map_pure (f : α → β) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).map f = FreeM₂.pure (f x) := rfl

@[simp]
lemma map_roll (f : α → β) (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α) :
    (FreeM₂.roll a r).map f = FreeM₂.roll a (fun b => (r b).map f) := rfl

/-! ## Injectivity -/

lemma pure_inj (x y : α) :
    (FreeM₂.pure (P := P) (s := s) x : FreeM₂ P s s α) = FreeM₂.pure y ↔ x = y := by
  refine ⟨?_, fun h => by rw [h]⟩
  intro h; cases h; rfl

@[simp]
lemma roll_inj (a a' : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α)
    (r' : (b : P.B s a') → FreeM₂ P (P.st s a' b) t α) :
    FreeM₂.roll a r = FreeM₂.roll a' r' ↔ ∃ h : a = a', h ▸ r = r' := by
  by_cases ha : a = a'
  · subst ha; simp
  · refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h ha⟩
    cases h; exact (ha rfl).elim

/-! ## Induction principle -/

/-- Induction principle for `FreeM₂` with both pre- and post-state in the motive. -/
@[elab_as_elim]
protected def inductionOn {C : ∀ s t, FreeM₂ P s t α → Prop}
    (pure : ∀ s (x : α), C s s (FreeM₂.pure x))
    (roll : ∀ s t (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α),
      (∀ b, C (P.st s a b) t (r b)) → C s t (FreeM₂.roll a r)) :
    ∀ {s t} (x : FreeM₂ P s t α), C s t x
  | _, _, .pure x   => pure _ x
  | _, _, .roll a r => roll _ _ a r (fun b => FreeM₂.inductionOn pure roll (r b))

/-! ## `Pure` instance and `IndexedMonad` / `LawfulIndexedMonad` instances -/

/-- Plain `Pure` instance for the state-preserving slice `FreeM₂ P s s`.
The `IndexedMonad.ipure` below carries the same data, but exposing the
plain `Pure` typeclass instance is what lets `pure x` / `return x`
resolve inside a `do`-block whose expected type is `FreeM₂ P s s α`. -/
instance (s : I) : Pure (FreeM₂ P s s) where
  pure x := FreeM₂.pure x

instance (P : IPFunctor.{uI, uA, uB} I) :
    IndexedMonad I (fun s t α => FreeM₂.{uI, uA, uB, v} P s t α) where
  ipure := FreeM₂.pure
  ibind := FreeM₂.bind

@[simp]
lemma ipure_def (x : α) :
    (ipure x : FreeM₂ P s s α) = FreeM₂.pure x := rfl

@[simp]
lemma ibind_def (x : FreeM₂ P s t α) (g : α → FreeM₂ P t u β) :
    ibind x g = x.bind g := rfl

instance (P : IPFunctor.{uI, uA, uB} I) :
    LawfulIndexedMonad I (fun s t α => FreeM₂.{uI, uA, uB, v} P s t α) where
  ipure_ibind _ _ := rfl
  ibind_ipure x := by
    induction x using FreeM₂.inductionOn with
    | pure _ _ => rfl
    | roll _ _ _ _ ih => exact congrArg _ (funext ih)
  ibind_assoc x f _ := by
    induction x using FreeM₂.inductionOn with
    | pure _ _ => rfl
    | roll _ _ _ _ ih => exact congrArg _ (funext (fun b => ih b f))

/-! ## Forgetful coercion to single-index `IPFunctor.FreeM`

Every `IPFunctor.FreeM₂ P s t α` tree can be viewed as an `IPFunctor.FreeM P s α` tree by
forgetting the uniform post-state. The reverse direction is not generally available because
`IPFunctor.FreeM P s α` may have leaves at differing states across branches. -/

/-- Forget the post-state, yielding a single-index `FreeM`. -/
def toFreeM : {s t : I} → FreeM₂ P s t α → FreeM P s α
  | _, _, .pure x   => FreeM.pure _ x
  | _, _, .roll a r => FreeM.roll _ a (fun b => (r b).toFreeM)

@[simp]
lemma toFreeM_pure (s : I) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).toFreeM = FreeM.pure s x := rfl

@[simp]
lemma toFreeM_roll (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α) :
    (FreeM₂.roll a r).toFreeM = FreeM.roll s a (fun b => (r b).toFreeM) := rfl

/-! ## `mapM` into a plain monad

The state-transition `P.st s a b` is data-dependent on the response `b`, which prevents
chaining it through the `IndexedMonad` `ibind` signature (whose indices are static). We
therefore interpret `IPFunctor.FreeM₂` into an ordinary monad, dropping the indexed structure on
the target side. The responses live in `Type uB`, so the target monad must operate at that
universe. -/

section mapM

variable {m : Type uB → Type*} {α : Type uB}

/-- Interpret a `FreeM₂` into an arbitrary monad `m`, given for each state `s` and shape
`a : P.A s` a way to produce a response. The state indices are erased on the target side. -/
protected def mapM [Pure m] [Bind m] (h : (s : I) → (a : P.A s) → m (P.B s a)) :
    {s t : I} → FreeM₂ P s t α → m α
  | _, _, .pure x   => Pure.pure x
  | _, _, .roll a r => h _ a >>= fun b => (r b).mapM h

@[simp]
lemma mapM_pure [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a)) (s : I) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_roll [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a))
    (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.st s a b) t α) :
    (FreeM₂.roll a r).mapM h = h _ a >>= fun b => (r b).mapM h := rfl

end mapM

end FreeM₂

end IPFunctor
