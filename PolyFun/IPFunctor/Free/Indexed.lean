/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Indexed
public import PolyFun.IPFunctor.Free.Basic

/-!
# Two-Index Free Monad on an `IPFunctor.Endo` — the `IndexedMonad` Variant

`IPFunctor.FreeM₂ P s t α` is the *terminal-state-marker* specialization of the primitive
[`IPFunctor.IFreeM`](Family.lean):

```
FreeM₂ P s t α := IFreeM P (fun u => PSigma (fun _ : u = t => α)) s
```

A leaf at state `u` carries a proof `u = t` and a value of type `α`, so the type forces every
leaf of a `FreeM₂ P s t α` tree to sit at state `t`. Consequently `FreeM₂.bind` chains pre-
and post-indices positionally, and the type carries a `LawfulIndexedMonad I (FreeM₂ P)`
instance.

`FreeM₂` is strictly more restrictive than `FreeM`: a `FreeM₂ P s t α` tree corresponds to a
`FreeM P s α` tree whose leaves are uniformly at state `t`. The forgetful coercion `toFreeM`
makes this explicit by discarding the equality witness.

## Limitations

There is no general `lift : P.Obj α s → FreeM₂ P s t α` because `lift`'s post-state varies
with the response (`P.src s a b`); `FreeM₂` instead requires a statically chosen post-state.
Where this matters, use `FreeM` and `FreeM.lift` directly, then convert if/when the post-state
is known to be uniform.
-/

@[expose] public section

universe uI uA uB v

namespace IPFunctor

variable {I : Type uI}

/-- The two-index variant of the state-indexed free monad as the *terminal-state-marker*
specialization of [`IPFunctor.IFreeM`](Family.lean). A leaf at state `u` carries a proof
`u = t` (so all leaves sit at `t`) and a value of type `α`.

Defined as a plain `def` (not `@[reducible]`) so the `do`-notation elaborator's
reducible-transparency `whnf` does not unfold the head — keeping `IPFunctor.FreeM₂` visible as
the dispatch handle. Default-transparency unfolding to `IFreeM P (fun u => PSigma _ α) s`
still goes through for the equation-lemma `rfl` proofs in this file. -/
def FreeM₂ (P : Endo.{uI, uA, uB} I) (s t : I) (α : Type v) :
    Type (max uI uA uB (v + 1)) :=
  IFreeM P (fun u => PSigma (fun _ : u = t => α)) s

namespace FreeM₂

variable {P : Endo.{uI, uA, uB} I} {α β γ : Type v} {s t u v : I}

/-- A pure leaf, available when pre- and post-states agree. Tagged `@[match_pattern]`; plain
`def` so the notation elaborator's `.reducible` `whnf` does not unfold the head. -/
@[match_pattern]
def pure {s : I} {α} (x : α) : FreeM₂ P s s α :=
  IFreeM.pure (s := s) ⟨rfl, x⟩

/-- Roll a shape into a continuation whose branches all terminate at the same post-state `t`.
Tagged `@[match_pattern]`; plain `def` (same reasoning as `FreeM₂.pure`). -/
@[match_pattern]
def roll {s t : I} {α} (a : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) : FreeM₂ P s t α :=
  IFreeM.roll (X := fun u => PSigma (fun _ : u = t => α)) a r

/-! ## Bind chaining indices positionally -/

/-- Bind on `FreeM₂`. The intermediate index `t` is the post-state of `x` and the pre-state of
`g`'s output. Defined via `IFreeM.bind` by transporting `g a` along the equality witness
recovered from the leaf payload. -/
@[always_inline, inline]
protected def bind {s t u : I} (x : FreeM₂ P s t α) (g : α → FreeM₂ P t u β) :
    FreeM₂ P s u β :=
  IFreeM.bind x (fun _ p => p.casesOn (fun h a => h ▸ g a))

@[simp]
lemma bind_pure (x : α) (g : α → FreeM₂ P s u β) :
    (FreeM₂.pure (P := P) (s := s) x).bind g = g x := rfl

@[simp]
lemma bind_roll (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α)
    (g : α → FreeM₂ P t u β) :
    (FreeM₂.roll a r).bind g = FreeM₂.roll a (fun b => (r b).bind g) := rfl

/-! ## Functor map -/

/-- Functor map on `FreeM₂`. Preserves the equality witness, applies `f` to the payload. -/
protected def map (f : α → β) : {s t : I} → FreeM₂ P s t α → FreeM₂ P s t β :=
  fun x => IFreeM.imap (fun _ p => ⟨p.1, f p.2⟩) x

@[simp]
lemma map_pure (f : α → β) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).map f = FreeM₂.pure (f x) := rfl

@[simp]
lemma map_roll (f : α → β) (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    (FreeM₂.roll a r).map f = FreeM₂.roll a (fun b => (r b).map f) := rfl

/-! ## Injectivity -/

lemma pure_inj (s : I) (x y : α) :
    FreeM₂.pure (P := P) (s := s) x = FreeM₂.pure (s := s) y ↔ x = y := by
  refine (IFreeM.pure_inj (P := P) (X := fun u => PSigma (fun _ : u = s => α))
    (s := s) ⟨rfl, x⟩ ⟨rfl, y⟩).trans ?_
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  injection h

@[simp]
lemma roll_inj (a a' : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α)
    (r' : (b : P.B s a') → FreeM₂ P (P.src s a' b) t α) :
    FreeM₂.roll a r = FreeM₂.roll a' r' ↔ ∃ h : a = a', h ▸ r = r' :=
  IFreeM.roll_inj (P := P) (X := fun u => PSigma (fun _ : u = t => α)) (s := s) a a' r r'

/-! ## Induction principle -/

/-- Induction principle for `FreeM₂` with both pre- and post-state in the motive. Wraps
`IFreeM.inductionOn` so the `pure` / `roll` cases see the high-level `FreeM₂` constructors. -/
@[elab_as_elim]
protected def inductionOn {C : ∀ s t, FreeM₂ P s t α → Prop}
    (pure : ∀ s (x : α), C s s (FreeM₂.pure x))
    (roll : ∀ s t (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α),
      (∀ b, C (P.src s a b) t (r b)) → C s t (FreeM₂.roll a r))
    {s t : I} (x : FreeM₂ P s t α) : C s t x := by
  -- Reduce to induction on the underlying IFreeM. The leaf payload `⟨h, a⟩` carries the
  -- equality witness `h : s' = t`, which lets us identify the leaf state with `t`.
  refine IFreeM.inductionOn
    (P := P) (X := fun u => PSigma (fun _ : u = t => α))
    (C := fun s' (x : IFreeM P (fun u => PSigma (fun _ : u = t => α)) s') => C s' t x)
    ?_ ?_ x
  · rintro s' ⟨h, a⟩
    subst h
    exact pure _ a
  · intro s' a r ih
    exact roll s' t a r ih

/-! ## `Functor` / `LawfulFunctor` instances

`FreeM₂` is a functor in the value type at fixed pre/post-states. State is unchanged by
mapping (it only rewrites leaves), so the instance is well-defined despite `FreeM₂` not
being a plain `Monad`. Proofs use `IFreeM.inductionOn` on the underlying primitive. -/

instance (s t : I) : Functor (FreeM₂ P s t) where
  map f x := FreeM₂.map f x
  mapConst b x := FreeM₂.map (fun _ => b) x

instance (s t : I) : LawfulFunctor (FreeM₂ P s t) where
  map_const := rfl
  id_map x := by
    change FreeM₂.map id x = x
    induction x using IFreeM.inductionOn with
    | pure _ _ => rfl
    | roll _ a r ih =>
      change FreeM₂.map id (FreeM₂.roll a r) = FreeM₂.roll a r
      exact congrArg _ (funext ih)
  comp_map f g x := by
    change FreeM₂.map (g ∘ f) x = FreeM₂.map g (FreeM₂.map f x)
    induction x using IFreeM.inductionOn with
    | pure _ _ => rfl
    | roll _ a r ih =>
      change FreeM₂.map (g ∘ f) (FreeM₂.roll a r) =
        FreeM₂.map g (FreeM₂.map f (FreeM₂.roll a r))
      exact congrArg _ (funext (fun b => ih b))

/-! ## `Pure` instance and `IndexedMonad` / `LawfulIndexedMonad` instances -/

/-- Plain `Pure` instance for the state-preserving slice `FreeM₂ P s s`. The `IndexedMonad.ipure`
below carries the same data, but exposing the plain `Pure` typeclass instance is what lets
`pure x` / `return x` resolve inside a `do`-block whose expected type is `FreeM₂ P s s α`. -/
instance (s : I) : Pure (FreeM₂ P s s) where
  pure x := FreeM₂.pure x

instance (P : Endo.{uI, uA, uB} I) :
    IndexedMonad I (fun s t α => FreeM₂.{uI, uA, uB, v} P s t α) where
  ipure := FreeM₂.pure
  ibind := FreeM₂.bind

@[simp]
lemma ipure_def (x : α) :
    (ipure x : FreeM₂ P s s α) = FreeM₂.pure x := rfl

@[simp]
lemma ibind_def (x : FreeM₂ P s t α) (g : α → FreeM₂ P t u β) :
    ibind x g = x.bind g := rfl

instance (P : Endo.{uI, uA, uB} I) :
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

/-! ## Forgetful coercion to single-index `FreeM`

Every `FreeM₂ P s t α` tree can be viewed as a `FreeM P s α` tree by forgetting the uniform
post-state. The reverse direction is not generally available because `FreeM P s α` may have
leaves at differing states across branches. -/

/-- Forget the post-state, yielding a single-index `FreeM`. Forgets the equality witness at
each leaf, keeping the payload. -/
def toFreeM : {s t : I} → FreeM₂ P s t α → FreeM P s α :=
  fun x => IFreeM.imap (fun _ p => p.2) x

@[simp]
lemma toFreeM_pure (s : I) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).toFreeM = FreeM.pure s x := rfl

@[simp]
lemma toFreeM_roll (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    (FreeM₂.roll a r).toFreeM = FreeM.roll s a (fun b => (r b).toFreeM) := rfl

/-! ## Pre-state transport and witness-carrying leaves

The pre-state of a `FreeM₂` is a type-level parameter, so translations that compute the
pre-state only propositionally need an explicit transport `castPre`. Its companion `pureCast`
generalizes `FreeM₂.pure` to a leaf carrying an arbitrary proof that the pre-state equals the
post-state; binding such a leaf transports the continuation along the witness
(`bind_pureCast`). Both are bare `Eq.rec`s / constructor applications, so every commutation
lemma is proved by `subst` and reflexive transports vanish definitionally.

There is no `castPost`-through-`roll` analogue for the *pre*-state: the shape type `P.A s`
itself depends on the pre-state, so casting it commutes with `roll` only when the shape
family is constant (as for the indexed image of a graded polynomial). -/

/-- Transport a `FreeM₂` along an equality of pre-states. -/
def castPre {s s' : I} (e : s = s') (x : FreeM₂ P s t α) : FreeM₂ P s' t α :=
  e ▸ x

@[simp]
lemma castPre_rfl {s : I} (e : s = s) (x : FreeM₂ P s t α) :
    castPre e x = x := rfl

@[simp]
lemma castPre_castPre {s s' s'' : I} (e : s = s') (e' : s' = s'') (x : FreeM₂ P s t α) :
    castPre e' (castPre e x) = castPre (e.trans e') x := by
  subst e'; subst e; rfl

/-- A pure leaf at pre-state `s` with post-state `t`, carrying a proof `s = t`.
Generalizes `FreeM₂.pure`, which is the diagonal case `pureCast rfl`. -/
def pureCast {s t : I} (w : s = t) (x : α) : FreeM₂ P s t α :=
  IFreeM.pure ⟨w, x⟩

@[simp]
lemma pureCast_rfl {s : I} (w : s = s) (x : α) :
    pureCast (P := P) w x = FreeM₂.pure x := rfl

@[simp]
lemma castPre_pureCast {s s' t : I} (e : s = s') (w : s = t) (x : α) :
    castPre (P := P) e (pureCast w x) = pureCast (e.symm.trans w) x := by
  subst e; rfl

/-- Binding a witness-carrying leaf transports the continuation along the witness. -/
@[simp]
lemma bind_pureCast {s t u : I} (w : s = t) (x : α) (g : α → FreeM₂ P t u β) :
    (pureCast (P := P) w x).bind g = castPre w.symm (g x) := by
  subst w; rfl

/-- Pre-state transports float out of the tree argument of `bind`. -/
@[simp]
lemma bind_castPre {s s' t u : I} (e : s = s') (x : FreeM₂ P s t α)
    (g : α → FreeM₂ P t u β) :
    (castPre e x).bind g = castPre e (x.bind g) := by
  subst e; rfl

/-- Witness-carrying leaves are equal exactly when their payloads are: the witnesses are
proofs and play no role. -/
@[simp]
lemma pureCast_inj {s t : I} (w₁ w₂ : s = t) (x y : α) :
    pureCast (P := P) w₁ x = pureCast w₂ y ↔ x = y := by
  subst w₁
  rw [pureCast_rfl, pureCast_rfl, pure_inj]

@[simp]
lemma pureCast_ne_roll {s t : I} (w : s = t) (x : α) (a : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    pureCast (P := P) w x ≠ FreeM₂.roll a r := by
  intro h; injection h

@[simp]
lemma roll_ne_pureCast {s t : I} (w : s = t) (x : α) (a : P.A s)
    (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    FreeM₂.roll a r ≠ pureCast (P := P) w x := by
  intro h; injection h

/-! ## `mapM` into a plain monad

The source-index map `P.src s a b` is data-dependent on the response `b`, which prevents
chaining it through the `IndexedMonad` `ibind` signature (whose indices are static). We
therefore interpret `FreeM₂` into an ordinary monad, dropping the indexed structure on the
target side. -/

section mapM

variable {m : Type uB → Type*} {α : Type uB}

/-- Interpret a `FreeM₂` into an arbitrary monad `m`, given for each state `s` and shape
`a : P.A s` a way to produce a response. The state indices are erased on the target side.
Wraps `IFreeM.mapM` with a leaf interpretation that discards the equality witness. -/
protected def mapM [Pure m] [Bind m] (h : (s : I) → (a : P.A s) → m (P.B s a))
    {s t : I} (x : FreeM₂ P s t α) : m α :=
  IFreeM.mapM h (fun _ p => Pure.pure p.2) x

@[simp]
lemma mapM_pure [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a)) (s : I) (x : α) :
    (FreeM₂.pure (P := P) (s := s) x).mapM h = Pure.pure x := rfl

@[simp]
lemma mapM_roll [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a))
    (a : P.A s) (r : (b : P.B s a) → FreeM₂ P (P.src s a b) t α) :
    (FreeM₂.roll a r).mapM h = h _ a >>= fun b => (r b).mapM h := rfl

@[simp]
lemma mapM_pureCast [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a)) {s t : I} (w : s = t) (x : α) :
    (pureCast (P := P) w x).mapM h = Pure.pure x := rfl

end mapM

end FreeM₂

end IPFunctor
