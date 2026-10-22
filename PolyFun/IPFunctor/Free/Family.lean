/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic
public import PolyFun.PFunctor.Free.Basic

/-!
# State-Indexed Free Monad on an Endomorphic `IPFunctor`

This file defines the primitive `IPFunctor.IFreeM P X : I → Type v`, the free monad over an
endomorphic indexed polynomial functor `P : IPFunctor.Endo I` taking a *state-indexed* return
family `X : I → Type v`. Leaves at state `s` carry values of type `X s`; the available head
shapes at each `liftBind` are gated by the current state, and the state of each continuation
branch is the source index `P.src s a b` of the chosen response.

The two parallel free monads
[`IPFunctor.FreeM`](Basic.lean) and [`IPFunctor.FreeM₂`](Indexed.lean) are obtained as
specializations:

* `FreeM P s α := IFreeM P (fun _ => α) s` — the *constant* return family.
* `FreeM₂ P s t α := IFreeM P (fun u => PSigma (fun _ : u = t => α)) s` — the
  *terminal-state-marker* family.

`IFreeM` itself is not a `Monad` — its bind is family-polymorphic in the leaf state,
since different branches of an `IFreeM` tree end at different leaf states. The continuation's
leaf family may live in a different universe from the tree's; `bind_assoc` relates leaf
families in three independent universes.
-/

@[expose] public section

universe uI uA uB v w w'

namespace IPFunctor

variable {I : Type uI}

/-- The state-indexed free monad over an endomorphic `IPFunctor`. The return family
`X : I → Type v` is state-indexed, so each leaf carries a value of type `X s` at its own
leaf state `s`. -/
inductive IFreeM (P : Endo.{uI, uA, uB} I) (X : I → Type v) : I → Type (max uI uA uB (v + 1))
  /-- A pure leaf at state `s` carrying a value of type `X s`. -/
  | pure {s : I} (x : X s) : IFreeM P X s
  /-- Roll a shape at state `s` into a continuation, with each branch landing at the
  source index `P.src s a b`. -/
  | liftBind {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) : IFreeM P X s

namespace IFreeM

variable {P : Endo.{uI, uA, uB} I} {X Y Z : I → Type v}

/-! ## Bind: family-polymorphic continuation -/

/-- Family-polymorphic bind on `IFreeM`. The continuation `g` accepts the leaf state
explicitly because different leaves of `x` may land at different states, and its leaf family
`Y` may live in a different universe from `X`. Specializes to both `FreeM.bind` (constant
family) and `FreeM₂.bind` (terminal-state-marker family). -/
@[always_inline, inline]
protected def bind {Y : I → Type w} :
    {s : I} → IFreeM P X s → (∀ s', X s' → IFreeM P Y s') → IFreeM P Y s
  | _, .pure x,   g => g _ x
  | _, .liftBind a r, g => .liftBind a (fun b => (r b).bind g)

@[simp]
lemma pure_bind {Y : I → Type w} {s : I} (x : X s) (g : ∀ s', X s' → IFreeM P Y s') :
    (IFreeM.pure (P := P) x).bind g = g s x := rfl

@[deprecated (since := "2026-10-19")] alias bind_pure := pure_bind

@[simp]
lemma bind_liftBind {Y : I → Type w} {s : I} (a : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b)) (g : ∀ s', X s' → IFreeM P Y s') :
    (IFreeM.liftBind a r).bind g = IFreeM.liftBind a (fun b => (r b).bind g) := rfl

/-! ## Family map -/

/-- Family functor map: apply a state-indexed function `f : ∀ s, X s → Y s` at every leaf. -/
protected def imap {Y : I → Type w} (f : ∀ s, X s → Y s) : {s : I} → IFreeM P X s → IFreeM P Y s
  | _, .pure x   => .pure (f _ x)
  | _, .liftBind a r => .liftBind a (fun b => (r b).imap f)

@[simp]
lemma imap_pure {Y : I → Type w} (f : ∀ s, X s → Y s) {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).imap f = IFreeM.pure (f s x) := rfl

@[simp]
lemma imap_liftBind {Y : I → Type w} (f : ∀ s, X s → Y s) {s : I} (a : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a r).imap f = IFreeM.liftBind a (fun b => (r b).imap f) := rfl

/-! ## Injectivity -/

lemma pure_inj {s : I} (x y : X s) :
    IFreeM.pure (P := P) x = IFreeM.pure y ↔ x = y := by simp

lemma liftBind_inj {s : I} (a a' : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b))
    (r' : (b : P.B s a') → IFreeM P X (P.src s a' b)) :
    IFreeM.liftBind a r = IFreeM.liftBind a' r' ↔ ∃ h : a = a', h ▸ r = r' := by grind

/-! ## Induction principles

The motive must be state-indexed because the continuation of a `liftBind` lands at a different
state than the parent. -/

/-- Induction principle for `IFreeM` with a state-indexed Prop-valued motive. -/
@[elab_as_elim]
protected theorem inductionOn {C : ∀ s, IFreeM P X s → Prop}
    (pure : ∀ s (x : X s), C s (IFreeM.pure x))
    (liftBind : ∀ s (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)),
      (∀ b, C (P.src s a b) (r b)) → C s (IFreeM.liftBind a r)) :
    ∀ {s} (x : IFreeM P X s), C s x
  | _, .pure x   => pure _ x
  | _, .liftBind a r => liftBind _ a r (fun b => IFreeM.inductionOn pure liftBind (r b))

/-- Dependent recursor (`Type*`-valued) for `IFreeM`. -/
@[elab_as_elim]
protected def construct {C : ∀ s, IFreeM P X s → Type*}
    (pure : ∀ s (x : X s), C s (IFreeM.pure x))
    (liftBind : ∀ s (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)),
      (∀ b, C (P.src s a b) (r b)) → C s (IFreeM.liftBind a r)) :
    ∀ {s} (x : IFreeM P X s), C s x
  | _, .pure x   => pure _ x
  | _, .liftBind a r => liftBind _ a r (fun b => IFreeM.construct pure liftBind (r b))

section construct

variable {C : ∀ s, IFreeM P X s → Type*}
  (h_pure : ∀ s (x : X s), C s (IFreeM.pure x))
  (h_liftBind : ∀ s (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)),
      (∀ b, C (P.src s a b) (r b)) → C s (IFreeM.liftBind a r))

@[simp]
lemma construct_pure {s : I} (x : X s) :
    IFreeM.construct h_pure h_liftBind (IFreeM.pure (P := P) x) = h_pure s x := rfl

@[simp]
lemma construct_liftBind {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.construct h_pure h_liftBind (IFreeM.liftBind a r) : C s (IFreeM.liftBind a r)) =
      h_liftBind s a r (fun b => IFreeM.construct h_pure h_liftBind (r b)) := rfl

end construct

/-! ## Bind and map laws

The continuation of `bind` may change the universe of the leaf family, so `bind_assoc`,
`bind_imap` and `imap_bind` take their families in independent universes. `imap` is the bind
whose continuation returns a leaf (`imap_eq_bind`), also across universes. -/

/-- Binding with `IFreeM.pure` returns the tree unchanged. -/
@[simp]
lemma bind_pure_right {s : I} (x : IFreeM P X s) : x.bind (fun _ y => IFreeM.pure y) = x := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

/-- Bind is associative, with the three leaf families in independent universes. -/
lemma bind_assoc {Y : I → Type w} {Z : I → Type w'} {s : I} (x : IFreeM P X s)
    (f : ∀ s', X s' → IFreeM P Y s') (g : ∀ s', Y s' → IFreeM P Z s') :
    (x.bind f).bind g = x.bind (fun s' y => (f s' y).bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

/-- Mapping the leaves is binding with a continuation that returns a leaf. -/
lemma imap_eq_bind {Y : I → Type w} (f : ∀ s, X s → Y s) {s : I} (x : IFreeM P X s) :
    x.imap f = x.bind (fun s' y => IFreeM.pure (f s' y)) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

@[simp]
lemma imap_id {s : I} (x : IFreeM P X s) : x.imap (fun _ => id) = x := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

@[simp]
lemma imap_imap {Y : I → Type w} {Z : I → Type w'} (f : ∀ s, X s → Y s)
    (g : ∀ s, Y s → Z s) {s : I} (x : IFreeM P X s) :
    (x.imap f).imap g = x.imap (fun s' => g s' ∘ f s') := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

/-- Binding after mapping the leaves feeds the mapped payloads to the continuation. -/
lemma bind_imap {Y : I → Type w} {Z : I → Type w'} (f : ∀ s, X s → Y s)
    (g : ∀ s', Y s' → IFreeM P Z s')
    {s : I} (x : IFreeM P X s) :
    (x.imap f).bind g = x.bind (fun s' y => g s' (f s' y)) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

/-- Mapping the leaves of a bind maps the leaves of each continuation. -/
lemma imap_bind {Y : I → Type w} {Z : I → Type w'} (g : ∀ s', X s' → IFreeM P Y s')
    (f : ∀ s, Y s → Z s)
    {s : I} (x : IFreeM P X s) :
    (x.bind g).imap f = x.bind (fun s' y => (g s' y).imap f) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ a _ ih => exact congrArg (IFreeM.liftBind a) (funext ih)

/-! ## `mapM`: interpreting `IFreeM` into a monad

The responses `P.B s a` live in `Type uB`, so the target monad `m` is constrained to
`Type uB → Type w`. The leaf interpretation `k` says how to convert a leaf payload
`X s` (at any leaf state `s`) into an `m α` action; the result is a single `m α`. -/

section mapM

variable {m : Type uB → Type w} {α : Type uB}

/-- Interpret an `IFreeM P X` into an arbitrary monad `m`. The shape handler `h` produces a
response for each `(s, a : P.A s)`; the leaf handler `k` converts each leaf payload `X s` into
an `m α` action. Leaves at different states can therefore feed back into the same `m α`. -/
protected def mapM [Pure m] [Bind m]
    (h : (s : I) → (a : P.A s) → m (P.B s a))
    (k : (s : I) → X s → m α) :
    {s : I} → IFreeM P X s → m α
  | _, .pure x   => k _ x
  | _, .liftBind a r => h _ a >>= fun b => (r b).mapM h k

variable [Pure m] [Bind m]
  (h : (s : I) → (a : P.A s) → m (P.B s a)) (k : (s : I) → X s → m α)

@[simp]
lemma mapM_pure {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).mapM h k = k s x := rfl

@[simp]
lemma mapM_liftBind {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a r).mapM h k = h _ a >>= fun b => (r b).mapM h k := rfl

end mapM

/-! ## Σ-bundled forgetful map

Forget the source-index structure by Σ-bundling the originating state into each `PFunctor`
position, yielding a `PFunctor.FreeM` over `P.sigmaPFunctor` whose leaves are pairs
`⟨s, X s⟩`. The leaf-state escape lets callers recover the family value `X s` on the target
side; constant-family callers (`FreeM`) post-compose with `Sigma.snd` to drop the state. -/

section toSigmaFreeM

/-- Σ-bundled erasure: the leaf state is carried with the leaf payload as `Σ s, X s`. -/
def toSigmaFreeM (P : Endo I) :
    {s : I} → IFreeM P X s → P.sigmaPFunctor.FreeM (Σ s, X s)
  | _, .pure (s := s) x => PFunctor.FreeM.pure ⟨s, x⟩
  | _, .liftBind (s := s) a r =>
      PFunctor.FreeM.liftBind (⟨s, a⟩ : P.sigmaPFunctor.A) (fun b => toSigmaFreeM P (r b))

@[simp]
lemma toSigmaFreeM_pure (P : Endo I) {s : I} (x : X s) :
    toSigmaFreeM P (IFreeM.pure (P := P) x) = PFunctor.FreeM.pure ⟨s, x⟩ := rfl

@[simp]
lemma toSigmaFreeM_liftBind (P : Endo I) {s : I} (a : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    toSigmaFreeM P (IFreeM.liftBind a r) =
      PFunctor.FreeM.liftBind (⟨s, a⟩ : P.sigmaPFunctor.A)
        (fun b => toSigmaFreeM P (r b)) := rfl

/-- Erasure preserves sequencing, including a change of leaf universe. -/
@[simp]
lemma toSigmaFreeM_bind {Y : I → Type w} {s : I} (x : IFreeM P X s)
    (g : ∀ s', X s' → IFreeM P Y s') :
    toSigmaFreeM P (x.bind g) =
      PFunctor.FreeM.bind (toSigmaFreeM P x) (fun value => toSigmaFreeM P (g value.1 value.2)) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ _ _ ih =>
      simp only [bind_liftBind, toSigmaFreeM_liftBind]
      congr 1
      funext answer
      exact ih answer

/-- Erasure maps the payload while retaining its terminal state. -/
@[simp]
lemma toSigmaFreeM_imap {Y : I → Type w} {s : I} (f : ∀ s, X s → Y s)
    (x : IFreeM P X s) :
    toSigmaFreeM P (x.imap f) =
      PFunctor.FreeM.map (fun value => (⟨value.1, f value.1 value.2⟩ : Σ s, Y s))
        (toSigmaFreeM P x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ _ _ ih =>
      simp only [imap_liftBind, toSigmaFreeM_liftBind, PFunctor.FreeM.map_liftBind]
      congr 1
      funext answer
      exact ih answer

end toSigmaFreeM

end IFreeM

end IPFunctor
