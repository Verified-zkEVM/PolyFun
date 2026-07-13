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
since different branches of an `IFreeM` tree end at different leaf states.
-/

@[expose] public section

universe uI uA uB v w

namespace IPFunctor

variable {I : Type uI}

/-- The state-indexed free monad over an endomorphic `IPFunctor`. The return family
`X : I → Type v` is state-indexed, so each leaf carries a value of type `X s` at its own
leaf state `s`. -/
inductive IFreeM (P : Endo.{uI, uA, uB} I) (X : I → Type v) :
    I → Type (max uI uA uB (v + 1))
  /-- A pure leaf at state `s` carrying a value of type `X s`. -/
  | pure {s : I} (x : X s) : IFreeM P X s
  /-- Roll a shape at state `s` into a continuation, with each branch landing at the
  source index `P.src s a b`. -/
  | liftBind {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b)) : IFreeM P X s

namespace IFreeM

variable {P : Endo.{uI, uA, uB} I} {X Y Z : I → Type v}

/-! ## Bind: family-polymorphic continuation -/

/-- Family-polymorphic bind on `IFreeM`. The continuation `g` accepts the leaf state
explicitly because different leaves of `x` may land at different states. Specializes to both
`FreeM.bind` (constant family) and `FreeM₂.bind` (terminal-state-marker family). -/
@[always_inline, inline]
protected def bind : {s : I} → IFreeM P X s → (∀ s', X s' → IFreeM P Y s') → IFreeM P Y s
  | _, .pure x,   g => g _ x
  | _, .liftBind a r, g => .liftBind a (fun b => (r b).bind g)

@[simp]
lemma bind_pure {s : I} (x : X s) (g : ∀ s', X s' → IFreeM P Y s') :
    (IFreeM.pure (P := P) x).bind g = g s x := rfl

@[simp]
lemma bind_liftBind {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b))
    (g : ∀ s', X s' → IFreeM P Y s') :
    (IFreeM.liftBind a r).bind g = IFreeM.liftBind a (fun b => (r b).bind g) := rfl

/-! ## Family map -/

/-- Family functor map: apply a state-indexed function `f : ∀ s, X s → Y s` at every leaf. -/
protected def imap (f : ∀ s, X s → Y s) : {s : I} → IFreeM P X s → IFreeM P Y s
  | _, .pure x   => .pure (f _ x)
  | _, .liftBind a r => .liftBind a (fun b => (r b).imap f)

@[simp]
lemma imap_pure (f : ∀ s, X s → Y s) {s : I} (x : X s) :
    (IFreeM.pure (P := P) x).imap f = IFreeM.pure (f s x) := rfl

@[simp]
lemma imap_liftBind (f : ∀ s, X s → Y s) {s : I} (a : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b)) :
    (IFreeM.liftBind a r).imap f = IFreeM.liftBind a (fun b => (r b).imap f) := rfl

/-! ## Injectivity -/

lemma pure_inj {s : I} (x y : X s) :
    IFreeM.pure (P := P) x = IFreeM.pure y ↔ x = y := by
  refine ⟨?_, fun h => by rw [h]⟩
  intro h; cases h; rfl

lemma liftBind_inj {s : I} (a a' : P.A s)
    (r : (b : P.B s a) → IFreeM P X (P.src s a b))
    (r' : (b : P.B s a') → IFreeM P X (P.src s a' b)) :
    IFreeM.liftBind a r = IFreeM.liftBind a' r' ↔ ∃ h : a = a', h ▸ r = r' := by
  by_cases ha : a = a'
  · subst ha; simp
  · refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h ha⟩
    cases h; exact (ha rfl).elim

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

end toSigmaFreeM

end IFreeM

end IPFunctor
