/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Bound

/-!
# Indexed free trees through ordinary imports

`IFreeM.bind` may move the leaf payloads to another universe. Its equations and laws are used at
independent leaf universes, including a continuation whose leaves are types, and the
constant-family bind still unfolds to it.

Roll bounds unfold to their constructor form, compose across leaf universes, and are reached by
dot notation on `IFreeM`, `FreeM` and `FreeM₂`.
-/

@[expose] public section

universe uI uA uB v w w'

namespace PolyFunTest.ModuleAPI.IndexedFree

open IPFunctor

section generic

variable {I : Type uI} {P : IPFunctor.Endo.{uI, uA, uB} I} {X : I → Type v}
  {Y : I → Type w} {Z : I → Type w'}

example {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b))
    (g : ∀ s', X s' → IFreeM P Y s') :
    (IFreeM.liftBind a r).bind g = IFreeM.liftBind a fun b => (r b).bind g := by
  rw [IFreeM.bind_liftBind]

example {s : I} (x : IFreeM P X s) (f : ∀ s', X s' → IFreeM P Y s')
    (g : ∀ s', Y s' → IFreeM P Z s') :
    (x.bind f).bind g = x.bind fun s' y => (f s' y).bind g :=
  IFreeM.bind_assoc x f g

/-- Lifting the leaves to a larger universe and lowering them again is the identity. -/
example {s : I} (x : IFreeM P X s) :
    (x.bind fun _ y => IFreeM.pure (ULift.up.{w} y)).bind (fun _ y => IFreeM.pure y.down) =
      x := by
  rw [IFreeM.bind_assoc]
  simp

example {s : I} (f : ∀ s, X s → X s) (x : IFreeM P X s) :
    x.imap f = x.bind fun s' y => IFreeM.pure (f s' y) :=
  IFreeM.imap_eq_bind f x

example {α β : Type v} {s : I} (x : FreeM P s α) (g : (s' : I) → α → FreeM P s' β) :
    x.bind g = IFreeM.bind x g := rfl

/-! ## Roll bounds -/

/-- A charge bound on a `liftBind` is built from its constructor form. -/
example {s : I} (a : P.A s) (r : (b : P.B s a) → IFreeM P X (P.src s a b))
    {c : (s : I) → P.A s → ℕ} {n : ℕ} (ha : c s a ≤ n)
    (hr : ∀ b, (r b).IsChargeBound c (n - c s a)) :
    (IFreeM.liftBind a r).IsChargeBound c n :=
  ⟨ha, hr⟩

example {s : I} {x : IFreeM P X s} {g : ∀ s', X s' → IFreeM P Y s'} {c : (s : I) → P.A s → ℕ}
    {n₁ n₂ : ℕ} (h₁ : x.IsChargeBound c n₁) (h₂ : ∀ s' y, (g s' y).IsChargeBound c n₂) :
    (x.bind g).IsChargeBound c (n₁ + n₂) :=
  IFreeM.isChargeBound_bind h₁ h₂

example {s : I} (x : IFreeM P X s) (n : ℕ) :
    (IFreeM.toSigmaFreeM P x).IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  IFreeM.isTotalRollBound_toSigmaFreeM_iff x n

example {α : Type v} {s : I} (x : FreeM P s α) (n : ℕ) :
    (FreeM.toSigmaFreeM P x).IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  FreeM.isTotalRollBound_toSigmaFreeM_iff x n

example {α β : Type v} {s t u : I} {x : FreeM₂ P s t α} {g : α → FreeM₂ P t u β}
    (h₁ : x.IsTotalRollBound 1) (h₂ : ∀ y, (g y).IsTotalRollBound 2) :
    (x.bind g).IsTotalRollBound 3 :=
  FreeM₂.isTotalRollBound_bind h₁ h₂

end generic

/-! ## A continuation whose leaves are types -/

/-- One request at each Boolean state, whose Boolean answer becomes the next state. It is
reducible, so that `liftBind` trees over it are well typed at the transparency of `simp`. -/
abbrev toggle : IPFunctor.Endo Bool where
  A _ := Unit
  B _ _ := Bool
  src _ _ b := b

/-- Ask once and return the answer. -/
def ask (s : Bool) : IFreeM toggle (fun _ => Bool) s :=
  .liftBind () fun b => .pure b

/-- The answer selects a type, so the leaves move from `Type` to `Type 1`. -/
def askType (s : Bool) : IFreeM toggle (fun _ => Type) s :=
  (ask s).bind fun _ b => .pure (if b then Unit else Empty)

example (s : Bool) :
    askType s = .liftBind () fun (b : Bool) => .pure (if b then Unit else Empty) := rfl

example (s : Bool) : (ask s).IsTotalRollBound 1 := by
  simp [ask]

/-- The type-valued continuation makes no request. -/
example (s : Bool) : (askType s).IsTotalRollBound 1 :=
  IFreeM.isTotalRollBound_bind (n₁ := 1) (n₂ := 0) ⟨Nat.one_pos, fun _ => trivial⟩
    fun _ _ => trivial

/-- Erasure commutes with a universe-changing map of a genuinely indexed family. -/
example {I : Type uI} {P : Endo.{uI, uA, uB} I} {X : I → Type v}
    {Y : I → Type w} {s : I} (f : ∀ s, X s → Y s) (x : IFreeM P X s) :
    IFreeM.toSigmaFreeM P (x.imap f) =
      PFunctor.FreeM.map (fun value => (⟨value.1, f value.1 value.2⟩ : Σ s, Y s))
        (IFreeM.toSigmaFreeM P x) :=
  IFreeM.toSigmaFreeM_imap f x

end PolyFunTest.ModuleAPI.IndexedFree
