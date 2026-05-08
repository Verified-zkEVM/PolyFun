/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# UC composition notation

Scoped notation for open-system boundaries and the free composition syntax.
All notation is scoped to `Interaction.UC`; use `open Interaction.UC`
to bring it into scope.

## Typeclasses

The notation is backed by three typeclasses (`HasPar`, `HasWire`, `HasPlug`)
with instances for `Raw`, `Expr`, and `Interp`. Each instance is accompanied
by a `@[simp]` bridge lemma that normalizes the typeclass method back to
the concrete operation, ensuring that existing simp lemmas (e.g.,
`interpret_par`, `interpret_wire`) continue to fire on notation-introduced
terms.

## Boundary-level

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `Δ₁ ⊗ᵇ Δ₂` | `PortBoundary.tensor Δ₁ Δ₂` | `\otimes ^b` |
| `Δᵛ` | `PortBoundary.swap Δ` (dual) | `\^v` |

## Expression-level

| Notation | Meaning | Precedence |
|----------|---------|------------|
| `e₁ ∥ e₂` | `HasPar.par e₁ e₂` (parallel) | 70, right |
| `e₁ ⊞ e₂` | `HasWire.wire e₁ e₂` (wire) | 65, right |
| `e ⊠ k` | `HasPlug.plug e k` (plug/close) | 60, right |

## Parsing rules

Precedence ensures natural parenthesization:
* `A ∥ B ∥ C` = `A ∥ (B ∥ C)` (right-associative)
* `A ∥ B ⊞ C` = `(A ∥ B) ⊞ C` (par binds tighter than wire)
* `A ⊞ B ⊠ C` = `(A ⊞ B) ⊠ C` (wire binds tighter than plug)
* `A ∥ B ⊞ C ∥ D ⊠ E` = `((A ∥ B) ⊞ (C ∥ D)) ⊠ E`
* `Γᵛ ⊗ᵇ Δ` = `tensor (swap Γ) Δ` (postfix `ᵛ` at max precedence)
* `(Δ₁ ⊗ᵇ Δ₂)ᵛ` = `swap (tensor Δ₁ Δ₂)` (parentheses required)
-/

namespace Interaction.UC

/-! ### Boundary-level notation -/

/-- Tensor (parallel) of port boundaries: `Δ₁ ⊗ᵇ Δ₂`. -/
scoped infixr:70 " ⊗ᵇ " => PortBoundary.tensor

/-- Dual (swap) of a port boundary: `Δᵛ` means `PortBoundary.swap Δ`.

The superscript v (typed `\^v`) visually suggests "flip" or "invert,"
matching the operation that swaps inputs and outputs. Avoids the
Mathlib-global `ᵒᵖ` (which denotes `Opposite`). -/
scoped notation:max Δ "ᵛ" => PortBoundary.swap Δ

/-! ### Composition typeclasses -/

/-- Parallel composition on boundary-indexed types. -/
class HasPar (F : PortBoundary → Type*) where
  par : {Δ₁ Δ₂ : PortBoundary} → F Δ₁ → F Δ₂ → F (PortBoundary.tensor Δ₁ Δ₂)

/-- Wiring (partial internal connection) on boundary-indexed types. -/
class HasWire (F : PortBoundary → Type*) where
  wire : {Δ₁ Γ Δ₂ : PortBoundary} →
    F (PortBoundary.tensor Δ₁ Γ) →
    F (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) →
    F (PortBoundary.tensor Δ₁ Δ₂)

/-- Plugging (full closure) on boundary-indexed types. -/
class HasPlug (F : PortBoundary → Type*) where
  plug : {Δ : PortBoundary} →
    F Δ → F (PortBoundary.swap Δ) → F PortBoundary.empty

/-! ### Notation -/

/-- Parallel composition: `e₁ ∥ e₂`. -/
scoped infixr:70 " ∥ " => HasPar.par

/-- Wiring: `e₁ ⊞ e₂`. -/
scoped infixr:65 " ⊞ " => HasWire.wire

/-- Plug (full closure): `e ⊠ k`. -/
scoped infixr:60 " ⊠ " => HasPlug.plug

/-! ### Instances and bridge lemmas for `Raw` -/

namespace OpenSyntax.Raw

instance {Atom : PortBoundary → Type*} : HasPar (Raw Atom) where
  par := Raw.par

instance {Atom : PortBoundary → Type*} : HasWire (Raw Atom) where
  wire := Raw.wire

instance {Atom : PortBoundary → Type*} : HasPlug (Raw Atom) where
  plug := Raw.plug

variable {Atom : PortBoundary → Type*}
variable {Δ₁ Δ₂ Γ : PortBoundary}

@[simp]
theorem hasPar (e₁ : Raw Atom Δ₁) (e₂ : Raw Atom Δ₂) :
    HasPar.par e₁ e₂ = Raw.par e₁ e₂ := rfl

@[simp]
theorem hasWire (e₁ : Raw Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Raw Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Raw.wire e₁ e₂ := rfl

@[simp]
theorem hasPlug (e : Raw Atom Δ₁)
    (k : Raw Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Raw.plug e k := rfl

end OpenSyntax.Raw

/-! ### Instances and bridge lemmas for `Expr` -/

namespace OpenSyntax.Expr

instance {Atom : PortBoundary → Type*} : HasPar (Expr Atom) where
  par := Expr.par

instance {Atom : PortBoundary → Type*} : HasWire (Expr Atom) where
  wire := Expr.wire

instance {Atom : PortBoundary → Type*} : HasPlug (Expr Atom) where
  plug := Expr.plug

variable {Atom : PortBoundary → Type*}
variable {Δ₁ Δ₂ Γ : PortBoundary}

@[simp]
theorem hasPar (e₁ : Expr Atom Δ₁) (e₂ : Expr Atom Δ₂) :
    HasPar.par e₁ e₂ = Expr.par e₁ e₂ := rfl

@[simp]
theorem hasWire (e₁ : Expr Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Expr.wire e₁ e₂ := rfl

@[simp]
theorem hasPlug (e : Expr Atom Δ₁)
    (k : Expr Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Expr.plug e k := rfl

end OpenSyntax.Expr

/-! ### Instances and bridge lemmas for `Interp` -/

namespace OpenSyntax.Interp

instance {Atom : PortBoundary → Type*} : HasPar (Interp Atom) where
  par := Interp.par

instance {Atom : PortBoundary → Type*} : HasWire (Interp Atom) where
  wire := Interp.wire

instance {Atom : PortBoundary → Type*} : HasPlug (Interp Atom) where
  plug := Interp.plug

variable {Atom : PortBoundary → Type*}
variable {Δ₁ Δ₂ Γ : PortBoundary}

@[simp]
theorem hasPar (e₁ : Interp Atom Δ₁) (e₂ : Interp Atom Δ₂) :
    HasPar.par e₁ e₂ = Interp.par e₁ e₂ := rfl

@[simp]
theorem hasWire (e₁ : Interp Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Interp Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Interp.wire e₁ e₂ := rfl

@[simp]
theorem hasPlug (e : Interp Atom Δ₁)
    (k : Interp Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Interp.plug e k := rfl

end OpenSyntax.Interp

/-! ### Verification

The following examples verify correct elaboration, precedence, and
that bridge lemmas fire correctly with `simp`. -/

section Tests

open Interaction.UC

variable {Atom : PortBoundary → Type*}
variable {Δ₁ Δ₂ Δ₃ Γ : PortBoundary}

-- Boundary notation
example : Δ₁ ⊗ᵇ Δ₂ = PortBoundary.tensor Δ₁ Δ₂ := rfl
example : Γᵛ = PortBoundary.swap Γ := rfl
example : Γᵛ ⊗ᵇ Δ₂ = PortBoundary.tensor (PortBoundary.swap Γ) Δ₂ := rfl
example : Δ₁ ⊗ᵇ Δ₂ᵛ = PortBoundary.tensor Δ₁ (PortBoundary.swap Δ₂) := rfl

-- Raw notation: bridge lemmas normalize to concrete constructors
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Δ₂) :
    A ∥ B = OpenSyntax.Raw.par A B := by simp
example (A : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Γ))
    (B : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂)) :
    A ⊞ B = OpenSyntax.Raw.wire A B := by simp
example (A : OpenSyntax.Raw Atom Δ₁)
    (K : OpenSyntax.Raw Atom Δ₁ᵛ) :
    A ⊠ K = OpenSyntax.Raw.plug A K := by simp

-- Expr notation
example (A : OpenSyntax.Expr Atom Δ₁) (B : OpenSyntax.Expr Atom Δ₂) :
    A ∥ B = OpenSyntax.Expr.par A B := by simp

-- Interp notation
example (A : OpenSyntax.Interp Atom Δ₁) (B : OpenSyntax.Interp Atom Δ₂) :
    A ∥ B = OpenSyntax.Interp.par A B := by simp

-- Precedence: par (70) binds tighter than wire (65)
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Γ)
    (C : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂)) :
    A ∥ B ⊞ C = (A ∥ B) ⊞ C := rfl

-- Precedence: wire (65) binds tighter than plug (60)
example (A : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Γ))
    (B : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂))
    (K : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Δ₂)ᵛ) :
    A ⊞ B ⊠ K = (A ⊞ B) ⊠ K := rfl

-- Right-associativity
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Δ₂)
    (C : OpenSyntax.Raw Atom Δ₃) :
    A ∥ B ∥ C = A ∥ (B ∥ C) := rfl

end Tests

end Interaction.UC
