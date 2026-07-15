/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.M

/-!
# Coinductive resumptions over polynomial interfaces

A `Resumption p β` is a possibly infinite, tau-free computation that either
returns a value in `β` or exposes a visible query from `p` and continues from
the selected direction. It is the M-type of the return-or-query polynomial
`C β + p`, the coinductive counterpart of `FreeM p β`.

This module provides only the foundational one-step interface. Functorial and
monadic structure, finite-program embeddings, and interaction-tree semantics
can be layered on this canonical M-type representation.
-/

@[expose] public section

universe uA uB uβ uX uY

namespace PFunctor

/-- A possibly infinite, tau-free computation that returns a `β` or performs a
visible query from `p`. -/
abbrev Resumption (p : PFunctor.{uA, uB}) (β : Type uβ) :=
  M.{max uβ uA, uB} (C.{uβ, uB} β + p)

namespace Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ}

/-! ## One-step views -/

/-- Reassociate the extension of `C β + p` into the computational
return-or-query view. -/
def unpack {X : Type uX} : (C.{uβ, uB} β + p).Obj X → β ⊕ p.Obj X
  | ⟨Sum.inl value, _⟩ => Sum.inl value
  | ⟨Sum.inr position, next⟩ => Sum.inr ⟨position, next⟩

/-- Repack a computational return-or-query view as an extension of `C β + p`. -/
def pack {X : Type uX} : β ⊕ p.Obj X → (C.{uβ, uB} β + p).Obj X
  | Sum.inl value => ⟨Sum.inl value, PEmpty.elim⟩
  | Sum.inr ⟨position, next⟩ => ⟨Sum.inr position, next⟩

@[simp] theorem pack_inl {X : Type uX} (value : β) :
    pack (p := p) (X := X) (Sum.inl value) = ⟨Sum.inl value, PEmpty.elim⟩ := rfl

@[simp] theorem pack_inr {X : Type uX} (position : p.A) (next : p.B position → X) :
    pack (Sum.inr ⟨position, next⟩ : β ⊕ p.Obj X) = ⟨Sum.inr position, next⟩ := rfl

@[simp] theorem unpack_pack {X : Type uX} (step : β ⊕ p.Obj X) :
    unpack (pack step) = step := by
  cases step with
  | inl _ => rfl
  | inr step => rcases step with ⟨_, _⟩; rfl

@[simp] theorem pack_unpack {X : Type uX} (step : (C.{uβ, uB} β + p).Obj X) :
    pack (unpack step) = step := by
  rcases step with ⟨shape, next⟩
  cases shape with
  | inl value =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext direction
        exact PEmpty.elim direction
  | inr position => rfl

/-- The extension of `C β + p` is equivalent to the computational
return-or-query view. -/
def viewEquiv {X : Type uX} : (C.{uβ, uB} β + p).Obj X ≃ β ⊕ p.Obj X where
  toFun := unpack
  invFun := pack
  left_inv := pack_unpack
  right_inv := unpack_pack

@[simp] theorem unpack_map {X : Type uX} {Y : Type uY} (f : X → Y)
    (step : (C.{uβ, uB} β + p).Obj X) :
    unpack ((C.{uβ, uB} β + p).map f step) =
      Sum.map (fun value : β => value) (p.map f) (unpack step) := by
  rcases step with ⟨shape, next⟩
  cases shape <;> rfl

/-! ## Constructors, destructor, and corecursor -/

/-- A resumption that immediately returns `value`. -/
def pure (value : β) : Resumption p β :=
  M.mk (pack (Sum.inl value))

/-- A resumption that exposes `position` and continues according to the
selected direction. -/
def query (position : p.A) (next : p.B position → Resumption p β) : Resumption p β :=
  M.mk (pack (Sum.inr ⟨position, next⟩))

/-- Observe whether a resumption returns or performs a visible query. -/
def dest (computation : Resumption p β) : β ⊕ p.Obj (Resumption p β) :=
  unpack (M.dest computation)

@[simp] theorem pack_dest (computation : Resumption p β) :
    pack (dest computation) = M.dest computation :=
  pack_unpack _

/-- The computational destructor is injective, just as the underlying
M-type destructor is. -/
theorem eq_of_dest_eq {left right : Resumption p β} (h : dest left = dest right) :
    left = right := by
  apply M.eq_of_dest_eq
  rw [← pack_dest left, ← pack_dest right, h]

@[simp] theorem dest_inj {left right : Resumption p β} :
    dest left = dest right ↔ left = right :=
  ⟨eq_of_dest_eq, fun h => h ▸ rfl⟩

/-- Build a resumption from a return-or-query coalgebra. -/
def corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) : Resumption p β :=
  M.corec (fun state => pack (step state)) seed

@[simp] theorem dest_pure (value : β) : dest (pure (p := p) value) = Sum.inl value := by
  simp only [dest, pure, M.dest_mk, unpack_pack]

@[simp] theorem dest_query (position : p.A) (next : p.B position → Resumption p β) :
    dest (query position next) = Sum.inr ⟨position, next⟩ := by
  simp only [dest, query, M.dest_mk, unpack_pack]

@[simp] theorem dest_corec {X : Type uX} (step : X → β ⊕ p.Obj X) (seed : X) :
    dest (corec step seed) =
      Sum.map (fun value : β => value) (p.map (corec step)) (step seed) := by
  unfold dest corec
  rw [M.dest_corec, unpack_map, unpack_pack]

/-- Corecursing from the destructor reconstructs the original resumption. -/
@[simp] theorem corec_dest (computation : Resumption p β) :
    corec dest computation = computation := by
  unfold corec
  have hstep : (fun state : Resumption p β => pack (dest state)) = M.dest := by
    funext state
    exact pack_dest state
  rw [hstep]
  exact M.corec_dest computation

end Resumption

end PFunctor
