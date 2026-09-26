/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Logic.Equiv.Prod

/-! # Comonads

A `Comonad` provides `Functor`, `Extract`, and `Extend`; `LawfulComonad`
states the counit, coassociativity, and map-compatibility laws. This is the
functional presentation of a comonad. Nesting via `duplicate` requires an
endofunctor; the extraction/extension interface permits a context functor
between different universes.

`Coapplicative` chooses a pairing of contexts; `LawfulCoapplicative` requires
associativity and naturality. It is not the categorical dual of `Applicative`, and a comonad does
not choose such a pairing. For example, streams can pair pointwise or preserve
the left context while extracting a single value from the right. The pairing
classes carry no law relating `extract` to `coseq`.

A consumer combining extension and pairing can request `[Comonad w] [Coseq w]`.
Two independent assumptions `[Comonad w] [Coapplicative w]` may select different
functor and extraction data; they do not assert that the shared operations agree.

-/

@[expose] public section

universe u v

/-- The `Extract` typeclass provides the `extract` operation, dual to `Pure.pure`. -/
class Extract (w : Type u → Type v) where
  /-- Extract a value from the comonadic context. -/
  extract {α : Type u} : w α → α

/-- The `Extend` typeclass provides the `extend` operation, dual to `Bind.bind`. -/
class Extend (w : Type u → Type v) where
  /-- Extend a function across the comonadic context. -/
  extend {α β : Type u} : w α → (w α → β) → w β

/-- Pair values in two contexts using a chosen combination of their structure. -/
class Coseq (w : Type u → Type v) where
  /-- Combine two comonadic contexts. -/
  coseq : {α β : Type u} → w α → w β → w (α × β)

/-- Combine two contexts and retain the first result. -/
class CoseqLeft (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the first result. -/
  coseqLeft : {α β : Type u} → w α → w β → w α

/-- Combine two contexts and retain the second result. -/
class CoseqRight (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the second result. -/
  coseqRight : {α β : Type u} → w α → w β → w β

export Extract (extract)
export Extend (extend)
export Coseq (coseq)
export CoseqLeft (coseqLeft)
export CoseqRight (coseqRight)

namespace Comonad

/-- Cosequencing `Coseq.coseq`, pairing two comonadic contexts; activate it with
`open scoped Comonad`. -/
scoped infixl:60 " <@> " => Coseq.coseq
/-- Left cosequencing `CoseqLeft.coseqLeft`, keeping the left context's result; activate it with
`open scoped Comonad`. -/
scoped infixl:60 " <@ "  => CoseqLeft.coseqLeft
/-- Right cosequencing `CoseqRight.coseqRight`, keeping the right context's result; activate it
with `open scoped Comonad`. -/
scoped infixl:60 " @> "  => CoseqRight.coseqRight

end Comonad

open scoped Comonad

/-- A functor with extraction and a chosen pairing of contexts. -/
class Coapplicative (w : Type u → Type v) extends
    Functor w, Extract w, Coseq w, CoseqLeft w, CoseqRight w where
  /-- Default implementation for `coseqLeft` using `coseq` and `map`. -/
  coseqLeft wa wb := Functor.map Prod.fst (coseq wa wb)
  /-- Default implementation for `coseqRight` using `coseq` and `map`. -/
  coseqRight wa wb := Functor.map Prod.snd (coseq wa wb)

/-- A comonad in terms of extraction and extension of context-dependent functions. -/
class Comonad (w : Type u → Type v) extends Functor w, Extract w, Extend w where
  /-- Mapping obtained by extending a function of the extracted value. -/
  map f wa := extend wa (f ∘ extract)

/-! ## Lawful hierarchy -/

/-- Functor laws and associativity/naturality of the chosen context pairing. -/
class LawfulCoapplicative (w : Type u → Type v) [Coapplicative w] extends LawfulFunctor w where
  /-- Ensure default `coseqLeft` law holds even if overridden. -/
  coseqLeft_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    @coseqLeft w _ α β wa wb = Functor.map (@Prod.fst α β) (coseq wa wb)
  /-- Ensure default `coseqRight` law holds even if overridden. -/
  coseqRight_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    coseqRight wa wb = Functor.map (@Prod.snd α β) (coseq wa wb)
  /-- Associativity law for `coseq`. `assoc` maps `(α × β) × γ` to `α × (β × γ)`. -/
  coseq_assoc : ∀ {α β γ : Type u} (wa : w α) (wb : w β) (wc : w γ),
    Functor.map (Equiv.prodAssoc α β γ) (coseq (coseq wa wb) wc) = coseq wa (coseq wb wc)
  /-- Naturality of `coseq` in both arguments. -/
  map_coseq : ∀ {α β α' β' : Type u} (f : α → α') (g : β → β')
    (wa : w α) (wb : w β),
    Functor.map (fun p : α × β => (f p.1, g p.2)) (coseq wa wb) =
      coseq (Functor.map f wa) (Functor.map g wb)

export LawfulCoapplicative (coseqLeft_eq coseqRight_eq coseq_assoc map_coseq)

/-- Lawful `Comonad`. Dual to `LawfulMonad`. -/
class LawfulComonad (w : Type u → Type v) [Comonad w] extends LawfulFunctor w where
  /-- Compatibility between `map` and `extend`/`extract`.
      Since `Comonad.map` defines map this way, this law ensures the `Functor` instance
      used by `LawfulFunctor` is consistent. -/
  map_eq_extend_extract : ∀ {α β : Type u} (f : α → β) (wa : w α),
    Functor.map f wa = extend wa (f ∘ extract)
  /-- Extending with `extract` is the identity (Left identity dual). -/
  extend_extract : ∀ {α : Type u} (wa : w α), extend wa (@extract w _ α) = wa
  /-- Extracting after extending yields the original function application (Right identity dual). -/
  extract_extend : ∀ {α β : Type u} (wa : w α) (f : w α → β),
    extract (extend wa f) = f wa
  /-- Extend is associative (Associativity dual). -/
  extend_assoc : ∀ {α β γ : Type u} (wa : w α) (f : w α → β) (g : w β → γ),
    extend (extend wa f) g = extend wa (fun w'a => g (extend w'a f))

export LawfulComonad (map_eq_extend_extract extend_extract extract_extend extend_assoc)

/-! ## Theorems derived from lawful classes -/

section LawfulnessProofs
variable {w : Type u → Type v} [Comonad w] [LawfulComonad w]

theorem comonad_id_map {α : Type u} (wa : w α) : Functor.map id wa = wa :=
  id_map wa

@[simp] theorem comonad_comp_map {α β γ : Type u} (f : β → γ) (g : α → β) (wa : w α) :
    Functor.map (f ∘ g) wa = Functor.map f (Functor.map g wa) :=
  comp_map g f wa

@[simp] theorem extract_map {α β : Type u} (f : α → β) (wa : w α) :
    extract (Functor.map f wa) = f (extract wa) := by
  rw [map_eq_extend_extract, extract_extend, Function.comp_apply]

end LawfulnessProofs

/-! ## Duplicate and derived laws

These require `w : Type u → Type u`, so the comonadic context can be nested. -/

section Duplicate
variable {w : Type u → Type u} [Comonad w]

/-- Duplicate the comonadic context. Defined via `extend`. -/
@[simp]
def duplicate {α : Type u} (wa : w α) : w (w α) :=
  extend wa id

variable [LawfulComonad w]
variable {α : Type u} (wa : w α)

theorem extract_duplicate_eq_id : extract (duplicate wa) = wa :=
  extract_extend wa id

theorem map_extract_duplicate_eq_id : Functor.map extract (duplicate wa) = wa := by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]
  rw [extend_extract]

theorem extend_eq_map_duplicate {β : Type u} (f : w α → β) :
    extend wa f = Functor.map f (duplicate wa) := by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]

theorem duplicate_duplicate_eq_map_duplicate :
    duplicate (duplicate wa) = Functor.map duplicate (duplicate wa) := by
  have h_lhs : duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, duplicate, extend_assoc]
    simp only [id_def]
    rfl
  have h_rhs : Functor.map duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, map_eq_extend_extract, extend_assoc]
    simp only [Function.comp_apply, extract_extend, id_def]
  rw [h_lhs, h_rhs]

end Duplicate
