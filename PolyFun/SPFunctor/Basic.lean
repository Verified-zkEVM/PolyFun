/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Indexed
public import PolyFun.PFunctor.Free.Basic

/-!
# Stateful/Dependent Polynomial Functors

This file defines a generalization `IPFunctor I` that generalizes `PFunctor` with a mechanism
for gating the available head types given some ambient state `I`.
This allows semantic requirements about interaction to be enforced at the type level.

Can be used to model things like a multi-phase game where the oracles change after the adversary
calls an initially available challenge oracle, or multiple parties handing off control in execution.

Also defines the type `IPFunctor.FreeM` of free monads over indexed polynomial functors.
Pure return values are allowed in any ambient state. The available head shapes at each `roll` are
gated by the current ambient state, and the state for the continuation function is the result of
applying `st` to the input to the continuation.
This type is not actually a `Monad`, but can be used to enforce query ordering on a `PFunctor.FreeM`
at the syntactic level, to control the allowable sequencing of oracle calls.
This representation naturally gains the universe level bump that `PFunctor.FreeM` doesn't
-/

@[expose] public section

/-- Indexed version of `PFunctor`, with some global state of type `I` gating the available shapes.
Given a state `s : I`, `A s` are the available shapes and `B s` maps `A s` to output types.
The function `st` specifies how the state transations on a input output pair. -/
structure IPFunctor (I : Type*) where
  /-- The head type -/
  A : I → Type*
  /-- The child family of types -/
  B : (s : I) → A s → Type*
  /-- State transition function -/
  st : (s : I) → (a : A s) → B s a → I
  deriving Inhabited

namespace IPFunctor

variable {I α β γ : Type*}

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (P : IPFunctor I) (α : Type*) (s : I) : Type _ :=
  Σ x : P.A s, P.B s x → α

instance : CoeFun (IPFunctor I) (fun _ => Type _ → (I → Type _)) where
  coe := Obj (I := I)

instance (I) : Zero (IPFunctor I) where
  zero := { A _ := PEmpty, B _ _ := PEmpty, st _ _ := PEmpty.elim }

instance (I) : One (IPFunctor I) where
  one := { A _ := PUnit, B _ _ := PEmpty, st _ _ := PEmpty.elim }

/-- View an `IPFunctor` as a `PFunctor` using the default element of the index type. -/
@[reducible, inline]
def toPFunctor [Inhabited I] (P : IPFunctor I) : PFunctor where
  A := P.A default; B := P.B default

/-- The free monad on a polynomial stateful polynomial functor, analogous to `PFunctor.FreeMonad`
but allows the set of available oracles to change in response to previous queries. -/
inductive FreeM (P : IPFunctor I) : I → Type* → Type _
  /-- A pure return value of `x` with current ambient state `s`. -/
  | pure (s : I) {α} (x : α) : FreeM P s α
  /-- Roll a value in the current set of shapes into a continuation with updated state. -/
  | roll (s : I) {α} (x : P.A s) (r : (b : P.B s x) → FreeM P (P.st s x b) α) : FreeM P s α

namespace FreeM

instance (P : IPFunctor I) (s : I) : Pure (P.FreeM s) where
  pure := .pure s

protected def map {P : IPFunctor I} (s : I) (f : α → β) : P.FreeM s α → P.FreeM s β
  | .pure s x => pure s (f x)
  | .roll s x r => roll s x fun y => FreeM.map (P.st s x y) f (r y)

/-- While we can't define a `Monad` instance due to changing state, we can define a `Functor`
operation since the additional mapping doesn't affect the monadic context in any way. -/
instance {P : IPFunctor I} (s : I) : Functor (P.FreeM s) where
  map := .map s

instance {P : IPFunctor I} (s : I) : LawfulFunctor (P.FreeM s) where
  map_const := rfl
  id_map x := by
    induction x with
    | pure s x => simp [Functor.map, FreeM.map]
    | roll s x r h => simpa [Functor.map, FreeM.map, funext_iff] using h
  comp_map := by

    sorry

section erase

/-- Remove all indexing information from a `IPFunctor.FreeM` to get a `PFunctor.FreeM`.
This is the natural forgetful functor and factors through almost every construction,
allowing reasonable simplification lemmas. -/
def erase {I} [Unique I] (P : IPFunctor I) (s : I) {α} :
    P.FreeM s α → P.toPFunctor.FreeM α
  | .pure s x => PFunctor.FreeM.pure x
  | .roll s x r => PFunctor.FreeM.roll (Unique.eq_default s ▸ x : P.A default)
      fun y => erase P _ <| r (Unique.eq_default s ▸ y)

def defaultAnnotate {I} [Unique I] (P : IPFunctor I) (s : I) {α} :
    P.toPFunctor.FreeM α → P.FreeM s α
  | .pure x => Unique.eq_default s ▸ IPFunctor.FreeM.pure default x
  | .roll x r => sorry

end erase

/-- With a trivial indexing set the free monad is equivalent to that of the default `PFunctor`. -/
def equiv_PFunctor_freeM {I} [Unique I] (P : IPFunctor I) (s : I) {α} :
    FreeM P s α ≃ PFunctor.FreeM P.toPFunctor α where
  toFun := erase P s
  invFun := defaultAnnotate P s
  left_inv x := by
    sorry
  right_inv := by
    sorry

variable {I : Type*} (P : IPFunctor I) {α β : Type*}

/-- Bind operator on `FreeM P` operation used in the monad definition.
Note this doesn't satisfy the definition of `Monad.bind` as the second arg must handle all states.
This still works with `do` notation in the expected ways via custom elaborators. -/
@[always_inline, inline]
protected def bind (s : I) : FreeM P s α →
    (g : (s' : I) → α → FreeM P s' β) → FreeM P s β
  | FreeM.pure s x, g => g s x
  | FreeM.roll s x r, g => FreeM.roll s x (fun u ↦ FreeM.bind (P.st s x u) (r u) g)

end FreeM

end IPFunctor
