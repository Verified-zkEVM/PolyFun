/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Free.Basic

/-!
# Codes for program-tree signatures

A universe of codes, in the style of the descriptions of Chapman, Dagand, McBride and Morris
[CDMM10], for the signatures of program-tree types read by
`derive_free_sig` (`PolyFun.PFunctor.Free.DeriveSig`). A code is the data of a
signature; it has two interpretations: the polynomial functor `Code.interp c` (its container
interpretation), whose free monad `PFunctor.FreeM (Code.interp c)` is the type of program trees
over `c`, and the relational lift `Code.Rel c R` of a relation `R` on results to a relation on
program trees.

An operation code `OpCode` is a telescope of non-recursive fields followed by the type of the
directions of the operation: `field S D` binds a field of type `S` and continues with `D s`;
`dir B` ends the telescope with the direction type `B`, which may depend on all fields bound
before it. The direction is `PEmpty` for an operation without continuation, `PUnit` for a
continuation `k : T α`, and `D` for a continuation `k : D → T α`. A code `Code` is the list of
the operation codes of a signature.

## Universes

`OpCode.{u, v}` has fields in `Type u` and directions in `Type v`, and lives in
`Type (max (u + 1) (v + 1))`; its interpretation is a `PFunctor.{u, v}`. A field of a smaller
universe enters through `ULift.{u}`, and a field in `Prop` through `ULift.{u} (PLift _)`. A
field may itself be a type (`field (ULift.{1} Type) fun β => ⋯` for an operation
`sample (β : Type)`), which puts the code at `u = 1`. The results of a program tree lie in an
independent universe `Type w`.

## Main definitions

* `OpCode`, `OpCode.Pos`, `OpCode.Dir`, `OpCode.interp` — operation codes, their positions (the
  tuples of fields), their directions, and their polynomial functor;
* `Code`, `Code.interp` — signature codes and their polynomial functor, the sum of the
  operations' functors;
* `FreeRel P R` — the relational lift of `R : α → β → Prop` to `P.FreeM α → P.FreeM β → Prop`:
  the least relation relating `pure a` to `pure b` when `R a b` holds, and two nodes at the same
  position whose continuations are related at every direction;
* `Code.Rel c R` — the relational lift over the code `c`;
* `freeMCongr` — the equivalence of free monads along a lens equivalence of polynomial
  functors.

## Main results

* `freeRel_eq_iff` — the lift of equality is equality;
* `freeRel_graph_iff` — the lift of the graph of `f` is the graph of `FreeM.map f`;
* `FreeRel.bind` — the lift commutes with bind: related programs with continuations that send
  related results to related programs give related programs;
* `FreeRel.mono`, `freeRel_pure_iff`, `freeRel_liftBind_iff` — monotonicity in the relation
  and inversion at leaves and nodes;
* `freeRel_flip_iff` — the lift of the converse relation is the converse of the lift.

The monad laws of `PFunctor.FreeM (Code.interp c)` are the instance
`PFunctor.FreeM.instLawfulMonad` of cslib, which holds for every polynomial functor and so for
every code.

## References

Chapman, Dagand, McBride and Morris [CDMM10]; see `REFERENCES.md`.
-/

@[expose] public section

universe u v u' v' w w' w''

namespace PFunctor

/-! ## Codes -/

/-- The code of one operation: a telescope of fields ending in the direction type. -/
inductive OpCode : Type (max (u + 1) (v + 1)) where
  /-- A field of type `S`, followed by the rest of the telescope. -/
  | field (S : Type u) (D : S → OpCode)
  /-- The end of the telescope, with the direction type `B`. -/
  | dir (B : Type v)

namespace OpCode

/-- The positions of an operation: the tuples of its fields. -/
def Pos : OpCode.{u, v} → Type u
  | field S D => Σ s : S, Pos (D s)
  | dir _ => PUnit

/-- The directions of an operation at a tuple of its fields. -/
def Dir : (o : OpCode.{u, v}) → o.Pos → Type v
  | field _ D, ⟨s, p⟩ => Dir (D s) p
  | dir B, _ => B

/-- The polynomial functor of one operation. -/
def interp (o : OpCode.{u, v}) : PFunctor.{u, v} := ⟨o.Pos, o.Dir⟩

end OpCode

/-- The sum of the polynomial functors of a list of operations, nested to the right, with no
trailing `0` after the last operation. -/
def OpCode.sum : List OpCode.{u, v} → PFunctor.{u, v}
  | [] => 0
  | [o] => o.interp
  | o :: os => o.interp + OpCode.sum os

/-- The code of a signature: the list of the codes of its operations. -/
structure Code : Type (max (u + 1) (v + 1)) where
  /-- The codes of the operations. -/
  ops : List OpCode.{u, v}

/-- The polynomial functor of a signature code: the sum of the functors of its operations. -/
def Code.interp (c : Code.{u, v}) : PFunctor.{u, v} := OpCode.sum c.ops

/-! ## Free monads along lens equivalences -/

/-- The equivalence of free monads along a lens equivalence of their polynomial functors. -/
def freeMCongr {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} (e : P ≃ₗ Q) {α : Type w} :
    P.FreeM α ≃ Q.FreeM α where
  toFun := FreeM.mapLens e.toLens
  invFun := FreeM.mapLens e.invLens
  left_inv x := by simp only [FreeM.mapLens_mapLens, e.left_inv, FreeM.mapLens_id]
  right_inv x := by simp only [FreeM.mapLens_mapLens, e.right_inv, FreeM.mapLens_id]

/-! ## The relational lift -/

/-- The relational lift of `R : α → β → Prop` to program trees over `P`: `pure a` and `pure b`
are related when `R a b` holds, and two nodes at the same position are related when their
continuations are related at every direction. Non-recursive fields, the position, are related by
equality. -/
inductive FreeRel (P : PFunctor.{u, v}) {α : Type w} {β : Type w'} (R : α → β → Prop) :
    P.FreeM α → P.FreeM β → Prop where
  /-- Leaves with related results. -/
  | pure {a : α} {b : β} : R a b → FreeRel P R (.pure a) (.pure b)
  /-- Nodes at the same position with related continuations. -/
  | liftBind (a : P.A) {k : P.B a → P.FreeM α} {k' : P.B a → P.FreeM β} :
      (∀ d, FreeRel P R (k d) (k' d)) → FreeRel P R (.liftBind a k) (.liftBind a k')

/-- The relational lift of `R` to program trees over the code `c`. -/
abbrev Code.Rel (c : Code.{u, v}) {α : Type w} {β : Type w'} (R : α → β → Prop) :
    (Code.interp c).FreeM α → (Code.interp c).FreeM β → Prop :=
  FreeRel (Code.interp c) R

variable {P : PFunctor.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Leaves are related exactly when their results are. -/
theorem freeRel_pure_iff {R : α → β → Prop} {a : α} {b : β} :
    FreeRel P R (.pure a) (.pure b) ↔ R a b :=
  ⟨fun h => by cases h; assumption, .pure⟩

/-- Two nodes are related exactly when they have the same position and related
continuations. -/
theorem freeRel_liftBind_iff {R : α → β → Prop} {a : P.A} {k : P.B a → P.FreeM α}
    {k' : P.B a → P.FreeM β} :
    FreeRel P R (.liftBind a k) (.liftBind a k') ↔ ∀ d, FreeRel P R (k d) (k' d) :=
  ⟨fun h => by cases h; assumption, .liftBind a⟩

/-- The relational lift is monotone in the relation. -/
theorem FreeRel.mono {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) {x : P.FreeM α}
    {y : P.FreeM β} (hxy : FreeRel P R x y) : FreeRel P S x y := by
  induction hxy with
  | pure hab => exact .pure (h _ _ hab)
  | liftBind a _ ih => exact .liftBind a ih

/-- The lift of equality is equality. -/
theorem freeRel_eq_iff {x y : P.FreeM α} : FreeRel P (· = ·) x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | pure hab => rw [hab]
    | liftBind a _ ih => exact congrArg (FreeM.liftBind a) (funext ih)
  · rintro rfl
    induction x with
    | pure a => exact .pure rfl
    | lift_bind a k ih => exact .liftBind a ih

/-- The lift of the graph of `f` is the graph of `FreeM.map f`. -/
theorem freeRel_graph_iff {f : α → β} {x : P.FreeM α} {y : P.FreeM β} :
    FreeRel P (fun a b => f a = b) x y ↔ FreeM.map f x = y := by
  constructor
  · intro h
    induction h with
    | pure hab => rw [← hab]; rfl
    | liftBind a _ ih => exact congrArg (FreeM.liftBind a) (funext ih)
  · rintro rfl
    induction x with
    | pure a => exact .pure rfl
    | lift_bind a k ih => exact .liftBind a ih

/-- The relational lift commutes with bind: programs related by `R`, continued by functions
that send `R`-related results to `S`-related programs, are related by `S`. -/
theorem FreeRel.bind {γ' : Type w''} {R : α → β → Prop} {S : γ → γ' → Prop} {x : P.FreeM α}
    {y : P.FreeM β} {f : α → P.FreeM γ} {g : β → P.FreeM γ'} (hxy : FreeRel P R x y)
    (hfg : ∀ a b, R a b → FreeRel P S (f a) (g b)) :
    FreeRel P S (x.bind f) (y.bind g) := by
  induction hxy with
  | pure hab => exact hfg _ _ hab
  | liftBind a _ ih => exact .liftBind a ih

/-- The lift of the converse of `R` relates `y` to `x` when the lift of `R` relates `x` to
`y`. -/
theorem FreeRel.flip {R : α → β → Prop} {x : P.FreeM α} {y : P.FreeM β}
    (h : FreeRel P R x y) : FreeRel P (fun b a => R a b) y x := by
  induction h with
  | pure hab => exact .pure hab
  | liftBind a _ ih => exact .liftBind a ih

/-- The lift of the converse relation is the converse of the lift. -/
theorem freeRel_flip_iff {R : α → β → Prop} {x : P.FreeM α} {y : P.FreeM β} :
    FreeRel P (fun b a => R a b) y x ↔ FreeRel P R x y :=
  ⟨fun h => h.flip, fun h => h.flip⟩

end PFunctor

end
