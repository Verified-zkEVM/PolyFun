/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Free.DeriveSig
public import PolyFun.PFunctor.Free.CodeRel
public import PolyFun.PFunctor.Free.Quotient
public import PolyFun.PFunctor.Free.WP.Cost

/-!
# Codes, `derive_free_sig`, the cost fold and free monads modulo a theory

`derive_free_sig` runs on two program-tree types with the option `(code := true)`: a tree type
whose parameters precede the result type, with its bind, and a tree type in `Type 1` with a type
field, an instance field, a proof field, dependent directions and an operation without fields.
It also runs on a result type in a universe of its own, on a universe declared by `universe`, on
instance-implicit, implicit and strict-implicit parameters, and on a type with only a return
constructor. The remaining examples pin the relational lift over a generated code, the cost fold
and the lawful monad of a free monad modulo an equational theory.
-/

@[expose] public section

namespace PolyFunTest.FreeCodes

open PFunctor

/-! ## Parameters before the result type, with a bind -/

/-- Programs that ask questions of type `Q`, receive answers of type `R`, and may fail. -/
inductive Ask (Q R : Type) (α : Type) : Type where
  /-- Return a value. -/
  | ret (a : α)
  /-- Ask a question and continue with its answer. -/
  | ask (q : Q) (k : R → Ask Q R α)
  /-- Fail. -/
  | fail

/-- The bind of `Ask`. -/
def Ask.bind {Q R α β : Type} : Ask Q R α → (α → Ask Q R β) → Ask Q R β
  | .ret a, f => f a
  | .ask q k, f => .ask q fun r => (k r).bind f
  | .fail, _ => .fail

derive_free_sig Ask (namespace := AskGen) (bind := Ask.bind) (code := true)

/-- The generated equivalence of `Ask` with the free monad over its code. -/
example (Q R α : Type) : Ask Q R α ≃ FreeM (Code.interp (AskGen.code Q R)) α :=
  AskGen.equivCode

/-- The generated equivalence of `Ask` with the free monad over its signature. -/
example (Q R α : Type) : Ask Q R α ≃ FreeM (AskGen.Sig Q R) α :=
  AskGen.equivFreeM

/-- The relational lift over the code of `Ask` of equality is equality. -/
example (Q R α : Type) (x y : FreeM (Code.interp (AskGen.code Q R)) α) :
    Code.Rel (AskGen.code Q R) (· = ·) x y ↔ x = y :=
  freeRel_eq_iff

/-! ## A type in `Type 1` with operations without fields -/

/-- A program-tree type in `Type 1`: a type field with an `Inhabited` instance and a `Nonempty`
proof, a dependent direction `Fin (n + 1)`, a direction `PUnit` and an operation without
fields or continuation. -/
inductive Pick (α : Type) : Type 1 where
  /-- Return a value. -/
  | ret (a : α)
  /-- Choose an element of an inhabited type. -/
  | pick (β : Type) [Inhabited β] (h : Nonempty β) (k : β → Pick α)
  /-- Draw an element of `Fin (n + 1)`. -/
  | roll (n : Nat) (k : Fin (n + 1) → Pick α)
  /-- A step with one continuation. -/
  | tick (k : Pick α)
  /-- Stop. -/
  | stop

derive_free_sig Pick (namespace := PickGen) (code := true)

/-- The generated signature of `Pick` is the sum of its summands. -/
example : PFunctor.Equiv PickGen.Sig PickGen.SigSum := PickGen.sigEquivSum

/-- The summand of an operation without fields has positions in the universe of the signature. -/
example : PFunctor.{1, 0} := PickGen.Sig.stop

/-- The generated equivalence of `Pick` with the free monad over its code. -/
example (α : Type) : Pick α ≃ FreeM (Code.interp PickGen.code) α :=
  PickGen.equivCode

/-! ## A result type in a universe of its own -/

/-- Programs over a result type in an arbitrary universe; the operations do not mention it. -/
inductive Guess (α : Type*) : Type _ where
  /-- Return a value. -/
  | ret (a : α)
  /-- Draw a number below `n` and continue with it. -/
  | guess (n : Nat) (k : Fin n → Guess α)
  /-- Fail. -/
  | fail

derive_free_sig Guess (code := true)

/-- The signature of `Guess` takes no universe parameter. -/
example : PFunctor.{0, 0} := Guess.Sig

/-- The generated equivalence of `Guess` at a result type in `Type 2`. -/
example (α : Type 2) : Guess α ≃ FreeM Guess.Sig α := Guess.equivFreeM

/-! ## A universe declared by `universe` -/

universe v

/-- Programs whose operations choose an element of a type in the declared universe `v`. -/
inductive Choose (α : Type v) : Type (v + 1) where
  /-- Return a value. -/
  | ret (a : α)
  /-- Choose an element of `β`. -/
  | choose (β : Type v) (k : β → Choose α)
  /-- A step with one continuation. -/
  | step (k : Choose α)

derive_free_sig Choose (code := true)

/-- The signature of `Choose` at the declared universe `v`. -/
example : PFunctor.{v + 1, v} := Choose.Sig.{v}

/-- The generated equivalence of `Choose` with the free monad over its code. -/
example (α : Type v) : Choose α ≃ FreeM (Code.interp Choose.code) α := Choose.equivCode

/-! ## Instance-implicit, implicit and strict-implicit parameters -/

/-- Programs that ask questions of an inhabited type `Q` and receive answers of type `R`. -/
inductive Quiz (Q : Type) [Inhabited Q] {R : Type} ⦃S : Type⦄ (α : Type) : Type where
  /-- Return a value. -/
  | ret (a : α)
  /-- Ask a question and continue with its answer. -/
  | ask (q : Q) (k : R → @Quiz Q _ R S α)
  /-- Report a value of `S`. -/
  | report (s : S) (k : @Quiz Q _ R S α)

/-- The bind of `Quiz`. -/
def Quiz.bind {Q : Type} [Inhabited Q] {R S α β : Type} :
    @Quiz Q _ R S α → (α → @Quiz Q _ R S β) → @Quiz Q _ R S β
  | .ret a, f => f a
  | .ask q k, f => .ask q fun r => (k r).bind f
  | .report s k, f => .report s (k.bind f)

derive_free_sig Quiz (namespace := QuizGen) (bind := Quiz.bind) (code := true)

/-- The generated equivalence of `Quiz` with the free monad over its signature. -/
example (Q R S α : Type) [Inhabited Q] :
    @Quiz Q _ R S α ≃ FreeM (@QuizGen.Sig Q _ R S) α :=
  QuizGen.equivFreeM

/-! ## Only a return constructor -/

/-- Programs with no operation. -/
inductive Done (α : Type) : Type where
  /-- Return a value. -/
  | ret (a : α)

/-- The bind of `Done`. -/
def Done.bind {α β : Type} : Done α → (α → Done β) → Done β
  | .ret a, f => f a

derive_free_sig Done (namespace := DoneGen) (bind := Done.bind) (code := true)

/-- The signature of `Done` has no operation. -/
example : IsEmpty DoneGen.Sig.A := ⟨nofun⟩

/-- The generated equivalence of `Done` with the free monad over its code. -/
example (α : Type) : Done α ≃ FreeM (Code.interp DoneGen.code) α := DoneGen.equivCode

/-! ## The cost fold -/

/-- A polynomial functor with one operation and two answers. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- Two queries cost two at the unit charge. -/
example : FreeM.cost (P := coinP) (fun _ => 1)
    (FreeM.liftBind PUnit.unit fun _ => FreeM.liftBind PUnit.unit fun b => FreeM.pure b) = 2 := by
  simp only [FreeM.cost_liftBind, FreeM.pure_eq_pure, FreeM.cost_pure, ciSup_const, add_zero]
  exact one_add_one_eq_two

/-- Programs related by the relational lift have the same cost. -/
example {α β : Type} (R : α → β → Prop) (χ : coinP.A → ℕ) (x : coinP.FreeM α)
    (y : coinP.FreeM β) (h : FreeRel coinP R x y) : FreeM.cost χ x = FreeM.cost χ y :=
  h.cost_eq χ

/-! ## Free monads modulo a theory -/

/-- The free monad modulo a theory is a lawful monad. -/
example (T : EqTheory.{0, 0, 0} coinP) : LawfulMonad (QFreeM T) := inferInstance

end PolyFunTest.FreeCodes
