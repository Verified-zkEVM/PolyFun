/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import PolyFun.IPFunctor.Scoped.Sum

/-!
# Syntax of the cost language D

D is a typed call-by-value λ-calculus with ground data, primitive operations, bounded iteration
and the calls of an interface. Its cost model is that of the weak call-by-value λ-calculus of
Forster and Kunze: time is the number of β-steps, extended with primitive operations and with the
calls of the interface.

The ground types and the primitive operations are a parameter (`Ground`): a type `G` of codes, a
denotation `den : G → Type u` and primitive operations `Prim g h` from `den g` to `den h`. The
types of D (`Ty`) are the codes of `G`, `unit`, `nat`, products, sums and function types. They are
the sorts of a typed binding signature.

The syntax of D is the sum (`ScopedSignature.sum`) of two signatures over these sorts:

* `core B`: variables come from the binding signature; the constructors are `lam`, `app`, `letE`,
  `seq`, the literals `lit` and `natLit`, `prim`, `unit`, `pair`, `fst`, `snd`, `inl`, `inr`, the
  case analysis `case` and the iteration `iter`. An abstraction binds one variable in its body; a
  `letE` binds the value of its first argument in its second; each branch of a `case` binds the
  value of its side.
* `querySignature E`: one constructor `query e` per operation of an effect signature `E`, which
  takes an argument of the ground sort `E.dom e` and has the ground sort `E.cod e`. The interface
  of the calls is the polynomial functor `E.toPFunctor`, whose positions are an operation with an
  argument and whose directions are the answers.

## Main definitions

* `Ground`, `Ty`: the ground types with their primitive operations, and the types of D.
* `CoreOp`, `core`: the constructors of D without effects and their binding signature.
* `Effect`, `Effect.toPFunctor`, `querySignature`: effect signatures, their interface and their
  binding signature.
* `signature`: the binding signature of D; `Tm`: its terms, with smart constructors.
-/

public section

universe u

namespace IPFunctor.CostD

open IPFunctor.ScopedSignature

/-- Ground types of D: codes, their denotations, and primitive operations between them. -/
structure Ground where
  /-- The codes of the ground types. -/
  G : Type u
  /-- The values of a ground type. -/
  den : G → Type u
  /-- The primitive operations from a ground type to a ground type. -/
  Prim : G → G → Type u
  /-- The function a primitive operation computes. -/
  apply : {g h : G} → Prim g h → den g → den h

/-- The types of D over ground codes `G`. -/
inductive Ty (G : Type u) : Type u where
  /-- A ground type. -/
  | base (g : G)
  /-- The unit type. -/
  | unit
  /-- The natural numbers, the counters of `iter`. -/
  | nat
  /-- Products. -/
  | prod (a b : Ty G)
  /-- Sums. -/
  | sum (a b : Ty G)
  /-- Functions, read as Kleisli arrows. -/
  | arr (a b : Ty G)

variable {B : Ground.{u}}

/-- The constructors of D without effects, indexed by their result type. -/
inductive CoreOp (B : Ground.{u}) : Ty B.G → Type u where
  /-- Abstraction. -/
  | lam (a b : Ty B.G) : CoreOp B (.arr a b)
  /-- Application of a function to an argument. -/
  | app (a b : Ty B.G) : CoreOp B b
  /-- `letE e b` binds the value of `e` in `b`. -/
  | letE (a b : Ty B.G) : CoreOp B b
  /-- `seq e b` runs `e`, discards its value and runs `b`. -/
  | seq (a b : Ty B.G) : CoreOp B b
  /-- A literal of a ground type. -/
  | lit (g : B.G) (v : B.den g) : CoreOp B (.base g)
  /-- A natural-number literal. -/
  | natLit (n : ℕ) : CoreOp B .nat
  /-- A primitive operation. -/
  | prim {g h : B.G} (p : B.Prim g h) : CoreOp B (.base h)
  /-- The unit value. -/
  | unit : CoreOp B .unit
  /-- Pairing. -/
  | pair (a b : Ty B.G) : CoreOp B (.prod a b)
  /-- First projection. -/
  | fst (a b : Ty B.G) : CoreOp B a
  /-- Second projection. -/
  | snd (a b : Ty B.G) : CoreOp B b
  /-- Left injection. -/
  | inl (a b : Ty B.G) : CoreOp B (.sum a b)
  /-- Right injection. -/
  | inr (a b : Ty B.G) : CoreOp B (.sum a b)
  /-- Case analysis on a sum, each branch binding the value of its side. -/
  | case (a b c : Ty B.G) : CoreOp B c
  /-- `iter n f i` applies `f` to `i`, `n` times. -/
  | iter (c : Ty B.G) : CoreOp B c

/-- The number of arguments of a constructor. -/
@[expose, reducible] def CoreOp.arity : {a : Ty B.G} → CoreOp B a → ℕ
  | _, .lit _ _ | _, .natLit _ | _, .unit => 0
  | _, .lam _ _ | _, .prim _ | _, .fst _ _ | _, .snd _ _ | _, .inl _ _ | _, .inr _ _ => 1
  | _, .case _ _ _ | _, .iter _ => 3
  | _, _ => 2

/-- The binding signature of D without effects. -/
@[expose, reducible] def core (B : Ground.{u}) : ScopedSignature (Ty B.G) where
  Op := CoreOp B
  Arg op := Fin op.arity
  binders op := match op with
    | .lam a _ => fun _ => [a]
    | .letE a _ => Fin.cases [] fun _ => [a]
    | .case a b _ => Fin.cases [] (Fin.cases [a] fun _ => [b])
    | .lit _ _ | .natLit _ | .unit => Fin.elim0
    | .app _ _ | .seq _ _ | .prim _ | .pair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _
    | .iter _ => fun _ => []
  sort op := match op with
    | .lam _ b => fun _ => b
    | .app a b => Fin.cases (.arr a b) fun _ => a
    | .letE a b => Fin.cases a fun _ => b
    | .seq a b => Fin.cases a fun _ => b
    | .lit _ _ | .natLit _ | .unit => Fin.elim0
    | .prim (g := g) _ => fun _ => .base g
    | .pair a b => Fin.cases a fun _ => b
    | .fst a b | .snd a b => fun _ => .prod a b
    | .inl a _ => fun _ => a
    | .inr _ b => fun _ => b
    | .case a b c => Fin.cases (.sum a b) fun _ => c
    | .iter c => Fin.cases .nat (Fin.cases (.arr c c) fun _ => c)

/-! ## Effects -/

/-- An effect signature: operations, each with a ground argument type and a ground answer
type. -/
structure Effect (B : Ground.{u}) where
  /-- The operations. -/
  E : Type u
  /-- The type of the argument of an operation. -/
  dom : E → B.G
  /-- The type of the answer of an operation. -/
  cod : E → B.G

/-- The interface of an effect signature: a call is an operation with an argument, and its
answers are the values of the operation's answer type. -/
@[expose, reducible] def Effect.toPFunctor (E : Effect B) : PFunctor.{u, u} :=
  ⟨(e : E.E) × B.den (E.dom e), fun x => B.den (E.cod x.1)⟩

/-- The constructors of the calls of an effect signature. -/
inductive QueryOp (E : Effect B) : Ty B.G → Type u where
  /-- Call the operation `e` at the value of the argument. -/
  | query (e : E.E) : QueryOp E (.base (E.cod e))

/-- The binding signature of the calls: one argument, of the operation's argument type. -/
@[expose, reducible] def querySignature (E : Effect B) : ScopedSignature (Ty B.G) where
  Op := QueryOp E
  Arg _ := Fin 1
  binders _ _ := []
  sort op := match op with
    | .query e => fun _ => .base (E.dom e)

/-- The binding signature of D: the constructors without effects and the calls. -/
abbrev signature (E : Effect B) : ScopedSignature (Ty B.G) := (core B).sum (querySignature E)

/-- The terms of D in the context `Γ` at the type `a`. -/
abbrev Tm (E : Effect B) (Γ : List (Ty B.G)) (a : Ty B.G) := (signature E).Term Γ a

namespace Tm

variable {E : Effect B} {Γ : List (Ty B.G)} {a b c : Ty B.G}

/-- A variable. -/
@[expose] def var (x : ScopedVar Γ a) : Tm E Γ a := Term.var x

/-- Abstraction. -/
@[expose] def lam (body : Tm E (a :: Γ) b) : Tm E Γ (.arr a b) :=
  .node (.inl (.lam a b)) fun _ => body

/-- Application. -/
@[expose] def app (f : Tm E Γ (.arr a b)) (x : Tm E Γ a) : Tm E Γ b :=
  .node (.inl (.app a b)) (Fin.cases f fun _ => x)

/-- Binding the value of `e` in `body`. -/
@[expose] def letE (e : Tm E Γ a) (body : Tm E (a :: Γ) b) : Tm E Γ b :=
  .node (.inl (.letE a b)) (Fin.cases e fun _ => body)

/-- Running `e`, then `body`. -/
@[expose] def seq (e : Tm E Γ a) (body : Tm E Γ b) : Tm E Γ b :=
  .node (.inl (.seq a b)) (Fin.cases e fun _ => body)

/-- A literal of a ground type. -/
@[expose] def lit (g : B.G) (v : B.den g) : Tm E Γ (.base g) :=
  .node (.inl (.lit g v)) fun p => p.elim0

/-- A natural-number literal. -/
@[expose] def natLit (n : ℕ) : Tm E Γ .nat :=
  .node (.inl (.natLit n)) fun p => p.elim0

/-- A primitive operation. -/
@[expose] def prim {g h : B.G} (p : B.Prim g h) (x : Tm E Γ (.base g)) : Tm E Γ (.base h) :=
  .node (.inl (.prim p)) fun _ => x

/-- The unit value. -/
@[expose] def unit : Tm E Γ .unit :=
  .node (.inl .unit) fun p => p.elim0

/-- Pairing. -/
@[expose] def pair (x : Tm E Γ a) (y : Tm E Γ b) : Tm E Γ (.prod a b) :=
  .node (.inl (.pair a b)) (Fin.cases x fun _ => y)

/-- First projection. -/
@[expose] def fst (p : Tm E Γ (.prod a b)) : Tm E Γ a :=
  .node (.inl (.fst a b)) fun _ => p

/-- Second projection. -/
@[expose] def snd (p : Tm E Γ (.prod a b)) : Tm E Γ b :=
  .node (.inl (.snd a b)) fun _ => p

/-- Left injection. -/
@[expose] def inl (x : Tm E Γ a) : Tm E Γ (.sum a b) :=
  .node (.inl (.inl a b)) fun _ => x

/-- Right injection. -/
@[expose] def inr (y : Tm E Γ b) : Tm E Γ (.sum a b) :=
  .node (.inl (.inr a b)) fun _ => y

/-- Case analysis on a sum. -/
@[expose] def case (s : Tm E Γ (.sum a b)) (l : Tm E (a :: Γ) c) (r : Tm E (b :: Γ) c) :
    Tm E Γ c :=
  .node (.inl (.case a b c)) (Fin.cases s (Fin.cases l fun _ => r))

/-- `iter n f i` applies `f` to `i`, `n` times. -/
@[expose] def iter (n : Tm E Γ .nat) (f : Tm E Γ (.arr c c)) (i : Tm E Γ c) : Tm E Γ c :=
  .node (.inl (.iter c)) (Fin.cases n (Fin.cases f fun _ => i))

/-- A call of the operation `e`. -/
@[expose] def query (e : E.E) (x : Tm E Γ (.base (E.dom e))) : Tm E Γ (.base (E.cod e)) :=
  .node (.inr (.query e)) fun _ => x

end Tm

end IPFunctor.CostD
