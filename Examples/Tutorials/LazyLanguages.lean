/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Pointed
public import PolyFun.Control.Domain.PrefixRecursion
public import Mathlib.Order.Category.OmegaCompletePartialOrder

/-! # Meanings for a lazy typed language

A language with general recursion, runtime errors and lazy data needs a semantic target that keeps
three outcomes apart: a computation can diverge, fail, or return a value whose own entries,
arguments and results are still partial. `DomainResult` is that target.

This tutorial gives meanings to a small language with numbers, vectors, functions and a numeric
quantifier. Syntax is left out, so each term appears as its meaning. The language is not a model of
any existing one.
-/

@[expose] public section

open OmegaCompletePartialOrder

namespace PolyFunExamples.LazyLanguages

/-- The runtime errors of the language. -/
abbrev Err := String

/-- Types of the language. -/
inductive Ty
  /-- Numbers. -/
  | nat
  /-- Vectors of a fixed length. -/
  | vec (length : Nat) (entry : Ty)
  /-- Functions. -/
  | arrow (arg result : Ty)

/-- Values of each type. Entries, arguments and results are computations, so a value's outer
constructor can be known while they are still partial. -/
@[implicit_reducible] noncomputable def Ty.value : Ty → ωCPO
  | .nat => .of (DiscreteOrder Nat)
  | .vec n a => .of (Fin n → DomainResult Err a.value)
  | .arrow a b => .of (DomainResult Err a.value →𝒄 DomainResult Err b.value)

/-- Computations of a type: they diverge, fail or return a value. -/
abbrev Comp (a : Ty) := DomainResult Err a.value

/-! ## Data is available while its entries are partial -/

/-- A vector with a failing first entry and a diverging second entry. -/
noncomputable def partialPair : Comp (.vec 2 .nat) :=
  .value fun i => if i.val = 0 then .error "first" else ⊥

/-- The vector is a returned value, although neither of its entries is. -/
example : partialPair ≠ ⊥ := DomainResult.value_ne_bot _

/-- Demanding the outer constructor does not touch the entries. -/
example (next : Comp .nat) : DomainResult.force partialPair next = next := rfl

/-! ## Functions do not demand their arguments -/

/-- The function that ignores its argument. -/
noncomputable def constant (a : Ty) {b : Ty} (x : Comp b) : Comp (.arrow a b) :=
  .value (ContinuousHom.const x)

/-- An ignored argument can diverge. -/
example (x : Comp .nat) : DomainResult.applyContinuous (constant .nat x) ⊥ = x := rfl

/-- An ignored argument can fail. -/
example (x : Comp .nat) :
    DomainResult.applyContinuous (constant .nat x) (.error "unused") = x := rfl

/-! ## Strict operations demand their operands from left to right -/

/-- Addition demands both operands. -/
noncomputable def add : Comp .nat →𝒄 (Comp .nat →𝒄 Comp .nat) :=
  DomainResult.bind₂ (DiscreteOrder.continuousMap fun a =>
    DiscreteOrder.continuousMap fun b => .value ⟨a + b⟩)

/-- The left operand's error wins, even over a diverging right operand. -/
example : add (.error "left") ⊥ = .error "left" := rfl

/-- The left operand's divergence wins, even over a failing right operand. -/
example : add ⊥ (.error "right") = ⊥ := rfl

/-- Both operands return. -/
example : add (.value ⟨1⟩) (.value ⟨2⟩) = .value ⟨3⟩ := rfl

/-! ## Recursion is a least fixed point -/

/-- The definition `x = x` carries no information, so it diverges rather than fails. -/
example : (ContinuousHom.id : Comp .nat →𝒄 Comp .nat).fix = ⊥ :=
  le_antisymm (ContinuousHom.fix_le _ le_rfl) bot_le

/-- The equations of `xs = [first, xs[0] + 1, xs[1] + 1]`: each entry reads an earlier one. -/
noncomputable def increments (first : Comp .nat) :
    (i : Fin 3) → (Fin i.val → Comp .nat) →𝒄 Comp .nat
  | ⟨0, _⟩ => .const first
  | ⟨k + 1, _⟩ => .ofFun fun xs => add (xs ⟨k, Nat.lt_succ_self k⟩) (.value ⟨1⟩)

/-- The recursive vector is a returned value for every `first`, including a diverging one, and it
is the vector that finite recursion on its entries computes. -/
theorem increments_fix (first : Comp .nat) :
    (DomainResult.generateStep (DomainResult.elim (fun e _ => .error e)
      (ContinuousHom.prefixMap (increments first)))).fix =
      DomainResult.value (Function.prefixRecursion fun i => increments first i) :=
  DomainResult.generateStep_fix_eq_prefixRecursion _ _ fun _ => rfl

/-! ## Polymorphic types have computed domains

The domain of a polymorphic type is defined by recursion on the type. `PointedDomain` lets that
recursion produce the carrier, its order and its bottom together. -/

/-- A type under `n` numeric parameters, or a quantifier over one more. -/
inductive Scheme : Nat → Type
  /-- A type that may mention the parameters. -/
  | mono {n : Nat} (type : (Fin n → Nat) → Ty) : Scheme n
  /-- A quantifier over one numeric parameter. -/
  | all {n : Nat} (body : Scheme (n + 1)) : Scheme n

/-- A quantifier denotes one meaning per parameter, behind one outer suspension: evaluating a
polymorphic definition can diverge or fail before any instance is selected. -/
@[implicit_reducible] noncomputable def Scheme.domain :
    {n : Nat} → Scheme n → (Fin n → Nat) → PointedDomain
  | _, .mono t, ρ => .ofType (Comp (t ρ))
  | _, .all s, ρ => .result Err (.pi Nat fun l => s.domain (Fin.cons (α := fun _ => Nat) l ρ))

/-- A failure at any scheme. -/
noncomputable def Scheme.fail :
    {n : Nat} → (s : Scheme n) → (ρ : Fin n → Nat) → Err → s.domain ρ
  | _, .mono _, _, e => DomainResult.error e
  | _, .all _, _, e => DomainResult.error e

/-- Instantiating a quantifier demands its suspension and selects one instance. It adds no
suspension of its own, because `DomainResult.elim` targets any pointed domain. -/
noncomputable def Scheme.instantiate {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) :
    (Scheme.all s).domain ρ →𝒄 s.domain (Fin.cons (α := fun _ => Nat) l ρ) :=
  DomainResult.elim (fun e => s.fail _ e) (.ofFun fun f => f l)

/-- A diverging polymorphic definition diverges at every instance. -/
example {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) : s.instantiate ρ l ⊥ = ⊥ := rfl

/-- A failing polymorphic definition fails at every instance. -/
example {n : Nat} (s : Scheme (n + 1)) (ρ : Fin n → Nat) (l : Nat) (e : Err) :
    s.instantiate ρ l (DomainResult.error e) = s.fail _ e := rfl

end PolyFunExamples.LazyLanguages
