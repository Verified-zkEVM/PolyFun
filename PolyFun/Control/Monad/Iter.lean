/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Init

/-! # Iterative monads

A monad `m` is *iterative* when it provides a uniform iteration combinator
`MonadIter.iterM : (β → m (β ⊕ α)) → β → m α` that turns any "loop body"
sending each input to either a fresh input (`Sum.inl`) or a final result
(`Sum.inr`) into a transformer producing the result.

The notion is due to Adámek, Milius, and Velebil (and used pervasively in
the Coq `InteractionTrees` library, `Basics/Basics.v`, where it is called
`MonadIter`). It generalises uniform definition of recursive functions
across monadic effects and is the data underlying `ITree.iter`,
`OracleComp`'s simulators, the `MonadIter` instances on `OptionT` /
`StateT`, and so on.

## Main definitions

* `MonadIter m` — typeclass packaging a single iteration combinator.
* `LawfulMonadIter m` — the standard Conway/Elgot iteration laws, stated
  over a monad-specific semantic equivalence.

## Conventions

We use `Sum.inl` for "loop continues with new input" and `Sum.inr` for
"loop terminates with this final result", matching the Coq library and
the standard Bekic / iterative-monads literature. (Some Haskell libraries
flip the convention; we stick with `inl = continue`, `inr = stop`.)

## Implementation notes

Lean 4.32 provides the function
`whileM : (β → m (β ⊕ α)) → β → m α`, with the same branch
convention as `iterM`, but not a typeclass or a corresponding lawful interface.
Core `whileM` is implemented by partial recursion and requires `Nonempty α`.
By contrast, `MonadIter` lets a monad select its own implementation and also
supports empty result types, which are useful for non-returning resumptions.

This distinction is operationally important for `ITree`: continuing an
iteration must first expose a silent-step constructor so the coinductive tree
remains productive. Its standard iteration theory therefore holds up to weak
bisimulation, rather than raw equality. `LawfulMonadIter` accordingly lets each
instance select its semantic equivalence.

Lean's `while` notation does not call `iterM` directly. It elaborates through
`ForIn m Lean.Loop Unit`, whose generic instance uses core `whileM`. The module
`PolyFun.ITree.Do` provides a scoped, `ITree`-specific `ForIn` instance backed
by `ITree.iter`; users opt into that interpretation with `open scoped ITree`.
-/

@[expose] public section

universe u v

/-- A monad `m` is *iterative* when it admits a uniform iteration operator
turning loop bodies of type `β → m (β ⊕ α)` into transformers of type
`β → m α`. The operator should iterate the body, restarting on each
`Sum.inl` and terminating on each `Sum.inr`.

Unlike Lean's core `whileM`, the implementation is selected by the monad and
the result type need not have a `Nonempty` instance. -/
class MonadIter (m : Type u → Type v) where
  /-- Iterate `f`, restarting the loop on each `Sum.inl j` and terminating
  with the result of each `Sum.inr r`. -/
  iterM {α β : Type u} (f : β → m (β ⊕ α)) (init : β) : m α

export MonadIter (iterM)

/-- A lawful iterative monad satisfies the Conway/Elgot iteration laws over
a chosen semantic equivalence.

The selected relation must be an equivalence and a congruence for `bind` and
`iterM`. The four characteristic laws are:

* `iter_unfold`: the fixed-point equation;
* `iter_natural`: postprocessing / parameter naturality;
* `iter_dinatural`: the composition identity for changing loop state;
* `iter_codiagonal`: flattening two nested loops (double dagger).

Using an explicit semantic equivalence is essential for productive
coinductive monads: their iteration operator may add guards that are
observable by equality but intentionally invisible semantically. -/
class LawfulMonadIter (m : Type u → Type v) [Monad m] [LawfulMonad m]
    [MonadIter m] where
  /-- Semantic equivalence used by the iteration laws. -/
  Eqv {α : Type u} : m α → m α → Prop
  /-- The semantic relation is reflexive. -/
  eqv_refl {α : Type u} (x : m α) : Eqv x x
  /-- The semantic relation is symmetric. -/
  eqv_symm {α : Type u} {x y : m α} : Eqv x y → Eqv y x
  /-- The semantic relation is transitive. -/
  eqv_trans {α : Type u} {x y z : m α} : Eqv x y → Eqv y z → Eqv x z
  /-- Semantic equivalence is a two-sided congruence for monadic bind. -/
  bind_eqv {α β : Type u} {x y : m α} {f g : α → m β}
    (hxy : Eqv x y) (hfg : ∀ a, Eqv (f a) (g a)) :
    Eqv (x >>= f) (y >>= g)
  /-- Pointwise-equivalent loop bodies have equivalent iterations. -/
  iter_eqv {α β : Type u} {f g : β → m (β ⊕ α)}
    (hfg : ∀ b, Eqv (f b) (g b)) (init : β) :
    Eqv (iterM f init) (iterM g init)
  /-- Fixed-point / unfolding law. -/
  iter_unfold {α β : Type u} (body : β → m (β ⊕ α)) (init : β) :
    Eqv (iterM body init)
      (body init >>= fun
        | .inl next => iterM body next
        | .inr result => pure result)
  /-- Naturality in the output, also called the parameter identity. -/
  iter_natural {α β γ : Type u} (body : β → m (β ⊕ α))
      (k : α → m γ) (init : β) :
    Eqv (iterM body init >>= k)
      (iterM (fun b => body b >>= fun
        | .inl next => pure (.inl next)
        | .inr result => k result >>= fun value => pure (.inr value)) init)
  /-- Dinaturality in the loop state, also called the composition identity. -/
  iter_dinatural {α β γ : Type u} (f : α → m (β ⊕ γ))
      (g : β → m (α ⊕ γ)) (init : α) :
    Eqv
      (iterM (fun a => f a >>= fun
        | .inl b => g b
        | .inr result => pure (.inr result)) init)
      (f init >>= fun
        | .inl b => iterM (fun b => g b >>= fun
            | .inl a => f a
            | .inr result => pure (.inr result)) b
        | .inr result => pure result)
  /-- Codiagonal / double-dagger law: two nested loops flatten to one. -/
  iter_codiagonal {α β : Type u} (body : α → m (α ⊕ (α ⊕ β)))
      (init : α) :
    Eqv (iterM (iterM body) init)
      (iterM (fun a => body a >>= fun
        | .inl next => pure (.inl next)
        | .inr (.inl next) => pure (.inl next)
        | .inr (.inr result) => pure (.inr result)) init)

namespace LawfulMonadIter

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadIter m]
  [LawfulMonadIter m]

/-- The semantic relation supplied by a lawful iteration instance is an
equivalence relation at every result type. -/
theorem eqv_equivalence (α : Type u) : Equivalence (@Eqv m _ _ _ _ α) :=
  ⟨eqv_refl, fun {_ _} => eqv_symm, fun {_ _ _} => eqv_trans⟩

end LawfulMonadIter

export LawfulMonadIter
  (Eqv bind_eqv iter_eqv iter_unfold iter_natural iter_dinatural iter_codiagonal)
