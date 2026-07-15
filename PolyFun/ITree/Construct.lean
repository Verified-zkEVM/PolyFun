/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Basic

/-! # Standard ITree combinators

Definitions of the standard interaction-tree combinators that depend only on
`bind`, `iter`, the smart constructors, and `M.corec`. These are the Lean
analogues of Coq's `Core/ITreeDefinition.v` `spin`, `forever`, `burn` and the
helpers in `Core/KTree.v` (`map`, `cat`, `ignore`).

The list of definitions and their Coq counterparts:

| Coq             | Lean              |
| --------------- | ----------------- |
| `spin`          | `ITree.diverge`   |
| `forever t`     | `ITree.forever`   |
| `ITree.map f t` | `ITree.map`       |
| `ITree.cat f g` | `ITree.cat`       |
| `ITree.ignore`  | `ITree.ignore`    |
| `burn n t`      | `ITree.take`      |

The named `map`, `cat`, and `forever` operations allow their source and target
types to live in different universes. The `Functor` and `Applicative` instances
on `ITree F` are derived from the `Monad` instance in `PolyFun.ITree.Basic` and
therefore use one value universe at a time. We record the corresponding `simp`
lemma `Functor.map = ITree.map` on that homogeneous fragment so that `simp` can
normalise occurrences of `(· <$> ·)` to `ITree.map`.
-/

@[expose] public section

universe u uA uB uα uβ uγ uUnit

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-! ### Diverging tree -/

/-- The diverging interaction tree, an infinite sequence of silent (`step`)
nodes. (Coq `spin`.) -/
def diverge : ITree F α :=
  PFunctor.M.corec (F := Poly F α)
    (fun (_ : PUnit.{uB + 1}) => ⟨.step, fun _ => PUnit.unit⟩)
    PUnit.unit

@[simp] theorem shape'_diverge :
    shape' (diverge (F := F) (α := α)) = ⟨.step, fun _ => diverge⟩ := by
  unfold shape' diverge
  rw [PFunctor.M.dest_corec_eq _ _ rfl]
  rfl

@[simp] theorem shape_diverge :
    shape (diverge (F := F) (α := α)) = .step := by
  unfold shape; rw [shape'_diverge]

/-! ### Functor map -/

/-- Map a function over the leaves of an interaction tree. (Coq
`ITree.map`.) -/
def map (f : α → β) (t : ITree F α) : ITree F β :=
  bind t (fun a => pure (f a))

/-! ### Kleisli composition -/

/-- Kleisli composition for ITree-valued functions: `cat f g a = f a >>= g`.
(Coq `ITree.cat`.) -/
def cat (f : α → ITree F β) (g : β → ITree F γ) : α → ITree F γ :=
  fun a => bind (f a) g

/-! ### Ignoring the result -/

/-- Run `t`, discarding its leaf value. The unit result may live in any
universe. (Coq `ITree.ignore`.) -/
def ignore (t : ITree F α) : ITree F PUnit.{uUnit + 1} :=
  map (fun _ => PUnit.unit) t

/-! ### Forever -/

/-- Run `t` forever, discarding each leaf value. The result type `β` is
arbitrary because `forever t` never produces a leaf. (Coq `forever`.) -/
def forever (t : ITree F α) : ITree F β :=
  iter (fun _ : PUnit.{uB + 1} => bind t (fun _ => pure (Sum.inl PUnit.unit))) PUnit.unit

/-! ### Bounded execution -/

/-- Strip up to `n` silent steps from the head of an interaction tree.
Stops early at the first `pure` or `query` node. (Coq `burn`.) -/
def take : Nat → ITree F α → ITree F α
  | 0, t => t
  | n + 1, t =>
      match shape' t with
      | ⟨.step, c⟩ => take n (c PUnit.unit)
      | ⟨.pure _, _⟩ => t
      | ⟨.query _, _⟩ => t

@[simp] theorem take_zero (t : ITree F α) : take 0 t = t := rfl

@[simp] theorem take_step (n : Nat) (t : ITree F α) :
    take (n + 1) (step t) = take n t := by
  change (match shape' (step t) with
      | ⟨.step, c⟩ => take n (c PUnit.unit)
      | ⟨.pure _, _⟩ => step t
      | ⟨.query _, _⟩ => step t) = take n t
  rw [shape'_step]

@[simp] theorem take_pure (n : Nat) (r : α) :
    take (n + 1) (pure (F := F) r) = pure r := by
  change (match shape' (pure (F := F) r) with
      | ⟨.step, c⟩ => take n (c PUnit.unit)
      | ⟨.pure _, _⟩ => pure r
      | ⟨.query _, _⟩ => pure r) = pure r
  rw [shape'_pure]

@[simp] theorem take_query (n : Nat) (a : F.A) (k : F.B a → ITree F α) :
    take (n + 1) (query a k) = query a k := by
  change (match shape' (query a k) with
      | ⟨.step, c⟩ => take n (c PUnit.unit)
      | ⟨.pure _, _⟩ => query a k
      | ⟨.query _, _⟩ => query a k) = query a k
  rw [shape'_query]

/-! ### `Functor.map` agrees with `ITree.map`

The `Functor (ITree F)` instance is derived from `Monad (ITree F)` (defined
in `PolyFun.ITree.Basic`) and computes `Functor.map f t` as
`t >>= (pure ∘ f)`, which is definitionally `ITree.map f t`. We expose this as
a `simp` lemma so that ordinary `(· <$> ·)` notation is normalised to
`ITree.map`. -/

@[simp] theorem map_eq_functor_map {α β : Type u} (f : α → β) (t : ITree F α) :
    f <$> t = ITree.map f t := rfl

end ITree
