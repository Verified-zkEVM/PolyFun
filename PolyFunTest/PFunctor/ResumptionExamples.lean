/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Resumption

/-! # Resumption foundation examples -/

@[expose] public section

universe uA uB uα uβ uγ uX

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ} {X : Type uX}

/-- The computational view is an equivalence even when the polynomial,
return type, and recursive carrier inhabit independent universes. -/
example (step : β ⊕ p.Obj X) :
    viewEquiv (viewEquiv.symm step) = step := by
  simp

example (step : (p + C.{uβ, uB} β).Obj X) :
    viewEquiv.symm (viewEquiv step) = step := by
  simp

/-- Return and query views inject into the expected operation-first raw
summands, with the query continuation left attached to its operation. -/
example (value : β) :
    pack (Sum.inl value : β ⊕ p.Obj X) = ⟨Sum.inr value, PEmpty.elim⟩ := by
  rfl

example (position : p.A) (onAnswer : p.B position → X) :
    pack (Sum.inr ⟨position, onAnswer⟩ : β ⊕ p.Obj X) =
      ⟨Sum.inl position, onAnswer⟩ := by
  rfl

/-- The raw resumption carrier uses the same operation-first convention as
the interaction-tree carrier. -/
example : Resumption p β = M.{max uA uβ, uB} (p + C.{uβ, uB} β) := rfl

/-- Corecursion does not couple the seed universe to either universe of the
polynomial or to the return-value universe. -/
def universeSeparatedCorec (step : X → β ⊕ p.Obj X) (seed : X) :
    Resumption p β :=
  corec step seed

example (step : X → β ⊕ p.Obj X) (seed : X) :
    dest (universeSeparatedCorec step seed) =
      Sum.map (fun value : β => value) (p.map (corec step)) (step seed) := by
  simp [universeSeparatedCorec]

example (computation : Resumption p β) : corec dest computation = computation := by
  simp

/-! ## Functorial and monadic structure -/

/-- Named bind does not couple the source and target return universes. -/
example {α : Type uα} (computation : Resumption p α)
    (k : α → Resumption p β) : Resumption p β :=
  bind computation k

example (position : p.A) :
    dest (lift position) = Sum.inr ⟨position, pure⟩ :=
  dest_lift position

example {α : Type uα} (value : α) (k : α → Resumption p β) :
    bind (pure value) k = k value :=
  bind_pure_left value k

example {α : Type uα} (position : p.A)
    (next : p.B position → Resumption p α) (k : α → Resumption p β) :
    bind (query position next) k =
      query position (fun direction => bind (next direction) k) :=
  bind_query position next k

example {α : Type uα} (computation : Resumption p α) :
    bind computation pure = computation :=
  bind_pure_right computation

example {α : Type uα} {γ : Type uγ} (computation : Resumption p α)
    (k : α → Resumption p β) (k' : β → Resumption p γ) :
    bind (bind computation k) k' =
      bind computation (fun value => bind (k value) k') :=
  bind_assoc computation k k'

/-- The ordinary same-universe specialization exposes a lawful monad. -/
example {p : PFunctor.{uA, uB}} {α β : Type uX}
    (computation : Resumption p α) (k : α → Resumption p β) :
    computation >>= k = bind computation k :=
  rfl

end PFunctor.Resumption
