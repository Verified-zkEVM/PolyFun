/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedPrograms
public import PolyFun.IPFunctor.Scoped.Sum

/-!
# An effectful language read call by value

The language of the scoped-program tutorial gains one effectful operation: `query e` evaluates
`e` and asks an oracle for a number. The signature of the new language, `Lang`, is the sum of the
scoped-program signature and a signature whose only constructor is the query.

The language has two readings. The ordinary reading (`Term.denote`) answers each query by a fixed
function `f`. The call-by-value reading (`Term.denoteCBV` of `cbv`) is a free program over the
oracle interface `Query`. Its arguments run from left to right, an abstraction returns a Kleisli
arrow, and a query asks the oracle. Running the program with the handler that answers by `f`
(`run f`) gives the ordinary reading (`run_denoteCBV`). The proof is `Term.denoteCBV_related` at a
logical relation (`Rel`): equal numbers, and at an arrow sort, functions that send related
arguments to programs whose runs are related to the results.

A term that uses no query gives the same answer under every handler (`run_denoteCBV_of_heads`).
Its fragment is the set of left heads, `Set.range Head.inl`. A scoped-program expression
embedded by `Term.inl` lies in this fragment (`Term.heads_inl`) and keeps its meaning
(`Term.denote_inl`). So under every handler, its call-by-value reading runs to its meaning in
`ScopedPrograms.algebra` (`run_denoteCBV_inl`).
-/

public section

namespace Examples.ScopedEffects

open IPFunctor IPFunctor.ScopedSignature Examples.ScopedPrograms

/-! ## The language -/

/-- An oracle query is a number, and so is its answer. -/
abbrev Query : PFunctor := ⟨Nat, fun _ => Nat⟩

/-- Programs that query the oracle. -/
abbrev Prog := PFunctor.FreeM Query

/-- The effectful operation. -/
inductive QueryOp : Ty → Type where
  | query : QueryOp .nat

/-- The query takes one argument of sort `nat` and binds nothing. -/
@[expose, reducible] def querySignature : ScopedSignature Ty where
  Op := QueryOp
  Arg _ := Unit
  binders _ _ := []
  sort _ _ := .nat

/-- The effectful language: the scoped-program constructors and the query. -/
abbrev Lang : ScopedSignature Ty := signature.sum querySignature

/-- Query the oracle at the value of a term. -/
@[expose] def query {Γ : List Ty} (e : Lang.Term Γ .nat) : Lang.Term Γ .nat :=
  .node (.inr .query) fun _ => e

/-- `let x := query 3 in x + query x`: ask at `3`, then at the answer. -/
@[expose] def askTwice : Lang.Term [] .nat :=
  .node (.inl (.letE .nat .nat)) (Fin.cases (query (Term.inl (Expr.literal 3)))
    fun _ => .node (.inl .add) (Fin.cases (.var .zero) fun _ => query (.var .zero)))

/-! ## The call-by-value reading -/

/-- Values of the call-by-value reading: numbers, and Kleisli arrows at arrow sorts. -/
@[expose, reducible] def KValue : Ty → Type
  | .nat => Nat
  | .arrow a b => KValue a → Prog (KValue b)

/-- The call-by-value reading of the scoped-program constructors. Arguments run from left to
right. An abstraction returns a Kleisli arrow, and an application runs the function, then the
argument, then the arrow. A loop runs its seed and then its body once per iteration. -/
@[expose] def coreCBV : CBVInterpretation signature Prog KValue
  | _, .literal n, _ => pure n
  | _, .add, next => do
    let x ← next 0 Env.empty
    let y ← next 1 Env.empty
    pure (x + y)
  | _, .lam _ _, next => pure fun x => next 0 (Env.cons x Env.empty)
  | _, .app _ _, next => do
    let g ← next 0 Env.empty
    let x ← next 1 Env.empty
    g x
  | _, .letE _ _, next => do
    let x ← next 0 Env.empty
    next 1 (Env.cons x Env.empty)
  | _, .loop _ n, next => Nat.rec (next 0 Env.empty)
    (fun i state => do
      let s ← state
      next 1 (Env.cons i (Env.cons s Env.empty))) n

/-- The call-by-value reading of the query: run the argument, then ask the oracle. -/
@[expose] def queryCBV : CBVInterpretation querySignature Prog KValue
  | _, .query, next => do
    let x ← next () Env.empty
    PFunctor.FreeM.lift (P := Query) x

/-- The call-by-value reading of the effectful language. -/
abbrev cbv : CBVInterpretation Lang Prog KValue := coreCBV.sum queryCBV

/-- Run a program, answering each query `n` by `f n`. -/
@[expose] def run (f : Nat → Nat) {α : Type} (c : Prog α) : α :=
  c.liftM (m := Id) f

@[simp] theorem run_pure (f : Nat → Nat) {α : Type} (x : α) : run f (pure x) = x := rfl

theorem run_bind (f : Nat → Nat) {α β : Type} (c : Prog α) (g : α → Prog β) :
    run f (c >>= g) = run f (g (run f c)) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem run_lift (f : Nat → Nat) (n : Nat) :
    run f (PFunctor.FreeM.lift (P := Query) n) = f n := rfl

/-! ## The ordinary reading -/

/-- The ordinary reading of the query: answer by `f`. -/
@[expose] def queryAlgebra (f : Nat → Nat) : Interpretation querySignature Ty.Value
  | _, .query, next => f (next () Env.empty)

/-- With the oracle `(· + 1)`, `askTwice` asks at `3` and then at `4`. -/
example : askTwice.denote (algebra.sum (queryAlgebra (· + 1))) Env.empty = 4 + 5 := rfl

/-- The call-by-value reading of `askTwice` asks at `3`, then at the answer `x`, and returns
`x` plus the second answer. -/
example : askTwice.denoteCBV cbv Env.empty =
    .liftBind (P := Query) 3 fun x => .liftBind x fun y => pure (x + y) := rfl

example : run (· + 1) (askTwice.denoteCBV cbv Env.empty) = 4 + 5 := rfl

/-! ## Adequacy -/

/-- Related values, for runs that answer each query by `f`: equal numbers, and at an arrow sort,
functions that send related arguments to programs whose runs are related to the results. -/
@[expose] def Rel (f : Nat → Nat) : (a : Ty) → KValue a → a.Value → Prop
  | .nat, v, w => v = w
  | .arrow a b, v, w => ∀ x y, Rel f a x y → Rel f b (run f (v x)) (w y)

/-- The scoped-program constructors are related at every head, for runs with any handler. -/
theorem coreCBV_relatedOn (f : Nat → Nat) :
    CBVInterpretation.RelatedOn Set.univ (Rel f) (fun a c w => Rel f a (run f c) w) coreCBV
      algebra := by
  rintro ⟨a, op⟩ - k k' hk
  have h0 : Env.LiftRel (Rel f) (Env.empty : Env KValue []) (Env.empty : Env Ty.Value []) :=
    Env.liftRel_empty _
  cases op with
  | literal n => rfl
  | add =>
    change run f (k 0 Env.empty >>= fun x => k 1 Env.empty >>= fun y => pure (x + y)) =
      k' 0 Env.empty + k' 1 Env.empty
    rw [run_bind, run_bind, run_pure, hk 0 _ _ h0, hk 1 _ _ h0]
  | lam a b => exact fun x y hxy => hk 0 _ _ (h0.cons hxy)
  | app c b =>
    change Rel f _ (run f (k 0 Env.empty >>= fun g => k 1 Env.empty >>= fun x => g x))
      (k' 0 Env.empty (k' 1 Env.empty))
    rw [run_bind, run_bind]
    exact hk 0 _ _ h0 _ _ (hk 1 _ _ h0)
  | letE c b =>
    change Rel f _ (run f (k 0 Env.empty >>= fun x => k 1 (Env.cons x Env.empty)))
      (k' 1 (Env.cons (k' 0 Env.empty) Env.empty))
    rw [run_bind]
    exact hk 1 _ _ (h0.cons (hk 0 _ _ h0))
  | loop a n =>
    suffices h : ∀ i, Rel f a
        (run f (Nat.rec (motive := fun _ => Prog (KValue a)) (k 0 Env.empty)
          (fun j state => state >>= fun s => k 1 (Env.cons j (Env.cons s Env.empty))) i))
        (Nat.rec (motive := fun _ => a.Value) (k' 0 Env.empty)
          (fun j state => k' 1 (Env.cons j (Env.cons state Env.empty))) i) from h n
    intro i
    induction i with
    | zero => exact hk 0 _ _ h0
    | succ i ih =>
      change Rel f a (run f (_ >>= fun s => k 1 (Env.cons i (Env.cons s Env.empty)))) _
      rw [run_bind]
      exact hk 1 _ _ ((h0.cons ih).cons rfl)

/-- The query is related at its head when the ordinary reading answers by the handler's
function. -/
theorem queryCBV_relatedOn (f : Nat → Nat) :
    CBVInterpretation.RelatedOn Set.univ (Rel f) (fun a c w => Rel f a (run f c) w) queryCBV
      (queryAlgebra f) := by
  rintro ⟨a, op⟩ - k k' hk
  cases op
  change run f (k () Env.empty >>= fun x => PFunctor.FreeM.lift (P := Query) x) =
    f (k' () Env.empty)
  rw [run_bind, run_lift, hk () _ _ (Env.liftRel_empty _)]

/-- Every head of the language is a head of one of its summands. -/
theorem heads_subset_inl_union_inr {Γ : List Ty} {a : Ty} (t : Lang.Term Γ a) :
    t.heads ⊆ Head.inl '' Set.univ ∪ Head.inr '' Set.univ := by
  rintro ⟨a, op | op⟩ -
  · exact Or.inl ⟨⟨a, op⟩, trivial, rfl⟩
  · exact Or.inr ⟨⟨a, op⟩, trivial, rfl⟩

/-- **Adequacy.** Running the call-by-value reading with the handler that answers by `f` gives a
result related to the ordinary reading that answers by `f`. -/
theorem denoteCBV_related {Γ : List Ty} {a : Ty} (f : Nat → Nat) (t : Lang.Term Γ a)
    {η : Env KValue Γ} {ζ : Env Ty.Value Γ} (hη : Env.LiftRel (Rel f) η ζ) :
    Rel f a (run f (t.denoteCBV cbv η)) (t.denote (algebra.sum (queryAlgebra f)) ζ) :=
  Term.denoteCBV_related (RV := Rel f) (RC := fun a c w => Rel f a (run f c) w)
    (fun _ _ _ h => h) ((coreCBV_relatedOn f).sum (queryCBV_relatedOn f)) t
    (heads_subset_inl_union_inr t) hη

/-- At sort `nat`, the run of a closed program is its ordinary reading. -/
theorem run_denoteCBV (f : Nat → Nat) (t : Lang.Term [] .nat) :
    run f (t.denoteCBV cbv Env.empty) = t.denote (algebra.sum (queryAlgebra f)) Env.empty :=
  denoteCBV_related f t (Env.liftRel_empty _)

/-! ## Terms without queries -/

/-- Running the call-by-value reading of a term that uses no query, with any handler `f`, gives
a result related to its ordinary reading with queries answered by any `g`. -/
theorem denoteCBV_related_of_heads {Γ : List Ty} {a : Ty} (f g : Nat → Nat) (t : Lang.Term Γ a)
    (ht : t.heads ⊆ Set.range Head.inl) {η : Env KValue Γ} {ζ : Env Ty.Value Γ}
    (hη : Env.LiftRel (Rel f) η ζ) :
    Rel f a (run f (t.denoteCBV cbv η)) (t.denote (algebra.sum (queryAlgebra g)) ζ) := by
  refine Term.denoteCBV_related (H := Head.inl '' Set.univ ∪ Head.inr '' ∅) (RV := Rel f)
    (RC := fun a c w => Rel f a (run f c) w) (fun _ _ _ h => h)
    ((coreCBV_relatedOn f).sum fun _ h => h.elim) t ?_ hη
  rw [Set.image_univ, Set.image_empty, Set.union_empty]
  exact ht

/-- A closed program of sort `nat` that uses no query gives the same answer under every
handler. -/
theorem run_denoteCBV_of_heads (f g : Nat → Nat) (t : Lang.Term [] .nat)
    (ht : t.heads ⊆ Set.range Head.inl) :
    run f (t.denoteCBV cbv Env.empty) = run g (t.denoteCBV cbv Env.empty) :=
  (denoteCBV_related_of_heads f f t ht (Env.liftRel_empty _)).trans
    (denoteCBV_related_of_heads g f t ht (Env.liftRel_empty _)).symm

/-- Under every handler, an embedded scoped-program expression runs to its meaning in
`ScopedPrograms.algebra`. -/
theorem run_denoteCBV_inl (f : Nat → Nat) (e : Expr [] .nat) :
    run f ((Term.inl e).denoteCBV cbv Env.empty) = e.denote algebra Env.empty :=
  (denoteCBV_related_of_heads f f (Term.inl e)
    ((Term.heads_inl e).trans_subset (Set.image_subset_range _ _))
    (Env.liftRel_empty _)).trans (Term.denote_inl _ _ _ _)

/-- The loop `sumTo 4` runs to `0 + 1 + 2 + 3` under every handler. -/
example (f : Nat → Nat) : run f ((Term.inl (sumTo 4)).denoteCBV cbv Env.empty) = 6 :=
  (run_denoteCBV_inl f (sumTo 4)).trans rfl

end Examples.ScopedEffects
