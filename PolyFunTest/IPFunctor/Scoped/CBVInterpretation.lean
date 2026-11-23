/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.CBVInterpretation

/-!
# Call-by-value interpretations

A language of numbers with lets has one effectful operation: `tick n e` records `n` in a log and
returns the value of `e`. Its call-by-value reading runs in `StateM (List Nat)`. Its ordinary
reading ignores the log.

* The algebra fixes the order of effects. Addition read from left to right logs `[1, 2]` for
  `tick 1 _ + tick 2 _`; read from right to left it logs `[2, 1]`.
* A let runs its bound term once: `let x := tick 5 0 in x + x` logs `[5]`. Substituting the bound
  term for `x` logs `[5, 5]`, although the ordinary meaning is unchanged. So the call-by-value
  meaning has no substitution law for arbitrary terms. It has the renaming law.
* In the identity monad, the call-by-value meaning of an ordinary algebra is its ordinary meaning.
* `Term.denoteCBV_related` at every head gives adequacy: the value of a run is the ordinary
  meaning. At the heads other than `tick`, it shows that a term without ticks leaves the log
  unchanged. A term with a tick changes the log, so the restriction to the fragment is needed.
-/

@[expose] public section

namespace PolyFunTest.Scoped.CBV

open IPFunctor IPFunctor.ScopedSignature

/-- Literals, addition, logging and lets, all of the single sort. -/
inductive Op : Unit → Type where
  | literal (n : Nat) : Op ()
  | add : Op ()
  | tick (n : Nat) : Op ()
  | letE : Op ()

/-- Argument positions; a literal has none and a tick has one. -/
@[reducible] def Op.arity : {a : Unit} → Op a → Nat
  | _, .literal _ => 0
  | _, .tick _ => 1
  | _, .add | _, .letE => 2

/-- Only the body of a let binds a variable. -/
@[reducible] def signature : ScopedSignature Unit where
  Op := Op
  Arg op := Fin op.arity
  binders op := match op with
    | .letE => Fin.cases [] fun _ => [()]
    | _ => fun _ => []
  sort _ _ := ()

/-- Whether an operation logs. -/
def Op.isTick : {a : Unit} → Op a → Bool
  | _, .tick _ => true
  | _, _ => false

variable {Γ : List Unit}

/-- A literal. -/
def lit (n : Nat) : signature.Term Γ () := .node (.literal n) fun p => nomatch p

/-- Addition. -/
def add (x y : signature.Term Γ ()) : signature.Term Γ () := .node .add (Fin.cases x fun _ => y)

/-- Record `n`, then return the value of `e`. -/
def tick (n : Nat) (e : signature.Term Γ ()) : signature.Term Γ () := .node (.tick n) fun _ => e

/-- A lexical binding. -/
def letE (value : signature.Term Γ ()) (body : signature.Term (() :: Γ) ()) :
    signature.Term Γ () :=
  .node .letE (Fin.cases value fun _ => body)

/-- Runs that keep a log. -/
abbrev Logged := StateM (List Nat)

/-- The call-by-value reading: addition runs its arguments from left to right, and a tick logs
before it runs its argument. -/
def cbv : CBVInterpretation signature Logged (fun _ => Nat)
  | _, .literal n, _ => pure n
  | _, .add, next => do
    let x ← next 0 Env.empty
    let y ← next 1 Env.empty
    pure (x + y)
  | _, .tick n, next => do
    modify (· ++ [n])
    next 0 Env.empty
  | _, .letE, next => do
    let x ← next 0 Env.empty
    next 1 (Env.cons x Env.empty)

/-- The same reading, with the arguments of addition run from right to left. -/
def cbvRightToLeft : CBVInterpretation signature Logged (fun _ => Nat)
  | _, .add, next => do
    let y ← next 1 Env.empty
    let x ← next 0 Env.empty
    pure (x + y)
  | _, op, next => cbv op next

/-- The ordinary reading ignores the log. -/
def algebra : Interpretation signature (fun _ => Nat)
  | _, .literal n, _ => n
  | _, .add, next => next 0 Env.empty + next 1 Env.empty
  | _, .tick _, next => next 0 Env.empty
  | _, .letE, next => next 1 (Env.cons (next 0 Env.empty) Env.empty)

/-! ## Order and sharing of effects -/

/-- `tick 1 10 + tick 2 20`. -/
def twoTicks : signature.Term [] () := add (tick 1 (lit 10)) (tick 2 (lit 20))

example : (twoTicks.denoteCBV cbv Env.empty).run [] = (30, [1, 2]) := rfl

example : (twoTicks.denoteCBV cbvRightToLeft Env.empty).run [] = (30, [2, 1]) := rfl

/-- The body of `let x := tick 5 0 in x + x`. -/
def double : signature.Term [()] () := add (.var .zero) (.var .zero)

example : ((letE (tick 5 (lit 0)) double).denoteCBV cbv Env.empty).run [] = (0, [5]) := rfl

/-- Substituting the bound term for the variable runs it at each occurrence. -/
example : ((double.substOne (tick 5 (lit 0))).denoteCBV cbv Env.empty).run [] = (0, [5, 5]) :=
  rfl

/-- The ordinary meaning does not distinguish the two. -/
example : (double.substOne (tick 5 (lit 0))).denote algebra Env.empty =
    (letE (tick 5 (lit 0)) double).denote algebra Env.empty := by
  rw [Term.denote_substOne]
  rfl

/-- Renaming reads the environment through the renaming. -/
example (x : Nat) :
    (twoTicks.rename (fun _ => ScopedVar.succ) : signature.Term [()] ()).denoteCBV cbv
      (Env.single x) = twoTicks.denoteCBV cbv Env.empty := by
  rw [Term.denoteCBV_rename, Env.eq_empty (Env.rename _ _)]

/-- In the identity monad, the call-by-value meaning of an ordinary algebra is its ordinary
meaning. -/
example (t : signature.Term Γ ()) (η : Env (fun _ => Nat) Γ) :
    t.denoteCBV (m := Id) algebra η = t.denote algebra η := rfl

/-! ## Related readings -/

/-- One step of a run. -/
theorem run_bind {α β : Type} (c : Logged α) (f : α → Logged β) (s : List Nat) :
    (c >>= f).run s = (f (c.run s).1).run (c.run s).2 := rfl

/-- Every head relates the call-by-value reading to the ordinary one, at the value of the
run. -/
theorem cbv_relatedOn_univ :
    CBVInterpretation.RelatedOn Set.univ (fun _ v w => v = w)
      (fun _ c w => ∀ s, (c.run s).1 = w) cbv algebra := by
  rintro ⟨_, op⟩ - k k' hk
  have h0 := Env.liftRel_empty (V := fun _ : Unit => Nat) (fun _ v w => v = w)
  intro s
  cases op with
  | literal n => rfl
  | add =>
    change ((k 0 Env.empty >>= fun x => k 1 Env.empty >>= fun y => pure (x + y)).run s).1 =
      k' 0 Env.empty + k' 1 Env.empty
    rw [run_bind, run_bind, hk 0 _ _ h0, hk 1 _ _ h0]
    rfl
  | tick n =>
    change ((modify (· ++ [n]) >>= fun _ => k 0 Env.empty).run s).1 = k' 0 Env.empty
    rw [run_bind, hk 0 _ _ h0]
  | letE =>
    change ((k 0 Env.empty >>= fun x => k 1 (Env.cons x Env.empty)).run s).1 =
      k' 1 (Env.cons (k' 0 Env.empty) Env.empty)
    rw [run_bind]
    exact hk 1 _ _ (h0.cons (hk 0 _ _ h0 s)) _

/-- **Adequacy.** The value of a run is the ordinary meaning. -/
theorem run_denoteCBV (t : signature.Term Γ ()) (η : Env (fun _ => Nat) Γ) (s : List Nat) :
    ((t.denoteCBV cbv η).run s).1 = t.denote algebra η :=
  Term.denoteCBV_related (RV := fun _ v w => v = w)
    (RC := fun _ (c : Logged Nat) w => ∀ s, (c.run s).1 = w) (fun _ _ _ h _ => h)
    cbv_relatedOn_univ t (Set.subset_univ _) (fun _ _ => rfl) s

/-- The heads other than `tick` relate the call-by-value reading to a run that keeps the log. -/
theorem cbv_relatedOn_notTick :
    CBVInterpretation.RelatedOn {h : signature.Head | h.op.isTick = false} (fun _ v w => v = w)
      (fun _ c w => ∀ s, c.run s = (w, s)) cbv algebra := by
  rintro ⟨_, op⟩ hop k k' hk
  have h0 := Env.liftRel_empty (V := fun _ : Unit => Nat) (fun _ v w => v = w)
  intro s
  cases op with
  | literal n => rfl
  | add =>
    change (k 0 Env.empty >>= fun x => k 1 Env.empty >>= fun y => pure (x + y)).run s =
      (k' 0 Env.empty + k' 1 Env.empty, s)
    rw [run_bind, hk 0 _ _ h0, run_bind, hk 1 _ _ h0]
    rfl
  | tick n => cases hop
  | letE =>
    change (k 0 Env.empty >>= fun x => k 1 (Env.cons x Env.empty)).run s =
      (k' 1 (Env.cons (k' 0 Env.empty) Env.empty), s)
    rw [run_bind, hk 0 _ _ h0]
    exact hk 1 _ _ (h0.cons rfl) s

/-- A term without ticks leaves the log unchanged. -/
theorem run_denoteCBV_of_heads (t : signature.Term Γ ())
    (ht : t.heads ⊆ {h | h.op.isTick = false}) (η : Env (fun _ => Nat) Γ) (s : List Nat) :
    (t.denoteCBV cbv η).run s = (t.denote algebra η, s) :=
  Term.denoteCBV_related (RV := fun _ v w => v = w)
    (RC := fun _ (c : Logged Nat) w => ∀ s, c.run s = (w, s)) (fun _ _ _ h _ => by subst h; rfl)
    cbv_relatedOn_notTick t ht (fun _ _ => rfl) s

example : (letE (lit 2) double).heads ⊆ {h | h.op.isTick = false} := by decide

example : ((letE (lit 2) double).denoteCBV cbv Env.empty).run [7] = (4, [7]) :=
  run_denoteCBV_of_heads _ (by decide) _ _

/-- A tick changes the log, so the fragment condition cannot be dropped. -/
example : ¬ twoTicks.heads ⊆ {h | h.op.isTick = false} := by decide

example : (twoTicks.denoteCBV cbv Env.empty).run [] ≠ (twoTicks.denote algebra Env.empty, []) :=
  fun h => by cases congrArg Prod.snd h

end PolyFunTest.Scoped.CBV
