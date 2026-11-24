/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import PolyFun.IPFunctor.Scoped.CostD.Semantics

/-!
# Erasure of the ticks of D

The evaluator of D with its ticks erased is related to the denotation (`Tm.eval_erase_rel`). The
values of the two readings differ at function types, since the closures of the evaluator tick, so
the statement is a logical relation `VRel`: equality at the ground types, the natural numbers and
unit, componentwise at products and sums, and at a function type, related arguments go to
programs that are related by `FreeRel` after erasing the ticks. At a ground type the relation is
equality, so the erased evaluation of a term is its denotation (`Tm.erase_eval`).

The proof is an instance of `Term.denoteCBV_related`. Its right-hand side is an ordinary
interpretation, so the denotation is read as one: a call-by-value algebra in a monad `m` gives an
ordinary algebra whose carrier at a sort is the computations in `m` and whose bound variables
receive their values by `pure` (`CBVInterpretation.toInterpretation`), with the same meaning
(`Term.denote_toInterpretation`).

## Main definitions

* `Env.pureEach`, `CBVInterpretation.toInterpretation`: the environment of returned values and
  the ordinary algebra of a call-by-value algebra.
* `VRel`: the logical relation between values of the evaluator and of the denotation.
* `RV`, `RC`: its lifts to a returned value and to a computation, against a computation of the
  denotation.

## Main results

* `Term.denote_toInterpretation`: the ordinary reading of `alg.toInterpretation` in an
  environment of returned values is the call-by-value reading of `alg`.
* `Tm.eval_erase_rel`: in related environments, the evaluator with its ticks erased and the
  denotation are related.
* `Tm.erase_eval`: at a ground type, the evaluator with its ticks erased is the denotation.
* `Tm.erase_eval_closed`: the same for a closed term.
-/

@[expose] public section

universe u v w z z'

namespace IPFunctor.ScopedSignature

section ToInterpretation

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {m : Type z → Type z'} {V : S → Type z}
  [Pure m]

/-- Each value of an environment, returned by `pure`. -/
def Env.pureEach {Γ : List S} (η : Env V Γ) : Env (fun a => m (V a)) Γ :=
  fun a x => pure (η a x)

/-- Returning the values of a block and of an environment by `pure` returns the values of the
appended environment. -/
theorem Env.append_pureEach {Γ : List S} :
    {Ξ : List S} → (ξ : Env V Ξ) → (η : Env V Γ) →
      Env.append (Env.pureEach (m := m) ξ) (Env.pureEach η) = Env.pureEach (Env.append ξ η)
  | [], _, _ => rfl
  | _ :: _, ξ, η => by
    funext a x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (Env.append_pureEach (fun _ y => ξ _ y.succ) η) a) x

/-- The ordinary algebra of a call-by-value algebra: its carrier at a sort is the computations
of values of the sort, and each bound variable receives its value by `pure`. -/
def CBVInterpretation.toInterpretation (alg : CBVInterpretation σ m V) :
    Interpretation σ (fun a => m (V a)) :=
  fun op k => alg op fun p ξ => k p (Env.pureEach ξ)

/-- The ordinary reading of `alg.toInterpretation` in an environment of returned values is the
call-by-value reading of `alg`. -/
theorem Term.denote_toInterpretation (alg : CBVInterpretation σ m V) {Γ : List S} {a : S}
    (t : σ.Term Γ a) (η : Env V Γ) :
    t.denote alg.toInterpretation (Env.pureEach η) = t.denoteCBV alg η := by
  induction t using Term.inductionOn with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [denote_node, denoteCBV_node]
    change alg op _ = alg op _
    congr 1
    funext p ξ
    dsimp only
    rw [Env.append_pureEach, ih p]

end ToInterpretation

end IPFunctor.ScopedSignature

namespace IPFunctor.CostD

open IPFunctor.ScopedSignature PFunctor

variable {B : Ground.{u}} {E : Effect B} {ω : Type u}

/-- The logical relation between the values of the evaluator and of the denotation: equality at
the ground types, unit and the natural numbers, componentwise at products and sums, and at a
function type, related arguments go to programs related by `FreeRel` after erasing the ticks. -/
def VRel (E : Effect B) (ω : Type u) :
    (a : Ty B.G) → Val B (Ticked E.toPFunctor ω) a → Val B E.toPFunctor a → Prop
  | .base _, v, w => v = w
  | .unit, _, _ => True
  | .nat, v, w => v = w
  | .prod a b, v, w => VRel E ω a v.1 w.1 ∧ VRel E ω b v.2 w.2
  | .sum a b, v, w => Sum.LiftRel (VRel E ω a) (VRel E ω b) v w
  | .arr a b, v, w => ∀ x y, VRel E ω a x y →
      FreeRel E.toPFunctor (VRel E ω b) (erase (v x)) (w y)

section Rel

variable {α β γ δ : Type u} {R : α → β → Prop} {R' : γ → δ → Prop}

/-- Related values returned by `pure` are related after erasure. -/
theorem freeRel_erase_pure {a : α} {b : β} (h : R a b) :
    FreeRel E.toPFunctor R (erase (pure a : PFunctor.FreeM (Ticked E.toPFunctor ω) α))
      (pure b) :=
  .pure h

/-- Related programs continued by related continuations are related after erasure. -/
theorem freeRel_erase_bind {x : PFunctor.FreeM (Ticked E.toPFunctor ω) α}
    {y : PFunctor.FreeM E.toPFunctor β} {f : α → PFunctor.FreeM (Ticked E.toPFunctor ω) γ}
    {g : β → PFunctor.FreeM E.toPFunctor δ} (hxy : FreeRel E.toPFunctor R (erase x) y)
    (hfg : ∀ a b, R a b → FreeRel E.toPFunctor R' (erase (f a)) (g b)) :
    FreeRel E.toPFunctor R' (erase (x >>= f)) (y >>= g) := by
  rw [erase_bind]
  exact FreeRel.bind hxy hfg

/-- A tick is erased: a tick before a program is related to an answered step before a related
program. -/
theorem freeRel_erase_tick {w : ω} {x : PFunctor.FreeM (Ticked E.toPFunctor ω) γ}
    {y : PFunctor.FreeM E.toPFunctor δ} (h : FreeRel E.toPFunctor R' (erase x) y) :
    FreeRel E.toPFunctor R' (erase (tick w >>= fun _ => x))
      (pure PUnit.unit >>= fun _ => y) :=
  freeRel_erase_bind (R := fun _ _ => True) (.pure trivial) fun _ _ _ => h

end Rel

variable (π : Price B ω)

/-- The iterations of related functions from related seeds are related after erasure. -/
theorem freeRel_erase_iterT {c : Ty B.G} {f : Val B (Ticked E.toPFunctor ω) (.arr c c)}
    {f' : Val B E.toPFunctor (.arr c c)} (hf : VRel E ω (.arr c c) f f')
    {i : Val B (Ticked E.toPFunctor ω) c} {i' : Val B E.toPFunctor c} (hi : VRel E ω c i i')
    (n : ℕ) :
    FreeRel E.toPFunctor (VRel E ω c) (erase (iterT (Machine.timed E ω) π f i n))
      (iterT (Machine.untimed E) (Price.unit B) f' i' n) := by
  induction n with
  | zero => exact .pure hi
  | succ n ih => exact freeRel_erase_bind ih fun s s' hs => freeRel_erase_tick (hf s s' hs)

/-- The relation between computed values and computations of the denotation: the computation
returns a related value. -/
abbrev RV (E : Effect B) (ω : Type u) (a : Ty B.G) (v : Val B (Ticked E.toPFunctor ω) a)
    (w : PFunctor.FreeM E.toPFunctor (Val B E.toPFunctor a)) : Prop :=
  FreeRel E.toPFunctor (VRel E ω a) (pure v) w

/-- The relation between computations of the evaluator and of the denotation: related after
erasing the ticks. -/
abbrev RC (E : Effect B) (ω : Type u) (a : Ty B.G)
    (c : PFunctor.FreeM (Ticked E.toPFunctor ω) (Val B (Ticked E.toPFunctor ω) a))
    (w : PFunctor.FreeM E.toPFunctor (Val B E.toPFunctor a)) : Prop :=
  FreeRel E.toPFunctor (VRel E ω a) (erase c) w

/-- The empty environments are related by `RV`. -/
theorem liftRel_rv_empty :
    Env.LiftRel (RV E ω) Env.empty (Env.pureEach (m := PFunctor.FreeM E.toPFunctor)
      (Env.empty : Env (Val B E.toPFunctor) [])) :=
  fun _ x => nomatch x

/-- Related values give related environments of one variable. -/
theorem liftRel_rv_cons {a : Ty B.G} {x : Val B (Ticked E.toPFunctor ω) a}
    {y : Val B E.toPFunctor a} (h : VRel E ω a x y) :
    Env.LiftRel (RV E ω) (Env.cons x Env.empty)
      (Env.pureEach (m := PFunctor.FreeM E.toPFunctor) (Env.cons y Env.empty)) := by
  rintro _ (_ | x)
  · exact .pure h
  · nomatch x

/-- The constructors of D without effects are related at every head. -/
theorem coreCBV_relatedOn :
    CBVInterpretation.RelatedOn Set.univ (RV E ω) (RC E ω) (coreCBV (Machine.timed E ω) π)
      (CBVInterpretation.toInterpretation (coreCBV (Machine.untimed E) (Price.unit B))) := by
  rintro ⟨a, op⟩ - k k' hk
  have h0 := liftRel_rv_empty (E := E) (ω := ω)
  cases op with
  | lam a b => exact freeRel_erase_pure fun x y hxy => hk 0 _ _ (liftRel_rv_cons hxy)
  | app a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun g g' hg =>
      freeRel_erase_bind (hk 1 _ _ h0) fun x x' hx => freeRel_erase_tick (hg x x' hx)
  | letE a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun x x' hx =>
      freeRel_erase_tick (hk 1 _ _ (liftRel_rv_cons hx))
  | seq a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun _ _ _ => freeRel_erase_tick (hk 1 _ _ h0)
  | lit g v => exact freeRel_erase_pure rfl
  | natLit n => exact freeRel_erase_pure rfl
  | prim p =>
    refine freeRel_erase_bind (hk 0 _ _ h0) fun x x' hx => ?_
    cases hx
    exact freeRel_erase_tick (freeRel_erase_pure rfl)
  | unit => exact freeRel_erase_pure trivial
  | pair a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun x x' hx =>
      freeRel_erase_bind (hk 1 _ _ h0) fun y y' hy => freeRel_erase_pure ⟨hx, hy⟩
  | fst a b => exact freeRel_erase_bind (hk 0 _ _ h0) fun _ _ hp => freeRel_erase_pure hp.1
  | snd a b => exact freeRel_erase_bind (hk 0 _ _ h0) fun _ _ hp => freeRel_erase_pure hp.2
  | inl a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun _ _ hx => freeRel_erase_pure (Sum.LiftRel.inl hx)
  | inr a b =>
    exact freeRel_erase_bind (hk 0 _ _ h0) fun _ _ hy => freeRel_erase_pure (Sum.LiftRel.inr hy)
  | case a b c =>
    refine freeRel_erase_bind (hk 0 _ _ h0) fun s s' hs => freeRel_erase_tick ?_
    cases hs with
    | inl h => exact hk 1 _ _ (liftRel_rv_cons h)
    | inr h => exact hk 2 _ _ (liftRel_rv_cons h)
  | iter c =>
    refine freeRel_erase_bind (hk 0 _ _ h0) fun n n' hn => ?_
    cases hn
    exact freeRel_erase_bind (hk 1 _ _ h0) fun f f' hf =>
      freeRel_erase_bind (hk 2 _ _ h0) fun i i' hi => freeRel_erase_iterT π hf hi _

/-- The calls are related at every head: erasing keeps them. -/
theorem queryCBV_relatedOn :
    CBVInterpretation.RelatedOn Set.univ (RV E ω) (RC E ω) (queryCBV (Machine.timed E ω))
      (CBVInterpretation.toInterpretation (queryCBV (Machine.untimed E))) := by
  rintro ⟨a, op⟩ - k k' hk
  cases op with
  | query e =>
    refine freeRel_erase_bind (hk 0 _ _ liftRel_rv_empty) fun x x' hx => ?_
    cases hx
    exact .liftBind _ fun _ => .pure rfl

/-- The call-by-value reading of D is related at every head. -/
theorem cbv_relatedOn :
    CBVInterpretation.RelatedOn Set.univ (RV E ω) (RC E ω) (cbv (Machine.timed E ω) π)
      (CBVInterpretation.toInterpretation (cbv (Machine.untimed E) (Price.unit B))) := by
  rintro ⟨a, op | op⟩ - k k' hk
  · exact coreCBV_relatedOn π ⟨a, op⟩ trivial k k' hk
  · exact queryCBV_relatedOn ⟨a, op⟩ trivial k k' hk

namespace Tm

variable {Γ : List (Ty B.G)}

/-- **Tick erasure.** In related environments, the evaluator with its ticks erased and the
denotation are related. -/
theorem eval_erase_rel {a : Ty B.G} (t : Tm E Γ a) {η : Env (Val B (Ticked E.toPFunctor ω)) Γ}
    {ζ : Env (Val B E.toPFunctor) Γ} (hη : Env.LiftRel (VRel E ω) η ζ) :
    FreeRel E.toPFunctor (VRel E ω a) (erase (t.eval π η)) (t.den ζ) := by
  have h := Term.denoteCBV_related (RV := RV E ω) (RC := RC E ω)
    (alg' := CBVInterpretation.toInterpretation (cbv (Machine.untimed E) (Price.unit B)))
    (fun _ _ _ h => h) (cbv_relatedOn π) t (Set.subset_univ _)
    (ζ := Env.pureEach ζ) fun b x => .pure (hη b x)
  rwa [Term.denote_toInterpretation] at h

/-- At a ground type, the evaluator with its ticks erased is the denotation. -/
theorem erase_eval {g : B.G} (t : Tm E Γ (.base g)) {η : Env (Val B (Ticked E.toPFunctor ω)) Γ}
    {ζ : Env (Val B E.toPFunctor) Γ} (hη : Env.LiftRel (VRel E ω) η ζ) :
    erase (t.eval π η) = t.den ζ :=
  freeRel_eq_iff.mp (eval_erase_rel π t hη)

/-- A closed term of a ground type: the evaluator with its ticks erased is the denotation. -/
theorem erase_eval_closed {g : B.G} (t : Tm E [] (.base g)) :
    erase (t.eval π Env.empty) = t.den Env.empty :=
  erase_eval π t (Env.liftRel_empty _)

end Tm

end IPFunctor.CostD
