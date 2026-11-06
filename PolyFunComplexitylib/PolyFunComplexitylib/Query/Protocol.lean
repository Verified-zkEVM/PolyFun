/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexity.Computability.Communication.Protocol
public import PolyFunComplexitylib.Query.DecisionTree

/-!
# Communication protocols as free programs

A deterministic two-party protocol is a free program over the *message interface*: a position is a
one-bit message function owned by Alice (`X → Bool`) or by Bob (`Y → Bool`), and its answer is the
bit sent. Running the protocol on inputs `x` and `y` answers Alice's messages at `x` and Bob's at
`y`, so it is the fold of the free program against the copairing of the two players' sections.

`Cslib.Communication.Protocol.equivFreeM` identifies complexitylib's protocols with these free
programs, matches `run` with that fold and `depth` with `PFunctor.FreeM.IsTotalRollBound`.

When the players' input types share a universe, the message interface is the coproduct of the two
players' one-bit interfaces up to the equivalence of their direction families; the positions are
defined here as a sum so that the inputs keep independent universes.
-/

@[expose] public section

universe u v w

namespace Cslib.Communication.Protocol

open PFunctor

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The message interface of a two-party protocol: a one-bit message function of Alice's or Bob's
input, answered by the bit sent. -/
abbrev messagePFunctor (X : Type u) (Y : Type v) : PFunctor.{max u v, 0} :=
  ⟨(X → Bool) ⊕ (Y → Bool), fun _ => Bool⟩

/-- The answer to a message when Alice holds `x` and Bob holds `y`. -/
def answer (x : X) (y : Y) : (m : (messagePFunctor X Y).A) → (messagePFunctor X Y).B m :=
  Sum.elim (fun send => send x) (fun send => send y)

/-- A protocol as a free program over its message interface. -/
def toFreeM : Protocol X Y Z → (messagePFunctor X Y).FreeM Z
  | output z => .pure z
  | alice send p₀ p₁ => .liftBind (.inl send) fun b => cond b p₁.toFreeM p₀.toFreeM
  | bob send p₀ p₁ => .liftBind (.inr send) fun b => cond b p₁.toFreeM p₀.toFreeM

/-- A free program over the message interface as a protocol. -/
def ofFreeM : (messagePFunctor X Y).FreeM Z → Protocol X Y Z
  | .pure z => output z
  | .liftBind (.inl send) k => alice send (ofFreeM (k false)) (ofFreeM (k true))
  | .liftBind (.inr send) k => bob send (ofFreeM (k false)) (ofFreeM (k true))

/-- Deterministic protocols are exactly the free programs of the message interface. -/
def equivFreeM : Protocol X Y Z ≃ (messagePFunctor X Y).FreeM Z where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv p := by
    induction p with
    | output => rfl
    | alice send p₀ p₁ ih₀ ih₁ =>
      change alice send (ofFreeM p₀.toFreeM) (ofFreeM p₁.toFreeM) = _
      rw [ih₀, ih₁]
    | bob send p₀ p₁ ih₀ ih₁ =>
      change bob send (ofFreeM p₀.toFreeM) (ofFreeM p₁.toFreeM) = _
      rw [ih₀, ih₁]
  right_inv t := by
    induction t with
    | pure => rfl
    | lift_bind m k ih =>
      rcases m with send | send
      all_goals
        change FreeM.liftBind _ (fun b => cond b (ofFreeM (k true)).toFreeM
          (ofFreeM (k false)).toFreeM) = FreeM.liftBind _ k
        congr 1
        funext b
        cases b
        · exact ih false
        · exact ih true

@[simp] theorem equivFreeM_apply (p : Protocol X Y Z) : equivFreeM p = p.toFreeM := rfl

@[simp] theorem equivFreeM_symm_apply (t : (messagePFunctor X Y).FreeM Z) :
    equivFreeM.symm t = ofFreeM t := rfl

/-- Running a protocol is folding its free program against the copaired answers of the two
players. -/
theorem run_eq_foldFreeM (p : Protocol X Y Z) (x : X) (y : Y) :
    p.run x y = p.toFreeM.foldFreeM id fun m k => k (answer x y m) := by
  induction p with
  | output => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    change cond (send x) (p₁.run x y) (p₀.run x y) =
      FreeM.foldFreeM id _ (cond (send x) p₁.toFreeM p₀.toFreeM)
    cases send x
    · exact ih₀
    · exact ih₁
  | bob send p₀ p₁ ih₀ ih₁ =>
    change cond (send y) (p₁.run x y) (p₀.run x y) =
      FreeM.foldFreeM id _ (cond (send y) p₁.toFreeM p₀.toFreeM)
    cases send y
    · exact ih₀
    · exact ih₁

/-- The number of bits a protocol sends in the worst case is the total roll bound of its free
program. -/
theorem depth_le_iff_isTotalRollBound (p : Protocol X Y Z) (n : ℕ) :
    p.depth ≤ n ↔ p.toFreeM.IsTotalRollBound n := by
  induction p generalizing n with
  | output => simp [toFreeM, FreeM.isTotalRollBound_pure]
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [toFreeM, FreeM.isTotalRollBound_liftBind_iff, Bool.forall_bool]
    simp only [depth_alice, Bool.cond_false, Bool.cond_true, ← ih₀, ← ih₁]
    omega
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [toFreeM, FreeM.isTotalRollBound_liftBind_iff, Bool.forall_bool]
    simp only [depth_bob, Bool.cond_false, Bool.cond_true, ← ih₀, ← ih₁]
    omega

end Cslib.Communication.Protocol
