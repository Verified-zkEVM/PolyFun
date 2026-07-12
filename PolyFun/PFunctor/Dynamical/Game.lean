/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Responder
public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.PFunctor.Lens.Duoidal

/-!
# Games: challengers wired against adversaries along evaluation

A **game** pairs a challenger, whose interface is an internal hom `q ⊸ r`
(Spivak–Niu Ex 4.78), with an adversary playing `q`. Wiring the two along the
evaluation lens `Lens.eval : (q ⊸ r) ⊗ q ⟹ r` (`DynSystem.game`) yields a single
system over the outer interface `r`; equivalently — definitionally — it is the
uncurried challenger applied to the adversary (`game_eq_uncurry`), the
tensor–hom adjunction in dynamical clothing. When the challenger is a
`Responder` (`r = X`) the game is closed and runs autonomously
(`DynSystem.closedGame`), the deterministic shadow of VCVio's `wireKStep`
wiring. There is no separate scored-game structure: a win readout is a state (or
Moore) readout on the closed run, and the win-bit form is the
`r := monomial Bool PUnit` instance of `game`.

Monadic runs against handlers are provided in two strengths: `kleisliStep` /
`kleisliIterate` drive a system with a stateless handler in a monad `m` (VCVio's
`wireKStep` / `wireKIterate` are the `m := SPMF` instances), and `stepWith` /
`iterWith` drive it with a *stateful* handler in `StateT σ m`, the handler state
first in the pair. The two agree along `StateT.lift` (`stepWith_lift`), and at
`m := Id` a responder's handler recovers the closed game
(`stepWith_toStateHandler`). The load-bearing export is
`PointedMachine.runWith_run_succ_of_output_eq_none`, the machine-vs-responder
step law that unrolls a machine's fuelled `runWith` through `stepWith` of its
dynamical core.

Two-phase (commit-then-guess) games arrive by substitution: `Lens.eval₂` runs
two evaluations in sequence after reshuffling along the duoidal interchange
`Lens.duoidalLens` (Spivak–Niu Eq 6.86), `DynSystem.orderPair` orders two
single-phase adversaries into a `q₁ ◃ q₂` player along `Lens.orderingLens`
(Ex 6.85), and `DynSystem.game₂` wires a two-phase challenger against a
two-phase adversary. `Lens.compOuter`, `Lens.compInner`, and `Lens.compPullback`
(Ex 6.40) are the
intro/elim rules for the two-phase challenger interface.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂

namespace PFunctor

namespace DynSystem

/-! ## The game former -/

section Game

variable {S : Type u} {T : Type v} {q r : PFunctor.{uA, uB}}

/-- Wire a challenger over the internal hom `q ⊸ r` against an adversary playing
`q`, along the evaluation lens (Spivak–Niu Ex 4.78): at each step the challenger
commits to a lens `q ⟹ r`, the adversary picks a `q`-position, and the composite
exposes the resulting `r`-position; the incoming `r`-direction is answered back
through the committed lens. VCVio's `Challenger`-vs-adversary wiring is the
Kleisli consumer of this former. -/
def game (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) : DynSystem (S × T) r :=
  wire₂ (Lens.eval q r) chal adv

@[simp] theorem game_expose (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q)
    (s : S) (t : T) :
    (game chal adv).expose (s, t) = (chal.expose s).toFunA (adv.expose t) := rfl

@[simp] theorem game_update (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q)
    (s : S) (t : T) (d : r.B ((game chal adv).expose (s, t))) :
    (game chal adv).update (s, t) d
      = (chal.update s ⟨adv.expose t, d⟩,
          adv.update t ((chal.expose s).toFunB (adv.expose t) d)) := rfl

theorem game_eq_wire₂ (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    game chal adv = wire₂ (Lens.eval q r) chal adv := rfl

end Game

/-- The game former is evaluation of the uncurried challenger: wiring along
`Lens.eval` is the tensor–hom adjunction in dynamical clothing. Stated with the
challenger's state universe identified with the interface universes, as
`Lens.uncurry` requires. -/
theorem game_eq_uncurry {S : Type u} {T : Type v} {q r : PFunctor.{u, u}}
    (chal : DynSystem S (q ⊸ r)) (adv : DynSystem T q) :
    game chal adv = (Lens.comp (Lens.uncurry chal) (Lens.id (selfMonomial S) ⊗ₗ adv) :
      Lens (selfMonomial S ⊗ selfMonomial T) r) := rfl

/-! ## Closed games -/

section Game

variable {S : Type u} {T : Type v} {q : PFunctor.{uA, uB}}

/-- Close a responder against an adversary: the `r = X` instance of `game` runs
autonomously, so the pair steps by "adversary queries, responder answers". This
is the deterministic shadow of VCVio's `wireKStep`; a win condition is a state
readout on the closed run (for a Moore win bit, instantiate `game` at
`r := monomial Bool PUnit` instead). -/
def closedGame (R : Responder S q) (adv : DynSystem T q) : Closed (S × T) :=
  game R adv

@[simp] theorem closedGame_step (R : Responder S q) (adv : DynSystem T q) (s : S) (t : T) :
    (closedGame R adv).step (s, t)
      = (R.next s (adv.expose t), adv.update t (R.answer s (adv.expose t))) := rfl

end Game

/-! ## Kleisli runs against monadic handlers -/

section Kleisli

variable {q : PFunctor.{uA, u}} {S σ : Type u} {m : Type u → Type v} [Monad m]

/-- One step of a system driven by a stateless monadic handler: resolve the
exposed position in `m` and update. VCVio's `wireKStep` is the `m := SPMF`
instance. -/
def kleisliStep (h : Handler m q) (A : DynSystem S q) (s : S) : m S :=
  (fun d => A.update s d) <$> h (A.expose s)

/-- `n` monadic steps of a system against a stateless handler. VCVio's
`wireKIterate` is the `m := SPMF` instance. -/
def kleisliIterate (h : Handler m q) (A : DynSystem S q) : ℕ → S → m S
  | 0, s => pure s
  | n + 1, s => kleisliStep h A s >>= kleisliIterate h A n

@[simp] theorem kleisliIterate_zero (h : Handler m q) (A : DynSystem S q) (s : S) :
    kleisliIterate h A 0 s = pure s := rfl

theorem kleisliIterate_succ (h : Handler m q) (A : DynSystem S q) (n : ℕ) (s : S) :
    kleisliIterate h A (n + 1) s = kleisliStep h A s >>= kleisliIterate h A n := rfl

/-- One step of a system driven by a *stateful* handler: the handler threads its
own state `σ` alongside the system's, handler state first in the pair. -/
def stepWith (h : Handler (StateT σ m) q) (A : DynSystem S q) (p : σ × S) : m (σ × S) :=
  (fun dt => (dt.2, A.update p.2 dt.1)) <$> h (A.expose p.2) p.1

/-- `n` steps of a system against a stateful handler, threading the handler
state. -/
def iterWith (h : Handler (StateT σ m) q) (A : DynSystem S q) : ℕ → σ × S → m (σ × S)
  | 0, p => pure p
  | n + 1, p => stepWith h A p >>= iterWith h A n

@[simp] theorem iterWith_zero (h : Handler (StateT σ m) q) (A : DynSystem S q) (p : σ × S) :
    iterWith h A 0 p = pure p := rfl

theorem iterWith_succ (h : Handler (StateT σ m) q) (A : DynSystem S q) (n : ℕ) (p : σ × S) :
    iterWith h A (n + 1) p = stepWith h A p >>= iterWith h A n := rfl

/-- A stateless handler lifted into the state monad steps the system as
`kleisliStep` does and carries the handler state unchanged. -/
theorem stepWith_lift [LawfulMonad m] (h₀ : Handler m q) (A : DynSystem S q) (p : σ × S) :
    stepWith (fun a => StateT.lift (h₀ a)) A p
      = (fun s' => (p.1, s')) <$> kleisliStep h₀ A p.2 := by
  simp only [stepWith, kleisliStep, StateT.lift, map_eq_pure_bind, bind_assoc, pure_bind]

/-- A lifted stateless handler runs as `kleisliIterate` does, carrying the
handler state unchanged. -/
theorem iterWith_lift [LawfulMonad m] (h₀ : Handler m q) (A : DynSystem S q) (n : ℕ)
    (p : σ × S) :
    iterWith (fun a => StateT.lift (h₀ a)) A n p
      = (fun s' => (p.1, s')) <$> kleisliIterate h₀ A n p.2 := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iterWith_succ, kleisliIterate_succ, stepWith_lift]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun s' => ih (p.1, s')

/-- Running a system against a responder's stateful handler is stepping the
closed game: `stepWith` at `m := Id` is `closedGame`'s step. -/
theorem stepWith_toStateHandler (R : Responder σ q) (A : DynSystem S q) (p : σ × S) :
    stepWith (m := Id) R.toStateHandler A p = (closedGame R A).step p := rfl

/-- The `Id` run against a responder's stateful handler computes the closed
game's trajectory. -/
theorem iterWith_toStateHandler (R : Responder σ q) (A : DynSystem S q) (n : ℕ) (p : σ × S) :
    iterWith (m := Id) R.toStateHandler A n p = pure ((closedGame R A).iterate p n) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change iterWith (m := Id) R.toStateHandler A n (stepWith (m := Id) R.toStateHandler A p) = _
    rw [stepWith_toStateHandler, ih]
    rfl

end Kleisli

end DynSystem

/-! ## The machine-vs-responder step law -/

namespace PointedMachine

section RunBridge

variable {q : PFunctor.{uA, u}} {α β : Type u} {σ : Type u} {m : Type u → Type v} [Monad m]

/-- **The machine-vs-responder step law**: on an unresolved state, one unit of
fuel of a machine's `runWith` against a stateful handler — read in
state-transformer form — is one `DynSystem.stepWith` of the machine's dynamical
core, bound into the rest of the run. Downstream machine-game step lemmas are
instances of this law at concrete monads (`m := SPMF` for VCVio's wiring). -/
theorem runWith_run_succ_of_output_eq_none [LawfulMonad m] (M : PointedMachine q α β)
    (h : Handler (StateT σ m) q) {s : M.State} (hs : M.output s = none) (k : ℕ) (t : σ) :
    (M.runWith h (k + 1) s).run t
      = DynSystem.stepWith h M.toDynSystem (t, s) >>= fun p => (M.runWith h k p.2).run p.1 := by
  rw [M.runWith_succ_of_output_eq_none h hs k]
  simp only [DynSystem.stepWith, bind_map_left]
  rfl

end RunBridge

end PointedMachine

/-! ## Two-phase games

Commit-then-guess games by substitution: the challenger plays
`(q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂)` — a phase-one responder lens whose continuation, fed the
phase-one transcript, is a phase-two responder lens — and the adversary plays
`q₁ ◃ q₂`. -/

namespace Lens

/-- The **two-phase evaluation wiring**: reshuffle a two-phase challenger against
a two-phase adversary along the duoidal interchange `duoidalLens` (Spivak–Niu
Eq 6.86), so the phase-one pair and phase-two pair each meet in an evaluation
lens (Ex 4.78), run in sequence. -/
def eval₂ (q₁ r₁ q₂ r₂ : PFunctor.{uA, uB}) :
    Lens (((q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂)) ⊗ (q₁ ◃ q₂)) (r₁ ◃ r₂) :=
  (eval q₁ r₁ ◃ₗ eval q₂ r₂) ∘ₗ duoidalLens (q₁ ⊸ r₁) (q₂ ⊸ r₂) q₁ q₂

end Lens

namespace DynSystem

section OrderPair

variable {T₁ : Type u} {T₂ : Type v} {q₁ : PFunctor.{uA₁, uB₁}} {q₂ : PFunctor.{uA₂, uB₂}}

/-- Order two systems into a single two-phase system along `Lens.orderingLens`
(Spivak–Niu Ex 6.85): the pair plays `q₁ ◃ q₂`, phase one first. **The second
phase cannot see the first phase's answer within one composite step**: before
ordering, the two phases were simultaneous (`tensor`), and the ordering lens
makes the phase-two position constant in the phase-one direction. A
same-step-adaptive second phase (e.g. a guesser reading the commit phase's
answer) must instead be built directly as a system over `q₁ ◃ q₂`. -/
def orderPair (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂) :
    DynSystem (T₁ × T₂) (q₁ ◃ q₂) :=
  wrap (Lens.orderingLens q₁ q₂) (A₁.tensor A₂)

@[simp] theorem orderPair_expose (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂)
    (st : T₁ × T₂) :
    (orderPair A₁ A₂).expose st = ⟨A₁.expose st.1, fun _ => A₂.expose st.2⟩ := rfl

@[simp] theorem orderPair_update (A₁ : DynSystem T₁ q₁) (A₂ : DynSystem T₂ q₂)
    (st : T₁ × T₂) (d : (q₁ ◃ q₂).B ((orderPair A₁ A₂).expose st)) :
    (orderPair A₁ A₂).update st d = (A₁.update st.1 d.1, A₂.update st.2 d.2) := rfl

end OrderPair

section Game₂

variable {S : Type u} {T : Type v} {q₁ r₁ q₂ r₂ : PFunctor.{uA, uB}}

/-- Wire a two-phase challenger against a two-phase adversary along
`Lens.eval₂`: commit phase, then guess phase, exposed on the outer interface
`r₁ ◃ r₂`. The challenger's interface has the direct composite-lens accessors
`compOuter`, `compInner`, and `compPullback` (Spivak–Niu Ex 6.40) as its
elimination rules; VCVio's
`Challenger₂` is the Kleisli consumer of this former. -/
def game₂ (chal : DynSystem S ((q₁ ⊸ r₁) ◃ (q₂ ⊸ r₂))) (adv : DynSystem T (q₁ ◃ q₂)) :
    DynSystem (S × T) (r₁ ◃ r₂) :=
  wire₂ (Lens.eval₂ q₁ r₁ q₂ r₂) chal adv

end Game₂

end DynSystem

end PFunctor
