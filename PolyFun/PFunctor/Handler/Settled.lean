/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Charge

/-!
# Settled runs of partial handlers

A partial handler `p : Handler Option P` answers some calls and declines the rest. A program `x`
is *settled* by `p` at `v` when `x.liftM p = some v`: every call `x` reaches is answered, and the
answers lead to `v`. A cache read as a partial answer function is the typical partial handler.

A settled run determines the runs of other handlers that agree with `p` where `p` answers:

* a handler that returns `p`'s answer purely runs `x` as `pure v`
  (`FreeM.liftM_eq_pure_of_liftM_eq_some`); with `Option` as the target, this says a settled
  program stays settled when `p` is extended (`FreeM.liftM_eq_some_of_le`);
* a stateful handler that returns `p`'s answer at a state `s` without changing it runs `x` from `s`
  as `pure (v, s)` (`FreeM.run_liftM_eq_pure_of_liftM_eq_some`): the run frames that state;
* charging `p` in a writer logs the charge of the one path `x` follows, which is the path of any
  total choice of answers that extends `p` (`FreeM.run_liftM_withChargeW_eq_of_liftM_eq_some`),
  and `v` is that path's output (`FreeM.output_ofHandler_eq_of_liftM_eq_some`).
-/

public section

universe uA uB v w

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uB}

/-- One step of a settled run: the first call is answered, and the continuation is settled. -/
theorem exists_eq_some_of_liftM_liftBind_eq_some (p : Handler Option P) {a : P.A}
    {r : P.B a → FreeM P α} {v : α} (hx : (FreeM.liftBind a r).liftM p = some v) :
    ∃ b, p a = some b ∧ (r b).liftM p = some v :=
  Option.bind_eq_some_iff.mp hx

/-- **A settled program runs purely.** If `h` returns `p`'s answer purely wherever `p` answers,
then a program that `p` settles at `v` runs through `h` as `pure v`. -/
theorem liftM_eq_pure_of_liftM_eq_some {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    (p : Handler Option P) (h : Handler m P) (hp : ∀ a b, p a = some b → h a = pure b)
    {x : FreeM P α} {v : α} (hx : x.liftM p = some v) : x.liftM h = pure v := by
  induction x using FreeM.rec generalizing v with
  | pure a =>
    cases Option.some.inj hx
    rfl
  | liftBind a r ih =>
    obtain ⟨b, hb, hr⟩ := exists_eq_some_of_liftM_liftBind_eq_some p hx
    change h a >>= (fun b => (r b).liftM h) = pure v
    rw [hp a b hb, LawfulMonad.pure_bind]
    exact ih b hr

/-- **Settled programs stay settled under extension.** If `q` answers as `p` wherever `p` answers,
a program that `p` settles at `v` is settled by `q` at `v`. -/
theorem liftM_eq_some_of_le (p q : Handler Option P) (hpq : ∀ a b, p a = some b → q a = some b)
    {x : FreeM P α} {v : α} (hx : x.liftM p = some v) : x.liftM q = some v :=
  liftM_eq_pure_of_liftM_eq_some p q hpq hx

/-- **A settled program frames a stateful run.** If `h` returns `p`'s answer at the state `s`
without changing it wherever `p` answers, then a program that `p` settles at `v` runs through `h`
from `s` as `pure (v, s)`. -/
theorem run_liftM_eq_pure_of_liftM_eq_some {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    {σ : Type uB} (p : Handler Option P) (h : Handler (StateT σ m) P) (s : σ)
    (hp : ∀ a b, p a = some b → (h a).run s = pure (b, s))
    {x : FreeM P α} {v : α} (hx : x.liftM p = some v) : (x.liftM h).run s = pure (v, s) := by
  induction x using FreeM.rec generalizing v with
  | pure a =>
    cases Option.some.inj hx
    rfl
  | liftBind a r ih =>
    obtain ⟨b, hb, hr⟩ := exists_eq_some_of_liftM_liftBind_eq_some p hx
    change (h a >>= fun b => (r b).liftM h).run s = pure (v, s)
    rw [StateT.run_bind, hp a b hb, LawfulMonad.pure_bind]
    exact ih b hr

/-- **The charge of a settled run.** Charging a partial handler in a writer, a program that it
settles at `v` returns `v` and logs the charge of the path it follows. That path is the path of
any total choice of answers `choose` that agrees with `p` where `p` answers. -/
theorem run_liftM_withChargeW_eq_of_liftM_eq_some {ω : Type uB} [AddMonoid ω]
    (p : Handler Option P) (c : P.A → ω) (choose : (a : P.A) → P.B a)
    (hchoose : ∀ a b, p a = some b → choose a = b)
    {x : FreeM P α} {v : α} (hx : x.liftM p = some v) :
    (x.liftM (p.withChargeW c)).run =
      some (v, Multiplicative.ofAdd (Path.charge c x (Path.ofHandler choose x))) := by
  induction x using FreeM.rec generalizing v with
  | pure a =>
    cases Option.some.inj hx
    rfl
  | liftBind a r ih =>
    obtain ⟨b, hb, hr⟩ := exists_eq_some_of_liftM_liftBind_eq_some p hx
    obtain rfl := hchoose a b hb
    change ((p.withChargeW c a >>= fun b => (r b).liftM (p.withChargeW c)).run) = _
    simp [Handler.run_withChargeW, hb, ih _ hr]
    rfl

/-- The output of a settled run is the output along the path of any total choice that agrees with
the partial handler. -/
theorem output_ofHandler_eq_of_liftM_eq_some (p : Handler Option P) (choose : (a : P.A) → P.B a)
    (hchoose : ∀ a b, p a = some b → choose a = b)
    {x : FreeM P α} {v : α} (hx : x.liftM p = some v) :
    output x (Path.ofHandler choose x) = v := by
  rw [output_ofHandler]
  exact liftM_eq_pure_of_liftM_eq_some (m := Id) p choose hchoose hx

end FreeM

end PFunctor
