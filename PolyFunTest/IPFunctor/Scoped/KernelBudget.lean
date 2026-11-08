/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedDomains
public import PolyFun.Logic.KernelRfl

/-!
# The kernel's cost of nested abstractions

The lazy-language tutorial writes an abstraction's value as `Env.abstraction` of its body's
meaning, whose proof of continuity is stated at its own function. The equation below states the
meaning of eight nested abstractions, `λ x₁ … x₈. x₈`, with a right side free of syntax that writes
each continuous map in the same form, as an importer does. The kernel's check runs under
`maxHeartbeats 200`, lowered from the default 200000, and needs between 5 and 10. With the value
written as a composite through `Env.bindOne`, the check needs between 4000 and 5000 and takes
1.3 s instead of 3 ms; the cost grows about 2.6 times with each level of nesting. The kernel
respects `maxHeartbeats`, so a change that makes the cost exponential again fails this module.
-/

@[expose] public section

namespace PolyFunTest.ScopedKernelBudget

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature Examples.ScopedDomains

/-- `nat → … → nat` with `n` arguments. -/
def arrows : ℕ → Ty
  | 0 => .nat
  | n + 1 => .arrow .nat (arrows n)

/-- The value of an abstraction with function `F`, as an importer writes it: its proof of
continuity is ascribed at `F`. -/
noncomputable abbrev lamValue {a b : Ty} (F : a.Comp → b.Comp) (h : ωScottContinuous F) :
    (Ty.arrow a b).Comp :=
  DomainResult.value (ContinuousHom.ofFun F (id (α := ωScottContinuous F) h))

/-- `λ x₁ … x₈. x₈`. -/
def nest : Expr [] (arrows 8) :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam (.var .zero))))))))

/-- The value of `nest` written without syntax. -/
noncomputable def nestValue : (arrows 8).Comp :=
  lamValue (fun _ => lamValue (fun _ => lamValue (fun _ => lamValue (fun _ =>
    lamValue (fun _ => lamValue (fun _ => lamValue (fun _ => lamValue (fun x => x)
      ωScottContinuous.id) .const) .const) .const) .const) .const) .const) .const

set_option maxHeartbeats 200 in
-- Lowered from the default 200000: the kernel's check needs between 5 and 10.
/-- The meaning of eight nested abstractions, checked by the kernel within a lowered budget. -/
theorem meaning_nest : meaning nest = nestValue := by
  kernel_rfl

end PolyFunTest.ScopedKernelBudget
