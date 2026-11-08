/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Value
public import ToCslib.Data.Fin.Lattice
public import Mathlib.Tactic.NormNum

/-!
# The `cost_bound` tactic

`cost_bound [defs]` proves charge bounds and worst-case costs of concrete free programs by
computation. It unfolds the given definitions and runs `simp` with the `do`-fragment equations of
`IsChargeBound` (`PolyFun.PFunctor.Free.Cost`) and of `costWith` and `cost`
(`PolyFun.PFunctor.Free.Cost.Value`), so that each call
contributes its charge and each continuation is checked or maximised branch by branch. Suprema over
finite answer types (`Fin n`, `Bool`, `Option`, sums) are unfolded into binary suprema. The
remaining arithmetic goes to `norm_num` and then `omega`.

Goals it targets:

* `x.IsChargeBound c B` in any ordered additive monoid. Each call becomes an inequality
  `s + c a ≤ B` on the amount spent, so natural-number and vector budgets reduce to linear
  arithmetic.
* `cost c x ≤ B` or `cost c x = v` in a complete lattice such as `ℕ∞`.

The tactic leaves the goals it cannot close, in simplified form, for further work.
-/

public section

namespace PFunctor.FreeM

open Lean.Parser.Tactic in
/-- `cost_bound [defs]` unfolds `defs` and evaluates charge bounds or worst-case costs of a
concrete free program: `simp` with the cost equations and finite-supremum unfolding, followed by
`norm_num` and `omega` on the remaining arithmetic. Goals that remain are left in simplified
form. -/
syntax (name := costBound) "cost_bound" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| cost_bound $[[$args,*]]?) => do
    let args := (args.map (·.getElems)).getD #[]
    `(tactic| (simp [isChargeBound_freeM_pure_iff, Fin.iSup_succ, iSup_of_empty, iSup_bool_eq,
        iSup_option, iSup_sum, $args,*]
        <;> (try norm_num [Fin.iSup_succ]) <;> (try omega)))

end PFunctor.FreeM
