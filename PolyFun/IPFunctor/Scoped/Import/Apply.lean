/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import PolyFun.IPFunctor.Scoped.Import.Env
public meta import Lean.Meta.Transform
public meta import Lean.Meta.WHNF
import PolyFun.IPFunctor.Scoped.StackedInterpretation

/-!
# Printing application equations

Let `N` be an imported declaration with an equation `N.meaning_eq : N.meaning = r`, where `r` is
the meaning written without the declaration's syntax. `applyEquation` writes the application
equation of `N`:

```
∀ ns xs, apply (N.meaning ns) xs = r'
```

Here `ns` are the type parameters of `N`'s scheme, named as the outer abstractions of `r` name
them, and `xs` has one variable per argument of its function type. The right side `r'` is `r` at
the same variables:

1. the outer type abstractions of `r` are applied to `ns`. Each outer abstraction of a value,
   such as `ContinuousHom.ofFun g h`, is applied to its variable by beta reduction of `g`; the
   application former applies `r` to any variable that remains;
2. every `Term.denote alg t ρ` of the type level is evaluated, and every lookup of an explicit
   environment is replaced by its entry (`EnvReader.lookup?`);
3. the frontend's inliner rewrites what remains, such as an instantiation of a primitive.

`logApplyEquation` prints the equation as a theorem to paste into a proof, with the proof
`kernel_rfl`. The kernel checks the statement once it is pasted; the printer is not trusted.

A frontend supplies an `ApplyPrinter`: the evaluator of its type level, the binder telescope of an
evaluated scheme, the application former, how to find the function of an abstraction value, and
the inliner. The evaluator returns `none` for a term it does not cover; an exception it throws
counts as `none` too.

The right side of a wrapper is the meaning of a dependency, instantiated or applied. Compared
directly with `N.meaning`, it makes the kernel unfold the dependency's meaning on both sides, the
left one reached through the unfolding of `N.meaning`. The printer therefore proves a wrapper's
equation with a rewrite by `N.meaning_eq` before `kernel_rfl`, which leaves the dependency as a
constant on both sides, when the frontend detects wrappers (`ApplyPrinter.isWrapper`).
-/

public meta section

namespace IPFunctor.Import

open Lean Meta

/-- The function `g` of a continuous map `ContinuousHom.ofFun g h`. -/
def ApplyPrinter.ofFunFunction? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``OmegaCompletePartialOrder.ContinuousHom.ofFun 6 then some (e.getArg! 4)
  else none

/-- What a frontend supplies to print application equations. -/
structure ApplyPrinter where
  /-- The command, for messages. -/
  command : String
  /-- The suffix of a declaration's equation. -/
  equation : Name := `meaning_eq
  /-- The suffix of the printed theorem. -/
  theoremSuffix : Name := `meaning_apply
  /-- Evaluate a type-level term at the values of its variables, nearest first; `none` outside the
  evaluator, and when it throws. -/
  evalTerm : Expr → Array Expr → MetaM (Option Expr)
  /-- Run the continuation with fresh variables for an evaluated scheme: its type parameters,
  named by the given names as far as they go, and one variable per argument of its function
  type. -/
  telescope : {α : Type} → Expr → List Name → (Array Expr → Array Expr → MetaM α) → MetaM α
  /-- Apply a meaning to arguments. -/
  apply : Expr → List Expr → MetaM Expr
  /-- The function of an abstraction value. -/
  function? : Expr → Option Expr := ApplyPrinter.ofFunFunction?
  /-- Rewrite the evaluated right side, such as by applying instantiations of primitives. -/
  inline : Expr → MetaM Expr := pure
  /-- Whether the evaluated right side is a wrapper: the meaning of a dependency, instantiated or
  applied. -/
  isWrapper : Expr → Bool := fun _ => false

namespace ApplyPrinter

variable (p : ApplyPrinter)

/-- `Term.denote alg t ρ` at an explicit environment `ρ`, evaluated, or `none` when the
evaluator does not cover it or throws. -/
def evalDenote (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``ScopedSignature.Term.denote 8 do return none
  let some values := EnvReader.values? (e.getArg! 7) | return none
  try p.evalTerm (e.getArg! 6) values catch _ => return none

/-- Evaluate every `Term.denote` of the type level that the evaluator covers, and replace every
lookup of an explicit environment by its entry. -/
def evalSyntax (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.isAppOfArity ``ScopedSignature.Term.denote 8 then
      if let some y ← p.evalDenote x then return .done y
    if let some y := EnvReader.lookup? x then return .visit y
    return .continue)

/-- Apply the outer abstractions of `f` to `xs` by beta reduction, and the application former to
the variables that remain. -/
def applyArgs (f : Expr) : List Expr → MetaM Expr
  | [] => pure f
  | x :: rest => do
    if let some g := p.function? f then return ← applyArgs (g.beta #[x]) rest
    p.apply f (x :: rest)

/-- The application equation of the declaration `decl`, and whether its right side is a
wrapper. -/
def applyEquation (decl : Name) : MetaM (Expr × Bool) := do
  let eqName := decl ++ p.equation
  let some info := (← getEnv).find? eqName
    | throwError "{p.command}: {decl} has no equation `{eqName}`"
  let some (_, lhs, rhs) := info.type.eq?
    | throwError "{p.command}: `{eqName}` is not an equation"
  let type ← inferType lhs
  let type := (← unfoldDefinition? type).getD type
  let some denote := type.find? (·.isAppOfArity ``ScopedSignature.Term.denote 8)
    | throwError "{p.command}: the type of {lhs} names no scheme{indentExpr type}"
  let some scheme ← p.evalDenote denote
    | throwError "{p.command}: cannot evaluate the scheme{indentExpr denote}"
  let names ← lambdaTelescope rhs fun xs _ => xs.toList.mapM (·.fvarId!.getUserName)
  p.telescope scheme names fun ns xs => do
    let l ← p.apply (mkAppN lhs ns) xs.toList
    let r ← p.applyArgs (rhs.beta ns) xs.toList
    let r ← p.inline (← p.evalSyntax r)
    return (← mkForallFVars (ns ++ xs) (← mkEq l r), p.isWrapper r)

/-- Print the application equation of `decl` as a theorem named relative to the current
namespace, so that it can be pasted there, with the proof `kernel_rfl`, after a rewrite by the
declaration's equation when the right side is a wrapper. Names are printed in full. -/
def logApplyEquation (decl : Name) : MetaM Unit := do
  let (stmt, wrapper) ← p.applyEquation decl
  let fmt ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.proofs true) do
    ppExpr stmt
  let proof := if wrapper then s!"by\n  rw [{decl ++ p.equation}]\n  kernel_rfl"
    else "by\n  kernel_rfl"
  let name := (decl ++ p.theoremSuffix).replacePrefix (← getCurrNamespace) .anonymous
  logInfo m!"theorem {name} :\n    {fmt.pretty 100 4} := {proof}"

end ApplyPrinter

end IPFunctor.Import
