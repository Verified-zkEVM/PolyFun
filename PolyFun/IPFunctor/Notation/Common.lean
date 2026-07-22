/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Lean.Elab.Do
public meta import Lean.Elab.Do.Basic
public meta import Lean.Elab.Term.TermElabM
meta import Lean.Parser.Do

/-!
# Shared indexed `do`-notation elaboration

This module owns the syntax-independent part of the custom `doLetArrow`
elaborators used by `IPFunctor.FreeM` and `IPFunctor.FreeM₂`. Each notation
module still supplies its own monad detector and bind builder.
-/

@[expose] public section

namespace IPFunctor.DoNotation

open Lean Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Lean.Parser.Term

/-- Elaborate the identifier and anonymous forms of `let ←` after checking
that the current monad belongs to the notation implementation calling this
helper. Pattern bindings and mutable bindings continue to fall through to
Lean's builtin elaborator. -/
meta def elabLetArrow
    (accepts : Expr → MetaM Bool) : DoElab := fun stx dec => do
  unless ← accepts (← read).monadInfo.m do throwUnsupportedSyntax
  let `(doLetArrow| let $[mut%$mutTk?]? $decl) := stx | throwUnsupportedSyntax
  if mutTk?.isSome then throwUnsupportedSyntax
  match decl with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    let xType ← Term.elabType (xType?.getD (Lean.mkHole x))
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      Term.addLocalVarInfo x (← getFVarFromUserName x.getId)
      dec.continueWithUnit
  | `(doPatDecl| _%$pat ← $rhs) =>
    let x := mkIdentFrom pat (← mkFreshUserName `__x)
    let xType ← Term.elabType (Lean.mkHole x)
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      dec.continueWithUnit
  | _ => throwUnsupportedSyntax

end IPFunctor.DoNotation
