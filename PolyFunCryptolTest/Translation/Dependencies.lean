/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceLink

/-! # Dependency boundaries used by whole-module linking -/

public section

namespace Cryptol.Tests.Dependencies

open Reference Translation

private def x : Reference.Name := ⟨1, "x", "x"⟩
private def y : Reference.Name := ⟨2, "y", "y"⟩
private def bits : TypeExpr := .constructor "TC TCBit" []
private def schema : Reference.Schema := ⟨[], [], bits⟩

-- A nonrecursive declaration does not bind its name in its own right-hand side.
example : DeclGroup.freeValuesMany 10 [.nonrecursive (.mk x schema (.expression (.var x)))] =
    .ok ([x], [x]) := rfl

-- Both names are local to a simultaneous recursive group.
example : DeclGroup.freeValuesMany 10 [.recursive
    [.mk x schema (.expression (.var y)), .mk y schema (.expression (.var x))]] =
    .ok ([], [x, y]) := rfl

-- A later sequential generator can use an earlier generator's bound value.
example : Match.freeValuesMany 10
    [.from x (.number 1) bits (.tuple []), .from y (.number 1) bits (.var x)] =
    .ok ([], [x, y]) := rfl

-- Parallel branches do not bring their bindings into one another's scope.
example : Expr.freeValues 10 (.comprehension (.number 1) bits (.var y)
    [[.from x (.number 1) bits (.tuple [])], [.from y (.number 1) bits (.var x)]]) =
    .ok [x] := rfl

-- Fields bound by a case arm are local, but the scrutinee remains a dependency.
example : Expr.freeValues 10 (.caseE (.var x) [("Some", .mk [(y, bits)] (.var y))] none) =
    .ok [x] := rfl

-- Dependency exhaustion cannot certify a body as dependency-free.
example : Expr.freeValues 0 (.var x) = .error "dependency traversal budget exhausted" := rfl

/-- A primitive requirement cannot hide an ordinary expression body. -/
theorem ordinary_body_not_requirement (r : PrimitiveRequirement) (e : Reference.Expr)
    (h : r.declaration.definition = .expression e) : False := by
  have := r.external
  simp [Decl.requiresImplementation, h] at this

-- Pure foreign bodies participate in dependency checking and are not parameters.
example : Decl.freeValues 10 (.mk x schema (.foreign "abi" (some (.var y)))) = .ok [y] := rfl

example : (.mk x schema (.foreign "abi" (some (.var y))) : Decl).requiresImplementation = false :=
  rfl

-- Cycles between separately nonrecursive groups must not be silently made recursive.
example : ModuleBundle.schedule 10 []
    [.nonrecursive (.mk x schema (.expression (.var y))),
     .nonrecursive (.mk y schema (.expression (.var x)))] =
    .error "unresolved dependency or cycle between source declaration groups" := rfl

end Cryptol.Tests.Dependencies
