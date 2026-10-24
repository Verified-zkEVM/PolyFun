/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Reference.Syntax
public import Mathlib.Data.List.Sort

/-!
# Value dependencies of retained Cryptol syntax

Dependencies are computed from bodies, independently of the frontend's metadata.
Lexical groups and sequential comprehension bindings remove only the names they
bind. Parallel branches do not bind names in one another. Exhausting the explicit
traversal budget is a failure, never an empty dependency set.
-/

public section

namespace Cryptol.Reference

/-- Remove the identities introduced by a lexical binding. -/
@[expose] def withoutNames (free bound : List Name) : List Name :=
  free.filter fun name => !bound.any (fun b => b.id == name.id)

mutual

  /-- Free value occurrences, retaining source identities and diagnostic spellings. -/
  @[expose] def Expr.freeValues : Nat → Expr → Except String (List Name)
    | 0, _ => .error "dependency traversal budget exhausted"
    | fuel + 1, expression => do
        let children (es : List Expr) := es.mapM (Expr.freeValues fuel)
        match expression with
        | .var name => return [name]
        | .list _ es | .tuple es => return (← children es).flatten
        | .record fields => return (← children (fields.map Prod.snd)).flatten
        | .select e _ | .typeAbs _ e | .typeApp e _ | .proofAbs _ e | .proofApp e =>
            e.freeValues fuel
        | .update _ e _ replacement | .app e replacement =>
            return (← e.freeValues fuel) ++ (← replacement.freeValues fuel)
        | .ite c a b => return (← children [c, a, b]).flatten
        | .abs name _ body => return withoutNames (← body.freeValues fuel) [name]
        | .caseE value alternatives fallback =>
            let arms ← (alternatives.map Prod.snd ++ fallback.toList).mapM fun
              | .mk bindings body => do
                  return withoutNames (← body.freeValues fuel) (bindings.map Prod.fst)
            return (← value.freeValues fuel) ++ arms.flatten
        | .comprehension _ _ body branches =>
            let parts ← branches.mapM (Match.freeValuesMany fuel)
            return parts.flatMap Prod.fst ++
              withoutNames (← body.freeValues fuel) (parts.flatMap Prod.snd)
        | .whereE body groups =>
            let (free, bound) ← DeclGroup.freeValuesMany fuel groups
            return free ++ withoutNames (← body.freeValues fuel) bound
        | .guards _ branches => return (← children (branches.map Prod.snd)).flatten

  /-- A declaration's body dependencies; its own name is not implicitly bound. -/
  @[expose] def Decl.freeValues : Nat → Decl → Except String (List Name)
    | 0, _ => .error "declaration dependency budget exhausted"
    | fuel + 1, .mk _ _ definition => match definition with
        | .primitive | .foreign _ none => .ok []
        | .expression body | .foreign _ (some body) => body.freeValues fuel

  /-- Dependencies and definitions of ordered lexical groups. -/
  @[expose] def DeclGroup.freeValuesMany : Nat → List DeclGroup →
      Except String (List Name × List Name)
    | 0, _ => .error "group dependency budget exhausted"
    | _ + 1, [] => .ok ([], [])
    | fuel + 1, group :: rest => do
        let ds := group.declarations
        let names := ds.map Decl.name
        let uses := (← ds.mapM (Decl.freeValues fuel)).flatten
        let free := match group with
          | .nonrecursive _ => uses
          | .recursive _ => withoutNames uses names
        let (later, bound) ← DeclGroup.freeValuesMany fuel rest
        return (free ++ withoutNames later names, names ++ bound)

  /-- Dependencies and definitions of one sequential comprehension branch. -/
  @[expose] def Match.freeValuesMany : Nat → List Match →
      Except String (List Name × List Name)
    | 0, _ => .error "comprehension dependency budget exhausted"
    | _ + 1, [] => .ok ([], [])
    | fuel + 1, binding :: rest => do
        let entry : Except String (List Name × Name) := match binding with
          | .from name _ _ source => do return (← source.freeValues fuel, name)
          | .letE d => do return (← d.freeValues fuel, d.name)
        let (free, name) ← entry
        let (later, bound) ← Match.freeValuesMany fuel rest
        return (free ++ withoutNames later [name], name :: bound)

end

/-- Canonical set of direct dependencies, sorted by bundle-local identity. -/
@[expose] def Decl.dependencies (declaration : Decl) (fuel : Nat := 10000) :
    Except String (List Name) := do
  return ((← declaration.freeValues fuel).eraseDups).insertionSort (fun a b => a.id ≤ b.id)

end Cryptol.Reference
