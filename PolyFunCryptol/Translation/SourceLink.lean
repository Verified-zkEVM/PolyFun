/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceScope

/-!+# Linking retained source groups

Closure is computed from bodies. Selecting any member of a recursive group
retains that entire group. Official reference fallbacks add explicit dependency
edges. The resulting schedule preserves groups and rejects cycles between them.
Only primitive declarations and foreign declarations without a body may become
external requirements; ordinary definitions always retain their bodies.

This is a structural linking check. It does not prove type preservation or
give an implementation to a primitive requirement.
-/

public section

namespace Cryptol.Translation

open Reference

/-- An external dependency retains its complete source scheme and original identity. -/
structure PrimitiveRequirement where
  /-- The original primitive or bodyless foreign declaration. -/
  declaration : Decl
  /-- Ordinary definitions cannot be replaced by semantic parameters. -/
  external : declaration.requiresImplementation = true

/-- The complete dependency closure, with bodies and external requirements distinguished. -/
structure LinkedSource where
  /-- The exact module selected from the retained bundle. -/
  source : ModuleDefinition
  /-- Original declaration groups, ordered so dependencies precede their users. -/
  groups : List DeclGroup
  /-- Explicit primitive implementations still required by the closure. -/
  requirements : List PrimitiveRequirement
  /-- Module value parameters and nominal constructors used as ambient identities. -/
  ambient : List Reference.Name

namespace ModuleBundle

/-- Whole-group closure of all definitions owned by a requested module. -/
@[expose] def groupClosure (bundle : ModuleBundle) (root : ModuleDefinition)
    (fuel : Nat := 10000) : Except String (List DeclGroup) := do
  let all := bundle.modules.flatMap ModuleDefinition.groups
  let edges ← all.mapM fun group => do
    let ds := group.declarations
    return (ds.map Decl.name, (← ds.mapM (fun d => d.dependencies fuel)).flatten)
  let mut needed := (root.groups.flatMap DeclGroup.declarations).map Decl.name
  for _ in List.range (all.length + 1) do
    let previous := needed
    for (names, dependencies) in edges do
      if names.any previous.contains then
        for name in names ++ dependencies do
          if !needed.contains name then needed := needed ++ [name]
    for (original, fallback) in bundle.primitiveFallbacks do
      if needed.contains original && !needed.contains fallback then needed := needed ++ [fallback]
    if needed == previous then break
  return all.filter fun group => group.declarations.any (fun d => needed.contains d.name)

/-- Substitute an official fallback reference while retaining the primitive's declared scheme. -/
@[expose] def resolveFallback (bundle : ModuleBundle) (d : Decl) : Decl :=
  match bundle.primitiveFallbacks.find? (fun entry => entry.1 == d.name) with
  | some (_, target) => .mk d.name d.schema (.expression (.var target))
  | none => d

/-- Separate genuine external primitives from retained source bodies. -/
@[expose] def partitionGroups (bundle : ModuleBundle) (groups : List DeclGroup) :
    Except String (List DeclGroup × List PrimitiveRequirement) := do
  let mut retained := []
  let mut requirements := []
  for group in groups do
    let mut bodies := []
    for original in group.declarations do
      let d := resolveFallback bundle original
      if h : d.requiresImplementation = true then
        requirements := requirements ++ [⟨d, h⟩]
      else
        bodies := bodies ++ [d]
    match group with
    | .nonrecursive _ =>
        match bodies with
        | [d] => retained := retained ++ [.nonrecursive d]
        | [] => pure ()
        | _ => throw "nonrecursive group contains multiple declarations"
    | .recursive _ =>
        if !bodies.isEmpty then retained := retained ++ [.recursive bodies]
  return (retained, requirements)

/-- Order groups by their checked dependencies without merging recursive groups. -/
@[expose] def schedule (fuel : Nat) (ambient : List Reference.Name) (groups : List DeclGroup) :
    Except String (List DeclGroup) := do
  let mut pending ← groups.mapM fun group => do
    let (free, _) ← DeclGroup.freeValuesMany fuel [group]
    return (group, free)
  let mut known := ambient
  let mut result := []
  for _ in List.range groups.length do
    if pending.isEmpty then break
    let some entry := pending.find? (fun (_, free) => free.all known.contains)
      | throw "unresolved dependency or cycle between source declaration groups"
    let names := entry.1.declarations.map Decl.name
    pending := pending.filter fun (g, _) => !(g.declarations.map Decl.name == names)
    result := result ++ [entry.1]
    known := known ++ names
  unless pending.isEmpty do throw "source group scheduling budget exhausted"
  return result

/-- Validate all retained modules, compute closure and schedule the original groups. -/
@[expose] def link (bundle : ModuleBundle) (rootName : String) (fuel : Nat := 10000) :
    Except ImportError LinkedSource := do
  for (_, result) in bundle.scopeReport fuel do result
  let checked : Except String LinkedSource := do
    let some root := bundle.modules.find? (fun m => m.provenance.name == rootName)
      | throw "link root is not a retained module"
    let (groups, requirements) ← partitionGroups bundle (← bundle.groupClosure root fuel)
    let ambient := bundle.modules.flatMap fun m =>
      m.valueParameters.map Prod.fst ++ m.constructors
    let bound := ambient ++ requirements.map (fun r => r.declaration.name)
    return ⟨root, ← schedule fuel bound groups, requirements, ambient⟩
  checked.mapError (⟨[rootName, "link"], ·⟩)

/-- Acceptance evidence for an exact retained bundle and requested source module. -/
structure LinkCertificate (bundle : ModuleBundle) (rootName : String) where
  /-- Explicit checker budget. -/
  budget : Nat
  /-- Linked groups and their declared implementation requirements. -/
  result : LinkedSource
  /-- Kernel-checkable acceptance, separate from source-semantic preservation. -/
  accepted : bundle.link rootName budget = .ok result

/-- Retain the checked link result together with its acceptance equation. -/
@[expose] def certifyLink (bundle : ModuleBundle) (rootName : String) (fuel : Nat := 10000) :
    Except ImportError (bundle.LinkCertificate rootName) :=
  match h : bundle.link rootName fuel with
  | .ok result => .ok ⟨fuel, result, h⟩
  | .error error => .error error

end ModuleBundle
end Cryptol.Translation
