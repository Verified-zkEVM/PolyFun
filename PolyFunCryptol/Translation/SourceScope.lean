/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle
public import PolyFunCryptol.Model.Reference.Kinds
public import PolyFunCryptol.Model.Reference.Dependencies

/-!
# Scope and kind validation of imported declaration graphs

Top-level groups are checked in dependency order. A nonrecursive declaration
cannot refer to itself or to a later group; recursive declarations see their
entire group. Parallel comprehension branches are checked independently before
their bound names are combined for the body. This gate establishes scope and
kind validity, separately from expression typing and semantic correspondence.
-/

public section

namespace Cryptol.Translation

open Reference

private def addNames (bound names : List Reference.Name) : Except String (List Reference.Name) := do
  let result := names ++ bound
  unless (result.map Reference.Name.id).Nodup do throw "duplicate value-binding identity"
  return result

private def checkSelector : Selector → Except String Unit
  | .tuple i (some n) | .list i (some n) =>
      if i < n then .ok () else .error "selector is outside its annotated shape"
  | .record field (some names) => do
      unless names.Nodup && names.contains field do throw "invalid record selector annotation"
  | _ => .ok ()

mutual

  private def checkExpression (nominals : List (Reference.Name × List Kind × Kind)) :
      Nat → List Reference.Name → List Parameter →
      Reference.Expr → Except String Unit
    | 0, _, _, _ => .error "scope-checking budget exhausted"
    | fuel + 1, bound, params, e => do
        let child := checkExpression nominals fuel bound params
        let type := TypeExpr.checkKindWith nominals fuel params
        match e with
        | .list t es => type .value t; es.forM child
        | .tuple es => es.forM child
        | .record fs =>
            unless (fs.map Prod.fst).Nodup do throw "duplicate record field"
            fs.forM (child ∘ Prod.snd)
        | .select e s => checkSelector s; child e
        | .update t e s v => type .value t; checkSelector s; child e; child v
        | .ite c a b => child c; child a; child b
        | .caseE value alternatives fallback =>
            child value
            unless (alternatives.map Prod.fst).Nodup do throw "duplicate case alternative"
            for .mk bindings body in alternatives.map Prod.snd ++ fallback.toList do
              for (_, t) in bindings do type .value t
              checkExpression nominals fuel (← addNames bound (bindings.map Prod.fst)) params body
        | .comprehension n t body branches =>
            type .number n
            type .value t
            if branches.isEmpty then throw "comprehension must have a branch"
            let introduced ← branches.mapM (checkMatches nominals fuel bound params)
            let scope ← addNames bound introduced.flatten
            checkExpression nominals fuel scope params body
        | .var name =>
            match bound.find? (fun n => n.id == name.id) with
            | none => throw s!"unbound value {name.origin} ({name.id})"
            | some known =>
                unless known = name do throw s!"inconsistent spelling for value identity {name.id}"
        | .typeAbs p body =>
            unless p.kind != .proposition do throw "invalid abstraction kind"
            if params.any (fun q => q.id == p.id) then throw "duplicate parameter binder"
            checkExpression nominals fuel bound (p :: params) body
        | .typeApp e t => child e; let _ ← t.kindWith? nominals fuel params
        | .app f x => child f; child x
        | .abs name t body =>
            type .value t
            checkExpression nominals fuel (← addNames bound [name]) params body
        | .proofAbs c body => type .proposition c; child body
        | .proofApp e => child e
        | .whereE body groups =>
            let scope ← checkGroups nominals fuel bound params groups
            checkExpression nominals fuel scope params body
        | .guards t branches =>
            type .value t
            for (constraints, body) in branches do
              constraints.forM (type .proposition)
              child body

  private def checkDeclaration (nominals : List (Reference.Name × List Kind × Kind)) :
      Nat → List Reference.Name → List Parameter →
      Reference.Decl → Except String Unit
    | 0, _, _, _ => .error "declaration-checking budget exhausted"
    | fuel + 1, bound, params, .mk name schema definition =>
        (do
          schema.checkKindsWith nominals fuel params
          match definition with
          | .primitive => pure ()
          | .expression body => checkExpression nominals fuel bound params body
          | .foreign _ (some body) => checkExpression nominals fuel bound params body
          | .foreign _ none => pure ()
        ).mapError (fun message => s!"{name.origin}: {message}")

  private def checkGroups (nominals : List (Reference.Name × List Kind × Kind)) :
      Nat → List Reference.Name → List Parameter →
      List Reference.DeclGroup → Except String (List Reference.Name)
    | 0, _, _, _ => .error "group-checking budget exhausted"
    | _ + 1, bound, _, [] => .ok bound
    | fuel + 1, bound, params, .nonrecursive d :: rest => do
        checkDeclaration nominals fuel bound params d
        checkGroups nominals fuel (← addNames bound [d.name]) params rest
    | fuel + 1, bound, params, .recursive ds :: rest => do
        if ds.isEmpty then throw "empty recursive group"
        let scope ← addNames bound (ds.map Reference.Decl.name)
        ds.forM (checkDeclaration nominals fuel scope params)
        checkGroups nominals fuel scope params rest

  private def checkMatches (nominals : List (Reference.Name × List Kind × Kind)) :
      Nat → List Reference.Name → List Parameter →
      List Reference.Match → Except String (List Reference.Name)
    | 0, _, _, _ => .error "comprehension-checking budget exhausted"
    | _ + 1, _, _, [] => .ok []
    | fuel + 1, bound, params, .from name n t source :: rest => do
        n.checkKindWith nominals fuel params .number
        t.checkKindWith nominals fuel params .value
        checkExpression nominals fuel bound params source
        return name :: (← checkMatches nominals fuel (← addNames bound [name]) params rest)
    | fuel + 1, bound, params, .letE d :: rest => do
        checkDeclaration nominals fuel bound params d
        return d.name :: (← checkMatches nominals fuel (← addNames bound [d.name]) params rest)

end

private def checkFallbacks (declarations : List Reference.Decl)
    (fallbacks : List (Reference.Name × Reference.Name)) : Except String Unit := do
  let globals := declarations.map Reference.Decl.name
  unless (fallbacks.map (fun p => p.1.id)).Nodup do
    throw "duplicate primitive fallback"
  for (source, target) in fallbacks do
    unless globals.contains source && globals.contains target do
      throw "primitive fallback has an unresolved endpoint"
    unless source.origin == s!"Cryptol::{source.text}" &&
        target.origin == s!"Cryptol::Reference::{source.text}" do
      throw "primitive fallback is not an official reference definition"
    unless ["pmult", "pdiv", "pmod", "foldl", "foldl'", "foldWhile", "scanl", "iterate"].contains
        source.text do throw "unknown reference primitive fallback"
    match declarations.find? (fun d => d.name == source),
        declarations.find? (fun d => d.name == target) with
    | some (.mk _ _ .primitive), some (.mk _ _ (.expression _)) => pure ()
    | _, _ => throw "primitive fallback endpoints have the wrong declaration forms"

/-- Nominal constructor names are ordinary value bindings, separate from type names. -/
def ModuleDefinition.constructors (module : ModuleDefinition) : List Reference.Name :=
  module.nominals.flatMap fun n => match n.definition with
    | .abstract => []
    | .struct name _ => [name]
    | .enumeration cs => cs.map EnumConstructor.name

/-- Check the complete parameter telescope and synonyms of an interface. -/
def InterfaceDefinition.checkScopes (interface : InterfaceDefinition) (fuel : Nat := 10000) :
    Except ImportError Unit :=
  let checked : Except String Unit := do
    let params := interface.typeParameters.map Prod.snd
    unless (params.map Parameter.id).Nodup do throw "duplicate interface type parameter"
    unless ((interface.typeParameters.map Prod.fst ++
        interface.valueParameters.map Prod.fst ++ interface.synonyms.map TypeSynonym.name).map
        Reference.Name.id).Nodup do throw "duplicate interface binding identity"
    let type := TypeExpr.checkKindWith [] fuel
    for c in interface.constraints do type params .proposition c
    for (_, scheme) in interface.valueParameters do scheme.checkKindsWith [] fuel params
    unless interface.typeExports.all (interface.synonyms.map TypeSynonym.name).contains do
      throw "unresolved interface type synonym"
    for synonym in interface.synonyms do
      let localParams := synonym.parameters ++ params
      unless (localParams.map Parameter.id).Nodup do throw "duplicate synonym parameter"
      for c in synonym.constraints do type localParams .proposition c
      let _ ← synonym.body.kindWith? [] fuel localParams
  checked.mapError (⟨["interface", interface.provenance.name, "scope"], ·⟩)

/-- Bundle-local value identities are unique across declarations and constructors.
Source spellings and source spans are diagnostic information, not linking keys. -/
def ModuleBundle.checkIdentities (bundle : ModuleBundle) : Except String Unit := do
  let modules := bundle.modules.map (fun m => m.provenance.name) ++
    bundle.interfaces.map (fun i => i.provenance.name)
  unless modules.Nodup do throw "duplicate module or interface identity"
  let globals := bundle.modules.flatMap fun m =>
    (m.groups.flatMap DeclGroup.declarations).map Decl.name ++ m.constructors
  unless (globals.map Reference.Name.id).Nodup do throw "duplicate global value identity"
  let types := bundle.modules.flatMap fun m =>
    m.nominals.map NominalType.name ++ m.synonyms.map TypeSynonym.name
  unless (types.map Reference.Name.id).Nodup do throw "duplicate global type identity"

/-- Check a whole module under its explicit numeric, type, and value parameters.
This validates scope and kinds, not expression types or source correspondence. -/
def ModuleBundle.checkModuleScopes (bundle : ModuleBundle) (module : ModuleDefinition)
    (fuel : Nat := 10000) : Except ImportError Unit :=
  let checked : Except String Unit := do
    bundle.checkIdentities
    for interface in bundle.interfaces do
      (interface.checkScopes fuel).mapError ImportError.message
    checkFallbacks (bundle.modules.flatMap (fun m => m.groups.flatMap DeclGroup.declarations))
      bundle.primitiveFallbacks
    let nominals := bundle.modules.flatMap fun m => m.nominals.map fun n =>
      (n.name, n.parameters.map Parameter.kind, n.kind)
    unless (nominals.map (fun n => n.1.id)).Nodup do throw "duplicate nominal identity"
    let declarations := module.groups.flatMap DeclGroup.declarations
    unless module.nestedFunctors.isEmpty && module.nestedSignatures.isEmpty do
      throw "nested functor or signature body is not retained by this bundle format"
    let names := declarations.map Decl.name
    unless names = module.declarations.map DeclarationInfo.name do
      throw "declaration metadata does not match retained groups"
    for (declaration, info) in declarations.zip module.declarations do
      let computed ← declaration.dependencies fuel
      unless computed = info.dependencies do
        throw s!"{declaration.name.origin}: dependency metadata differs from the retained body"
    unless (names.map Reference.Name.id).Nodup do throw "duplicate declaration identity"
    unless module.exports.all names.contains do throw "unresolved public value"
    unless module.typeExports.all (module.synonyms.map TypeSynonym.name).contains do
      throw "unresolved public type synonym"
    unless module.nominalExports.all (module.nominals.map NominalType.name).contains do
      throw "unresolved public nominal type"
    let params := module.typeParameters.map Prod.snd
    unless (params.map Parameter.id).Nodup do throw "duplicate module type parameter"
    let type := TypeExpr.checkKindWith nominals fuel
    for c in module.constraints do type params .proposition c
    for (_, scheme) in module.valueParameters do scheme.checkKindsWith nominals fuel params
    for synonym in module.synonyms do
      let localParams := synonym.parameters ++ params
      unless (localParams.map Parameter.id).Nodup do throw "duplicate synonym parameter"
      for c in synonym.constraints do type localParams .proposition c
      let _ ← synonym.body.kindWith? nominals fuel localParams
    for nominal in module.nominals do
      let localParams := nominal.parameters ++ params
      unless (localParams.map Parameter.id).Nodup do throw "duplicate nominal parameter"
      for c in nominal.constraints do type localParams .proposition c
      for (_, cs) in nominal.derived do
        for c in cs do type localParams .proposition c
      match nominal.definition with
      | .abstract => pure ()
      | .struct _ fields =>
          unless (fields.map Prod.fst).Nodup do throw "duplicate struct field"
          for (_, t) in fields do type localParams .value t
      | .enumeration constructors =>
          unless constructors.map EnumConstructor.number = List.range constructors.length do
            throw "enum constructor indices are not consecutive"
          for c in constructors do
            for t in c.fields do type localParams .value t
    let external := bundle.modules.flatMap fun m =>
      (m.groups.flatMap DeclGroup.declarations).map Decl.name
    let ambient := external.filter (fun n => !names.contains n) ++
      bundle.modules.flatMap ModuleDefinition.constructors ++ module.valueParameters.map Prod.fst
    unless (ambient.map Reference.Name.id).Nodup do throw "duplicate ambient value identity"
    let _ ← checkGroups nominals fuel ambient params module.groups
    pure ()
  checked.mapError (⟨["module", module.provenance.name, "scope"], ·⟩)

/-- Every module receives its own result, including modules after an earlier failure. -/
def ModuleBundle.scopeReport (bundle : ModuleBundle) (fuel : Nat := 10000) :
    List (String × Except ImportError Unit) :=
  (bundle.modules.map fun module =>
    (module.provenance.name, bundle.checkModuleScopes module fuel)) ++
  (bundle.interfaces.map fun interface =>
    (interface.provenance.name, do
      bundle.checkIdentities.mapError (⟨["bundle", "identity"], ·⟩)
      interface.checkScopes fuel))

/-- A module whose retained syntax passed the scope/kind gate. The certificate
does not imply expression typing, termination, or source-semantic preservation. -/
structure ModuleBundle.ScopeCertificate (bundle : ModuleBundle) (module : ModuleDefinition) where
  /-- Explicit recursion budget of the checker. -/
  budget : Nat
  /-- Kernel-checked acceptance equation. -/
  valid : bundle.checkModuleScopes module budget = .ok ()

/-- Successful module validation retains its acceptance equation. -/
def ModuleBundle.certifyModuleScopes (bundle : ModuleBundle) (module : ModuleDefinition)
    (fuel : Nat := 10000) : Except ImportError (bundle.ScopeCertificate module) :=
  match h : bundle.checkModuleScopes module fuel with
  | .ok () => .ok ⟨fuel, h⟩
  | .error error => .error error

/-- Resolve a public declaration by source spelling within one module.
Ambiguous spellings fail rather than selecting an arbitrary frontend identity. -/
def ModuleDefinition.findExport? (module : ModuleDefinition) (name : String) :
    Except ImportError Reference.Decl :=
  match (module.groups.flatMap DeclGroup.declarations).filter
      (fun d => module.exports.contains d.name && d.name.text == name) with
  | [declaration] => .ok declaration
  | [] => .error ⟨[module.provenance.name, name], "unknown public declaration"⟩
  | _ => .error ⟨[module.provenance.name, name], "ambiguous public declaration"⟩

/-- Validate binding structure, complete dependencies, and all type-expression kinds. -/
def SourceBundle.checkScopes (bundle : SourceBundle) (fuel : Nat := 10000) :
    Except ImportError Unit :=
  let checked : Except String Unit := do
    let globals ← checkGroups [] fuel [] [] bundle.groups
    checkFallbacks (bundle.groups.flatMap DeclGroup.declarations) bundle.primitiveFallbacks
    for root in bundle.roots do
      (do
        root.schema.checkKinds fuel []
        checkExpression [] fuel globals [] root.expression
      ).mapError (fun message => s!"root {root.text}: {message}")
  checked.mapError (⟨["scope"], ·⟩)

/-- Evidence that a bundle passed the scope/kind gate at an explicit finite budget.
This certificate makes no claim about expression typing or source fidelity. -/
structure SourceBundle.ScopeCertificate (bundle : SourceBundle) where
  /-- Nesting budget used by the terminating checker. -/
  budget : Nat
  /-- Acceptance is retained as an equation checked by Lean's kernel. -/
  valid : bundle.checkScopes budget = .ok ()

/-- Successful validation returns its acceptance witness, without an unchecked cast. -/
def SourceBundle.certifyScopes (bundle : SourceBundle) (fuel : Nat := 10000) :
    Except ImportError bundle.ScopeCertificate :=
  match h : bundle.checkScopes fuel with
  | .ok () => .ok ⟨fuel, h⟩
  | .error error => .error error

end Cryptol.Translation
