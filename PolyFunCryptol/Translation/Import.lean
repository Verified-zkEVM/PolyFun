/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceElaboration
public import PolyFunCryptol.Translation.Materialize
public import Mathlib.Data.Fin.VecNotation
public meta import PolyFunCryptol.Translation.SourceElaboration
public meta import PolyFunCryptol.Translation.Materialize
public meta import Lean

/-!
# Importing exported Cryptol source

`cryptol_import Imported from "path/to/export.json"` reads a source bundle exported by the
pinned frontend, checks every root with `SourceElaboration.check` at elaboration time,
and declares, in the current namespace:
* `Imported.bundle : SourceBundle`, the decoded bundle;
* for each root `r`, `Imported.r : Resolved.Term [] T`, the checked resolved term;
* `Imported.r.root : SourceRoot`, the root as exported;
* `Imported.r.accepted : check Imported.bundle Imported.r.root = .ok ⟨T, Imported.r⟩`.

`as f, g` names the roots in order. Otherwise a root is named after the identifier its source
text names, directly or as the function of an ascription `(f : T)`, when no other root names the
same identifier, and `root<i>` otherwise.

`cryptol_import Imported from "path/to/modules.json" module "M"` reads a whole-module bundle
and elaborates module `M` with `ModuleBundle.elaborate`. It declares:
* `Imported.source : ModuleDefinition`, the module as exported;
* `Imported.bundle : ModuleBundle`, restricted to `M` and the declaration groups its
  definitions reach in other modules, with the fallbacks of the retained primitives;
* `Imported.body<i>`, each checked body in declaration order, and `Imported.requirement<i>`,
  each primitive the module requires;
* `Imported.imported : ElaboratedModule`, assembled from these bodies and reducible, so its
  scope and bindings unify with their values;
* `Imported.accepted : Imported.bundle.elaborate "M" = .ok Imported.imported`.

The JSON file and this command are untrusted. The kernel re-runs the checker on the
declared bundle to prove each acceptance theorem. Module bodies are rendered by
`Materialize` and elaborated as ordinary terms. The path is relative to the importing
package's root; it is found from the source file's directory, so dependents may build the
importing module. Lake does not track the file, so regenerate the export through the
reference pipeline, whose manifest records its digest.
-/

public meta section

namespace Cryptol.Translation.Import

open Lean Elab Command Meta

/-- Closed Cryptol types have no type variables, so their variable type is `Empty`. -/
instance toExprEmpty : ToExpr Empty where
  toExpr e := e.elim
  toTypeExpr := mkConst ``Empty

deriving instance ToExpr for Length
deriving instance ToExpr for Ty
deriving instance ToExpr for EvalError
deriving instance ToExpr for BitOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for IntOp
deriving instance ToExpr for RingOp
deriving instance ToExpr for CompareOp
deriving instance ToExpr for LogicType
deriving instance ToExpr for RingType
deriving instance ToExpr for Primitive
deriving instance ToExpr for Reference.Kind
deriving instance ToExpr for Reference.Name
deriving instance ToExpr for Reference.Parameter
deriving instance ToExpr for Reference.Selector
deriving instance ToExpr for Reference.TypeExpr
deriving instance ToExpr for Reference.Schema
deriving instance ToExpr for Reference.Expr, Reference.CaseAlt, Reference.Match,
  Reference.Definition, Reference.Decl, Reference.DeclGroup
deriving instance ToExpr for SourceRoot
deriving instance ToExpr for SourceModule
deriving instance ToExpr for SourceBundle
deriving instance ToExpr for Reference.EnumConstructor
deriving instance ToExpr for Reference.NominalDefinition
deriving instance ToExpr for Reference.NominalType
deriving instance ToExpr for Reference.TypeSynonym
deriving instance ToExpr for SourceLocation
deriving instance ToExpr for SourceIdentity
deriving instance ToExpr for DeclarationInfo
deriving instance ToExpr for ModuleDefinition
deriving instance ToExpr for InterfaceDefinition
deriving instance ToExpr for ModuleBundle

/-- The closed Cryptol type former. -/
def closedTy : Lean.Expr := toTypeExpr ClosedTy

/-- Quote a typed variable with its context and sort. -/
def quoteVar : {Γ : List ClosedTy} → {a : ClosedTy} → IPFunctor.ScopedVar Γ a → Lean.Expr
  | _ :: Γ, a, .zero =>
      mkAppN (mkConst ``IPFunctor.ScopedVar.zero [Level.zero]) #[closedTy, toExpr Γ, toExpr a]
  | b :: Γ, a, .succ v =>
      mkAppN (mkConst ``IPFunctor.ScopedVar.succ [Level.zero])
        #[closedTy, toExpr Γ, toExpr a, toExpr b, quoteVar v]

/-- The smart constructor of an operator and its arguments other than context and children. -/
def head : {a : ClosedTy} → Resolved.Op a → Name × Array Lean.Expr
  | _, @Resolved.Op.sequence a n => (``Resolved.Term.sequence, #[toExpr a, toExpr n])
  | _, @Resolved.Op.primitive a p => (``Resolved.Term.primitive, #[toExpr a, toExpr p])
  | _, .bit b => (``Resolved.Term.bit, #[toExpr b])
  | _, .integer i => (``Resolved.Term.integer, #[toExpr i])
  | _, .unit => (``Resolved.Term.unit, #[])
  | _, @Resolved.Op.error a e => (``Resolved.Term.error, #[toExpr a, toExpr e])
  | _, @Resolved.Op.lam a b => (``Resolved.Term.lam, #[toExpr a, toExpr b])
  | _, @Resolved.Op.app a b => (``Resolved.Term.app, #[toExpr a, toExpr b])
  | _, @Resolved.Op.letE a b => (``Resolved.Term.letE, #[toExpr a, toExpr b])
  | _, @Resolved.Op.pair a b => (``Resolved.Term.pair, #[toExpr a, toExpr b])
  | _, @Resolved.Op.fst a b => (``Resolved.Term.fst, #[toExpr a, toExpr b])
  | _, @Resolved.Op.snd a b => (``Resolved.Term.snd, #[toExpr a, toExpr b])
  | _, @Resolved.Op.generate a l => (``Resolved.Term.generate, #[toExpr a, toExpr l])
  | _, @Resolved.Op.index a l => (``Resolved.Term.index, #[toExpr a, toExpr l])
  | _, @Resolved.Op.ite a => (``Resolved.Term.ite, #[toExpr a])
  | _, @Resolved.Op.fix a => (``Resolved.Term.fix, #[toExpr a])
  | _, .bitNot => (``Resolved.Term.bitNot, #[])
  | _, .bitOp o => (``Resolved.Term.bitOp, #[toExpr o])
  | _, .intOp o => (``Resolved.Term.intOp, #[toExpr o])
  | _, .intEq => (``Resolved.Term.intEq, #[])
  | _, .intLt => (``Resolved.Term.intLt, #[])

/-- Sequence literals take their children as one vector argument. -/
def isSequence : {a : ClosedTy} → Resolved.Op a → Bool
  | _, .sequence _ => true
  | _, _ => false

mutual

/-- Quote a resolved term as applications of the `Resolved.Term` smart constructors. -/
partial def quoteTerm : {Γ : List ClosedTy} → {a : ClosedTy} → Resolved.Term Γ a → MetaM Lean.Expr
  | Γ, a, .pure v => return mkAppN (mkConst ``Resolved.Term.var) #[toExpr Γ, toExpr a, quoteVar v]
  | _, _, .liftBind op k => quoteNode op k

/-- Quote one constructor application from its children. -/
partial def quoteNode {Γ : List ClosedTy} {a : ClosedTy} (op : Resolved.Op a)
    (k : (p : Resolved.syntaxSignature.Arg op) →
      Resolved.Term (Resolved.syntaxSignature.binders op p ++ Γ)
        (Resolved.syntaxSignature.sort op p)) : MetaM Lean.Expr := do
  let (name, params) := head op
  let children ← (List.finRange op.arity).mapM fun i => quoteTerm (k i)
  let prefix_ := #[toExpr Γ] ++ params
  if isSequence op then
    let element := mkAppN (mkConst ``Resolved.Term) #[toExpr Γ, params[0]!]
    let mut items ← mkAppOptM ``Matrix.vecEmpty #[some element]
    for child in children.reverse do
      items ← mkAppM ``Matrix.vecCons #[child, items]
    return mkAppN (mkConst name) (prefix_.push items)
  else
    return mkAppN (mkConst name) (prefix_ ++ children.toArray)

end

/-- Add and compile a definition whose body is exported, as `@[expose]` does. Compiling it lets
generated definitions that refer to it compile. -/
def addExposedDefinition (name : Name) (type value : Lean.Expr) (doc : String) : CoreM Unit := do
  withExporting do
    addDecl <| .defnDecl {
      name, levelParams := [], type, value, safety := .safe
      hints := .regular (getMaxHeight (← getEnv) value + 1) }
    enableRealizationsForConst name
    compileDecls #[name]
  addDocStringCore name doc

/-- A source spelling usable as a Lean declaration name. -/
def identifier? (text : String) : Option Name :=
  let name := text.toName
  if !name.isAnonymous && name.isAtomic && !text.isEmpty &&
      text.all (fun c => c.isAlphanum || c == '_') then
    some name
  else
    none

/-- The identifier a root names: its source text, or the function of an ascription `(f : T)`. -/
def rootIdentifier? (root : SourceRoot) : Option Name :=
  let ascribed := ((root.text.dropPrefix? "(").map fun rest =>
    (rest.toString.splitOn " : ").headD "").getD ""
  identifier? root.text <|> identifier? ascribed

/-- The declaration name for root `index`: the identifier it names when no other root names
the same one, and `root<index>` otherwise. -/
def rootName (roots : List SourceRoot) (index : Nat) (root : SourceRoot) : Name :=
  match rootIdentifier? root with
  | some name =>
      if (roots.filter (rootIdentifier? · == some name)).length == 1 then name
      else .mkSimple s!"root{index}"
  | none => .mkSimple s!"root{index}"

/-- Resolve a package-relative path from the directory of the importing source file, trying
each enclosing directory in turn. Lake builds dependencies from the workspace root, so the
working directory need not be the importing package's root. -/
def resolvePath (path : String) : CommandElabM System.FilePath := do
  let relative : System.FilePath := path
  if relative.isAbsolute then return relative
  let mut directory ← IO.FS.realPath ((← getFileName : System.FilePath).parent.getD ".")
  repeat
    let candidate := directory / relative
    if ← candidate.pathExists then return candidate
    match directory.parent with
    | some parent => if parent == directory then break else directory := parent
    | none => break
  return relative

/-- Read a JSON export. -/
def readJson (path : String) : CommandElabM Json := do
  match Json.parse (← IO.FS.readFile (← resolvePath path)) with
  | .ok json => pure json
  | .error e => throwError "{path}: invalid JSON: {e}"

/-- Decode, check, and declare an exported source bundle. -/
def importBundle (prefix_ : Name) (path : String) (names : Option (Array Name) := none) :
    CommandElabM Unit := do
  let json ← readJson path
  let bundle ← match SourceBundle.decode json with
    | .ok bundle => pure bundle
    | .error e => throwError "{path}: {String.intercalate " / " e.location}: {e.message}"
  let ns ← getCurrNamespace
  let bundleName := ns ++ prefix_ ++ `bundle
  liftCoreM <| addExposedDefinition bundleName (mkConst ``SourceBundle) (toExpr bundle)
    s!"The source bundle exported to `{path}`."
  if let some names := names then
    unless names.size == bundle.roots.length do
      throwError "{path}: {bundle.roots.length} roots, but {names.size} names"
  for h : index in [0:bundle.roots.length] do
    let root := bundle.roots[index]
    let base := ns ++ prefix_ ++ ((names.bind (·[index]?)).getD (rootName bundle.roots index root))
    let rootDecl := base ++ `root
    liftCoreM <| addExposedDefinition rootDecl (mkConst ``SourceRoot) (toExpr root)
      s!"The exported root `{root.text}`."
    match SourceElaboration.check bundle root with
    | .error e =>
        throwError "{path}, root `{root.text}`: {String.intercalate " / " e.location}: \
          {e.message}"
    | .ok ⟨type, result⟩ =>
        let value ← liftTermElabM <| quoteTerm result
        let termType := mkAppN (mkConst ``Resolved.Term)
          #[toExpr ([] : List ClosedTy), toExpr type]
        liftCoreM <| addExposedDefinition base termType value
          s!"The checked resolved term of root `{root.text}`."
    let accepted := mkIdent (`_root_ ++ base ++ `accepted)
    elabCommand (← `(command|
      set_option maxRecDepth 10000 in
      /-- The kernel re-runs the checker on the declared bundle and root. -/
      theorem $accepted : Cryptol.Translation.SourceElaboration.check
          $(mkIdent bundleName) $(mkIdent rootDecl) = .ok ⟨_, $(mkIdent base)⟩ := by
        with_unfolding_all rfl))

/-! ## Whole modules -/

/-- Restrict a bundle to a module and the declaration groups its definitions reach in other
modules, keeping the fallbacks of retained primitives and every interface. Other modules keep
their types and nominals; modules contributing no group are dropped. -/
def restrict (bundle : ModuleBundle) (rootName : String) : Except String ModuleBundle := do
  let some root := bundle.modules.find? (·.provenance.name == rootName)
    | throw s!"module {rootName} is not in the bundle"
  let needed := ((← bundle.groupClosure root).flatMap Reference.DeclGroup.declarations).map
    Reference.Decl.name
  let keep (m : ModuleDefinition) : Option ModuleDefinition :=
    if m.provenance.name == rootName then some m else
      let groups := m.groups.filter fun g => g.declarations.any (needed.contains ·.name)
      let names := (groups.flatMap Reference.DeclGroup.declarations).map Reference.Decl.name
      if groups.isEmpty then none else
        some { m with
          groups
          declarations := m.declarations.filter (names.contains ·.name)
          exports := m.exports.filter names.contains }
  return { bundle with
    modules := bundle.modules.filterMap keep
    primitiveFallbacks := bundle.primitiveFallbacks.filter (needed.contains ·.1) }

/-- Lean source for a parenthesized `repr`. -/
def reprText {α : Type} [Repr α] (x : α) : String := "(" ++ reprStr x ++ ")"

/-- Lean source for a checked parameter scope. -/
def scopeText (w : Polymorphic.Scope) : String :=
  s!"(Polymorphic.Scope.mk {w.numbers} {w.types} {reprText w.constraints})"

/-- A rendered body: its type and its value. -/
structure BodyText where
  /-- The body's declared type. -/
  type : String
  /-- The body's materialized term. -/
  value : String

/-- Render each body of a declaration sequence, and the sequence itself in terms of
`prefix.body<i>`, numbering bodies from `next`. -/
def renderDeclarations (prefix_ : String) {w : Polymorphic.Scope} :
    {Γ Δ : Signatures w} → Declarations w Γ Δ → Nat →
      Except String (Array BodyText × String)
  | _, _, .nil _, _ => .ok (#[], "(.nil _)")
  | Γ, _, .nonrecursive name s value rest, next => do
      let body := ⟨s!"Polymorphic.Term {scopeText w} {reprText (Γ.map Prod.snd)} {reprText s}",
        ← Materialize.term value⟩
      let (bodies, tail) ← renderDeclarations prefix_ rest (next + 1)
      return (#[body] ++ bodies, s!"(.nonrecursive {reprText name} {reprText s} \
        {prefix_}.body{next} {tail})")
  | Γ, _, .recursive bindings values rest, next => do
      let sorts := bindings.map Prod.snd
      let group ← (List.finRange sorts.length).mapM fun i => do
        return (⟨s!"Polymorphic.Term {scopeText w} {reprText (sorts ++ Γ.map Prod.snd)} \
          {reprText sorts[i]}", ← Materialize.term (values i)⟩ : BodyText)
      let (bodies, tail) ← renderDeclarations prefix_ rest (next + group.length)
      let cases := (List.range group.length).foldr
        (fun i rest => s!"(Fin.cases {prefix_}.body{next + i} {rest})") "(fun i => Fin.elim0 i)"
      return (group.toArray ++ bodies, s!"(.recursive {reprText bindings} {cases} {tail})")

/-- Elaborate one command of generated Lean source. -/
def elabSource (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated source does not parse: {e}\n{source}"

/-- Decode, restrict, elaborate and declare one module of an exported module bundle. -/
def importModule (prefix_ : Name) (path : String) (rootName : String) : CommandElabM Unit := do
  let full ← match SourceBundle.decodeModuleBundle (← readJson path) with
    | .ok bundle => pure bundle
    | .error e => throwError "{path}: {String.intercalate " / " e.location}: {e.message}"
  let bundle ← match restrict full rootName with
    | .ok bundle => pure bundle
    | .error e => throwError "{path}: {e}"
  match bundle.elaborate rootName with
  | .error e => throwError "{path}, module `{rootName}`: \
      {String.intercalate " / " e.location}: {e.message}"
  | .ok m => do
      let ns ← getCurrNamespace
      let base := ns ++ prefix_
      let sourceExpr := mkConst (base ++ `source)
      liftCoreM <| addExposedDefinition (base ++ `source) (mkConst ``ModuleDefinition)
        (toExpr m.source) s!"The module `{rootName}` exported to `{path}`."
      let modules := bundle.modules.map fun module =>
        if module.provenance.name == rootName then sourceExpr else toExpr module
      let moduleList ← liftTermElabM <| mkListLit (mkConst ``ModuleDefinition) modules
      liftCoreM <| addExposedDefinition (base ++ `bundle) (mkConst ``ModuleBundle)
        (mkAppN (mkConst ``ModuleBundle.mk) #[toExpr bundle.cryptolRevision, moduleList,
          toExpr bundle.interfaces, toExpr bundle.primitiveFallbacks,
          toExpr bundle.frontendPatches])
        s!"The part of `{path}` that module `{rootName}` needs."
      for h : i in [0:m.requirements.length] do
        liftCoreM <| addExposedDefinition (base ++ .mkSimple s!"requirement{i}")
          (mkConst ``Reference.Decl) (toExpr m.requirements[i].declaration)
          s!"Primitive requirement {i} of module `{rootName}`."
      let name := prefix_.toString
      let (bodies, code) ← match renderDeclarations name m.code 0 with
        | .ok rendered => pure rendered
        | .error e => throwError "module `{rootName}`: {e}"
      let opening := "open Cryptol Cryptol.Polymorphic Cryptol.Translation in"
      for h : i in [0:bodies.size] do
        elabSource <| String.intercalate "\n" [opening,
          s!"/-- Checked body {i} of module `{rootName}`. -/",
          s!"@[expose] def {name}.body{i} : {bodies[i].type} :=",
          s!"  {bodies[i].value}"]
      let requirements := (List.range m.requirements.length).map fun i =>
        s!"⟨{name}.requirement{i}, rfl⟩"
      elabSource <| String.intercalate "\n" [opening,
        s!"/-- The checked module `{rootName}`, with exposed bodies. -/",
        s!"@[expose, reducible] def {name}.imported : ElaboratedModule where",
        s!"  source := {name}.source",
        s!"  scope := {scopeText m.scope}",
        s!"  parameters := {reprText m.parameters}",
        s!"  bindings := {reprText m.bindings}",
        s!"  code := {code}",
        s!"  requirements := [{String.intercalate ", " requirements}]"]
      elabSource <| String.intercalate "\n" [opening, "set_option maxRecDepth 10000 in",
        "/-- The kernel re-runs module elaboration on the declared bundle. -/",
        s!"theorem {name}.accepted :",
        s!"    {name}.bundle.elaborate {reprStr rootName} = .ok {name}.imported := by",
        "  with_unfolding_all rfl"]

/-- `cryptol_import Imported from "export.json"` declares a checked exported Cryptol bundle, and
`as f, g` names its roots in order. With `module "M"`, it declares module `M` of a whole-module
bundle. -/
syntax (name := cryptolImport)
  "cryptol_import " ident " from " str (" module " str)? (" as " ident,+)? : command

/-- Elaborate `cryptol_import` by `importBundle` or `importModule`. -/
@[command_elab cryptolImport] def elabCryptolImport : CommandElab
  | `(cryptol_import $prefix_:ident from $path:str $[module $root:str]? $[as $names:ident,*]?) => do
      let names := names.map fun names => names.getElems.map (·.getId)
      match root with
      | some root =>
          if names.isSome then throwError "a module import names its bodies by position"
          importModule prefix_.getId path.getString root.getString
      | none => importBundle prefix_.getId path.getString names
  | _ => throwUnsupportedSyntax

end Cryptol.Translation.Import
