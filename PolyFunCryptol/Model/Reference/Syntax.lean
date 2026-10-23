/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Numeric

/-!
# The typechecked Cryptol reference syntax

This finite presentation retains the constructor distinctions of Cryptol
3.6.0's `TypeCheck.AST`. Names use frontend identities, not display spellings.
Types and expressions here are input syntax; acceptance requires a separate
scope, kind, and typing check. Proof application has no proof payload upstream.
-/

public section

namespace Cryptol.Reference

/-- Kinds accepted by the reference fragment. -/
inductive Kind where
  | number | value | proposition
  | arrow (argument result : Kind)
  deriving DecidableEq, Repr

/-- A declaration identity and its diagnostic source spelling. -/
structure Name where
  /-- Unique identity within one exported bundle. -/
  id : Nat
  /-- Unqualified source spelling, never used for resolving variables. -/
  text : String
  /-- Qualified source spelling for diagnostics and provenance. -/
  origin : String
  deriving DecidableEq, Repr

/-- A parameter binder retains its identity and kind. -/
structure Parameter where
  /-- Unique numeric/type parameter identity. -/
  id : Nat
  /-- The kind checked when applying this binder. -/
  kind : Kind
  deriving DecidableEq, Repr

/-- Upstream selectors retain their optional shape annotations. -/
inductive Selector where
  | tuple (index : Nat) (size : Option Nat)
  | record (field : String) (fields : Option (List String))
  | list (index : Nat) (size : Option Nat)
  deriving DecidableEq, Repr

/-- Source type expressions retain synonyms and named record fields.
Constructor spellings are the pinned frontend's `TC`, `TF`, and `PC` names. -/
inductive TypeExpr where
  | var (parameter : Parameter)
  | number (value : Nat)
  | constructor (name : String) (arguments : List TypeExpr)
  | tuple (size : Nat) (fields : List TypeExpr)
  | record (fields : List (String × TypeExpr))
  | synonym (name : Name) (arguments : List TypeExpr) (body : TypeExpr)
  | nominal (name : Name) (arguments : List TypeExpr)
  | has (selector : Selector) (arguments : List TypeExpr)
  deriving Repr, Inhabited

/-- An ordered prenex scheme, including every class and numeric obligation. -/
structure Schema where
  /-- Numeric and type parameters in source order. -/
  parameters : List Parameter
  /-- The proof assumptions following the parameter binders. -/
  constraints : List TypeExpr
  /-- The monomorphic result type under these binders. -/
  body : TypeExpr
  deriving Repr

/-- A nominal constructor carries suspended fields, in source order. -/
structure EnumConstructor where
  /-- Bundle-local constructor identity. -/
  name : Name
  /-- Constructor index assigned by the frontend. -/
  number : Nat
  /-- Whether the constructor is exported. -/
  isPublic : Bool
  /-- Field types under the enclosing nominal parameters. -/
  fields : List TypeExpr
  deriving Repr

/-- Nominal definitions retain abstract types, structs, and enumerations. -/
inductive NominalDefinition where
  | abstract
  | struct (constructor : Name) (fields : List (String × TypeExpr))
  | enumeration (constructors : List EnumConstructor)
  deriving Repr

/-- A named nominal type and its complete parameterized definition. -/
structure NominalType where
  /-- Identity used by nominal type applications. -/
  name : Name
  /-- Ordered numeric and type parameters. -/
  parameters : List Parameter
  /-- Result kind after the parameters are applied. -/
  kind : Kind
  /-- Formation constraints under the parameters. -/
  constraints : List TypeExpr
  /-- Constructor definitions, with no eager evaluation of fields. -/
  definition : NominalDefinition
  /-- Derived classes and their conditions, as supplied by the frontend. -/
  derived : List (String × List TypeExpr)
  deriving Repr

/-- A named type synonym retains its formation constraints and defining body. -/
structure TypeSynonym where
  /-- Synonym identity. -/
  name : Name
  /-- Ordered parameters of the synonym. -/
  parameters : List Parameter
  /-- Formation constraints under the parameters. -/
  constraints : List TypeExpr
  /-- Defining type expression. -/
  body : TypeExpr
  deriving Repr

mutual

  /-- Finite reference expressions with explicit binders and declaration groups. -/
  inductive Expr where
    | list (element : TypeExpr) (elements : List Expr)
    | tuple (elements : List Expr)
    | record (fields : List (String × Expr))
    | select (value : Expr) (selector : Selector)
    | update (type : TypeExpr) (value : Expr) (selector : Selector) (replacement : Expr)
    | ite (condition yes no : Expr)
    | caseE (value : Expr) (alternatives : List (String × CaseAlt)) (fallback : Option CaseAlt)
    | comprehension (length element : TypeExpr) (body : Expr) (branches : List (List Match))
    | var (name : Name)
    | typeAbs (parameter : Parameter) (body : Expr)
    | typeApp (function : Expr) (argument : TypeExpr)
    | app (function argument : Expr)
    | abs (name : Name) (argument : TypeExpr) (body : Expr)
    | proofAbs (constraint : TypeExpr) (body : Expr)
    | proofApp (function : Expr)
    | whereE (body : Expr) (groups : List DeclGroup)
    | guards (type : TypeExpr) (branches : List (List TypeExpr × Expr))
    deriving Repr

  /-- Constructor fields remain separate binders, with their source types. -/
  inductive CaseAlt where
    | mk (bindings : List (Name × TypeExpr)) (body : Expr)
    deriving Repr

  /-- One sequential comprehension binding. Parallel branches have separate scopes. -/
  inductive Match where
    | from (name : Name) (length element : TypeExpr) (source : Expr)
    | letE (declaration : Decl)
    deriving Repr

  /-- Declaration definitions distinguish primitives and pure foreign fallbacks. -/
  inductive Definition where
    | primitive
    | expression (body : Expr)
    | foreign (interface : String) (body : Option Expr)
    deriving Repr

  /-- A named declaration with its full source scheme. -/
  inductive Decl where
    | mk (name : Name) (schema : Schema) (definition : Definition)
    deriving Repr

  /-- Recursive declarations form a single simultaneous group. -/
  inductive DeclGroup where
    | nonrecursive (declaration : Decl)
    | recursive (declarations : List Decl)
    deriving Repr

end

/-- The identity declared by a source declaration. -/
@[expose] def Decl.name : Decl → Name
  | .mk name _ _ => name

/-- The complete scheme of a source declaration. -/
@[expose] def Decl.schema : Decl → Schema
  | .mk _ schema _ => schema

/-- The implementation of a source declaration. -/
@[expose] def Decl.definition : Decl → Definition
  | .mk _ _ definition => definition

/-- Exactly the source forms that require an external implementation. -/
@[expose] def Decl.requiresImplementation (d : Decl) : Bool :=
  match d.definition with
  | .primitive | .foreign _ none => true
  | .expression _ | .foreign _ (some _) => false

/-- The declarations introduced by a group, in their exported order. -/
@[expose] def DeclGroup.declarations : DeclGroup → List Decl
  | .nonrecursive declaration => [declaration]
  | .recursive declarations => declarations

end Cryptol.Reference
