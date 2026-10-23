/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceScope
public import PolyFunCryptol.Model.Reference.Types
public import PolyFunCryptol.Model.ResolvedSequences

/-!
# Checked elaboration of typed Cryptol expressions

The elaborator checks instantiated schemes, proof applications, lexical binding,
application types and lambda annotations before constructing intrinsically typed
resolved syntax. It supports nonrecursive global definitions with closed numeric
and type arguments, monomorphic local declarations, sequence literals and closed
property guards. Local bindings retain lexical scope and suspended evaluation.
Unsupported constructs and unsatisfied constraints are errors.
The acceptance certificate retains the exact input and output of this typed gate;
it does not assert correctness of the external frontend or a full Cryptol semantics.
-/

public section

namespace Cryptol.Translation.SourceElaboration

open Reference

/-- A resolved expression together with its checked result type. -/
abbrev TypedTerm (Γ : List ClosedTy) := (a : ClosedTy) × Resolved.Term Γ a

/-- Lift a first-order validation result into the universe of scoped syntax. -/
@[expose] def liftCheck {ε α : Type} : Except ε α → Except ε (ULift.{1} α)
  | .ok value => .ok ⟨value⟩
  | .error error => .error error

/-- Source aggregate labels are retained by checking and erased only for the carrier. -/
abbrev coreType := ValueType.coreType

/-- The canonical lazy product spine of a source tuple. -/
abbrev tupleType := ValueType.tupleType

/-- The canonical lazy product spine of a source record. -/
abbrev recordType := ValueType.recordType

/-- Elaboration retains source types: records and tuples with equal carriers remain distinct. -/
abbrev SourceTerm (Γ : List ClosedTy) := (a : ValueType) × Resolved.Term Γ (coreType a)

/-- Lexical source identities paired with source types and typed de Bruijn positions. -/
abbrev Names (Γ : List ClosedTy) := List ((a : ValueType) × (Name × Var Γ (coreType a)))

/-- Enter a value binder without merging distinct source identities. -/
@[expose] def Names.extend {Γ : List ClosedTy} (names : Names Γ) (name : Name) (a : ValueType) :
    Names (coreType a :: Γ) :=
  ⟨a, name, .zero⟩ :: names.map (fun ⟨b, n, v⟩ => ⟨b, n, .succ v⟩)

/-- Resolve a source annotation under the current checked type arguments. -/
@[expose] def annotation (fuel : Nat) (params : TypeEnvironment) (t : TypeExpr) :
    Except String ValueType := t.evaluate fuel params >>= TypeValue.value?

/-- Source equality supplies the transport proof, preserving labels and tuple arities. -/
@[expose] def expect {Γ : List ClosedTy} (a : ValueType) (t : SourceTerm Γ) :
    Except String (Resolved.Term Γ (coreType a)) :=
  if h : t.1 == a then .ok (congrArg coreType (eq_of_beq h) ▸ t.2)
  else .error "source type mismatch"

/-- Assemble suspended tuple components without demanding any component. -/
@[expose] def tuple {Γ : List ClosedTy} : (xs : List (SourceTerm Γ)) →
    Resolved.Term Γ (tupleType (xs.map Sigma.fst))
  | [] => .unit
  | ⟨_, x⟩ :: xs => .pair x (tuple xs)

/-- Assemble suspended record components in canonical field order. -/
@[expose] def record {Γ : List ClosedTy} : (xs : List (String × SourceTerm Γ)) →
    Resolved.Term Γ (recordType (xs.map fun (label, t) => (label, t.1)))
  | [] => .unit
  | (_, ⟨_, x⟩) :: xs => .pair x (record xs)

/-- Project a tuple field while preserving its checked source type. -/
@[expose] def selectTuple {Γ : List ClosedTy} : (fields : List ValueType) →
    Resolved.Term Γ (tupleType fields) → Nat → Except String (SourceTerm Γ)
  | [], _, _ => .error "tuple selector out of bounds"
  | a :: _, term, 0 => .ok ⟨a, .fst term⟩
  | _ :: fields, term, i + 1 => selectTuple fields (.snd term) i

/-- Record lookup uses field names, not merely the erased carrier shape. -/
@[expose] def selectRecord {Γ : List ClosedTy} : (fields : List (String × ValueType)) →
    Resolved.Term Γ (recordType fields) → String → Except String (SourceTerm Γ)
  | [], _, _ => .error "unknown record field"
  | (label, a) :: fields, term, wanted =>
      if label == wanted then .ok ⟨a, .fst term⟩ else selectRecord fields (.snd term) wanted

/-- Checked selection validates the optional frontend shape before constructing a projection. -/
@[expose] def select {Γ : List ClosedTy} (t : SourceTerm Γ) (s : Selector) :
    Except String (SourceTerm Γ) := do
  let _ ← liftCheck (t.1.select s)
  match t, s with
  | ⟨.tuple fields, term⟩, .tuple i _ => selectTuple fields term i
  | ⟨.record fields, term⟩, .record label _ => selectRecord fields term label
  | ⟨.seq _ a, term⟩, .list i _ => return ⟨a, .index term (.integer i)⟩
  | _, _ => throw "selector requires a compatible aggregate"

/-- Collect ordered type arguments followed by proof applications of a named declaration. -/
@[expose] def instantiation : Reference.Expr → Option (Name × List TypeExpr × Nat)
  | .var name => some (name, [], 0)
  | .typeApp f t => do
      let (name, args, proofs) ← instantiation f
      if proofs != 0 then none else some (name, args ++ [t], 0)
  | .proofApp f => do
      let (name, args, proofs) ← instantiation f
      some (name, args, proofs + 1)
  | _ => none

/-- Remove exactly the instantiated parameter and proof binders of a global body. -/
@[expose] def instantiateBody (fuel : Nat) (params : TypeEnvironment) :
    List Parameter → List TypeExpr → Reference.Expr → Except String Reference.Expr
  | p :: ps, constraints, .typeAbs q body =>
      if p = q then instantiateBody fuel params ps constraints body
      else .error "definition parameter differs from its scheme"
  | [], _ :: cs, .proofAbs constraint body => do
      unless (← constraint.evaluate fuel params >>= TypeValue.proposition?) do
        throw "unsatisfied definition constraint"
      instantiateBody fuel params [] cs body
  | [], [], body => .ok body
  | _, _, _ => .error "definition binders differ from its scheme"

/-- Recognize only explicitly supported, fully instantiated official primitive identities. -/
@[expose] def primitive {Γ : List ClosedTy} (name : Name) (args : List TypeValue) :
    Except String (SourceTerm Γ) := do
  unless name.origin == s!"Cryptol::{name.text}" ||
      name.origin == s!"(Cryptol::{name.text})" do throw "unrecognized primitive identity"
  match name.text, args with
  | "True", [] => return ⟨.bit, .bit true⟩
  | "False", [] => return ⟨.bit, .bit false⟩
  | "number", [.number (.finite n), .value .integer] =>
      return ⟨.integer, .integer n⟩
  | "number", [.number (.finite n), .value .bit] =>
      if n < 2 then return ⟨.bit, .bit (n == 1)⟩ else throw "invalid bit literal"
  | "number", [.number (.finite n), .value (.seq (.finite w) .bit)] =>
      return ⟨.seq (.finite w) .bit, .word (BitVec.ofNat w n)⟩
  | "^", [.value (.seq (.finite n) .bit)] =>
      return ⟨.function (.seq (.finite n) .bit)
        (.function (.seq (.finite n) .bit) (.seq (.finite n) .bit)),
        .primitive (.wordLogic n .xor)⟩
  | ">>", [.number (.finite n), .value .integer, .value .bit] =>
      return ⟨.function (.seq (.finite n) .bit)
        (.function .integer (.seq (.finite n) .bit)), .primitive (.shift n .right)⟩
  | ">>>", [.number (.finite n), .value .integer, .value .bit] =>
      return ⟨.function (.seq (.finite n) .bit)
        (.function .integer (.seq (.finite n) .bit)), .primitive (.shift n .rotateRight)⟩
  | "+", [.value .integer] =>
      return ⟨.function .integer (.function .integer .integer),
        .lam (.lam (.intOp .add (.var (.succ .zero)) (.var .zero)))⟩
  | "-", [.value .integer] =>
      return ⟨.function .integer (.function .integer .integer),
        .lam (.lam (.intOp .sub (.var (.succ .zero)) (.var .zero)))⟩
  | "*", [.value .integer] =>
      return ⟨.function .integer (.function .integer .integer),
        .lam (.lam (.intOp .mul (.var (.succ .zero)) (.var .zero)))⟩
  | "@", [.number n, .value a, .value .integer] =>
      return ⟨.function (.seq n a) (.function .integer a),
        .lam (.lam (.index (.var (.succ .zero)) (.var .zero)))⟩
  | "foldl", [.number (.finite n), .value a, .value b] =>
      return ⟨.function (.function a (.function b a))
        (.function a (.function (.seq (.finite n) b) a)),
        .primitive (.foldl n (coreType a) (coreType b))⟩
  | _, _ => throw "unsupported primitive or primitive instantiation"

/-- Select the first satisfied closed guard, retaining a kernel-reducible checking equation. -/
@[expose] def selectGuard (fuel : Nat) (params : TypeEnvironment) :
    List (List TypeExpr × Reference.Expr) → Except String Reference.Expr
  | [] => .error "no satisfied property guard"
  | (constraints, body) :: rest => do
      let holds ← constraints.mapM fun c => c.evaluate fuel params >>= TypeValue.proposition?
      if holds.all id then return body else selectGuard fuel params rest

/-- Specialize and elaborate the supported expression fragment at a finite checking budget. -/
@[expose] def elaborate : Nat → List Decl → TypeEnvironment →
    {Γ : List ClosedTy} → Names Γ → Reference.Expr → Except String (SourceTerm Γ)
  | 0, _, _, _, _, _ => .error "expression elaboration budget exhausted"
  | fuel + 1, globals, params, Γ, names, expression => do
      match expression with
      | .abs name type body =>
          let ⟨a⟩ ← liftCheck (annotation fuel params type)
          let ⟨b, term⟩ ← elaborate fuel globals params (names.extend name a) body
          return ⟨.function a b, .lam term⟩
      | .app function argument =>
          let f ← elaborate fuel globals params names function
          let x ← elaborate fuel globals params names argument
          match f with
          | ⟨.function a b, f⟩ => return ⟨b, .app f (← expect a x)⟩
          | _ => throw "application requires a function"
      | .ite condition yes no =>
          let c ← elaborate fuel globals params names condition >>= expect .bit
          let ⟨a, y⟩ ← elaborate fuel globals params names yes
          let n ← elaborate fuel globals params names no >>= expect a
          return ⟨a, .ite c y n⟩
      | .list type elements =>
          let ⟨a⟩ ← liftCheck (annotation fuel params type)
          let terms ← elements.mapM fun e =>
            elaborate fuel globals params names e >>= expect a
          return ⟨.seq (.finite terms.length) a, .sequence terms.length terms.get⟩
      | .tuple elements =>
          let terms ← elements.mapM (elaborate fuel globals params names)
          return ⟨.tuple (terms.map Sigma.fst), tuple terms⟩
      | .record fields =>
          unless (fields.map Prod.fst).Nodup do throw "duplicate record field"
          let terms ← fields.mapM fun (label, e) => do
            return (label, ← elaborate fuel globals params names e)
          return ⟨.record (terms.map fun (label, t) => (label, t.1)), record terms⟩
      | .select value selector =>
          select (← elaborate fuel globals params names value) selector
      | .comprehension length element body [[.from name sourceLength sourceType source]] =>
          let ⟨n⟩ ← liftCheck (length.evaluate fuel params >>= TypeValue.number?)
          let ⟨m⟩ ← liftCheck (sourceLength.evaluate fuel params >>= TypeValue.number?)
          unless n == m do throw "single-generator length mismatch"
          let ⟨a⟩ ← liftCheck (annotation fuel params sourceType)
          let ⟨b⟩ ← liftCheck (annotation fuel params element)
          let xs ← elaborate fuel globals params names source >>= expect (.seq n a)
          let body ← elaborate fuel globals params (names.extend name a) body >>= expect b
          return ⟨.seq n b, .map (.lam body) xs⟩
      | .whereE body [] => elaborate fuel globals params names body
      | .whereE body (.nonrecursive declaration :: rest) =>
          let schema := declaration.schema
          let ⟨(instantiated, type)⟩ ← liftCheck (schema.instantiate fuel params [])
          let a := type
          let .expression value := declaration.definition
            | throw "local declarations must have an expression body"
          let ⟨value⟩ ← liftCheck (instantiateBody fuel instantiated [] schema.constraints value)
          let value ← elaborate fuel globals instantiated names value >>= expect a
          let ⟨b, body⟩ ← elaborate fuel globals params
            (names.extend declaration.name a) (.whereE body rest)
          return ⟨b, .letE value body⟩
      | .whereE _ (.recursive _ :: _) =>
          throw "recursive local groups require a fixed-point certificate"
      | .guards type branches =>
          let ⟨a⟩ ← liftCheck (annotation fuel params type)
          let ⟨body⟩ ← liftCheck (selectGuard fuel params branches)
          let term ← elaborate fuel globals params names body >>= expect a
          return ⟨a, term⟩
      | _ =>
          let some (name, arguments, proofs) := instantiation expression
            | throw "unsupported expression constructor"
          match names.find? (fun entry => entry.2.1.id == name.id) with
          | some ⟨a, known, v⟩ =>
              unless known = name && arguments.isEmpty && proofs == 0 do
                throw "invalid lexical variable instantiation"
              return ⟨a, .var v⟩
          | none =>
              let some declaration := globals.find? (fun d => d.name.id == name.id)
                | throw "unresolved or recursive global declaration"
              unless declaration.name = name do throw "inconsistent global identity"
              let ⟨args⟩ ← liftCheck (arguments.mapM (fun t => t.evaluate fuel params))
              let schema := declaration.schema
              unless proofs == schema.constraints.length do throw "wrong proof-argument count"
              let ⟨(instantiated, type)⟩ ← liftCheck (schema.instantiate fuel [] args)
              let resultType := type
              let result ← match declaration.definition with
                | .primitive => primitive name args
                | .expression body => do
                    let ⟨body⟩ ← liftCheck (instantiateBody fuel instantiated schema.parameters
                      schema.constraints body)
                    elaborate fuel globals instantiated ([] : Names Γ) body
                | .foreign _ _ => throw "foreign definitions need a separate correspondence"
              return ⟨resultType, ← expect resultType result⟩

/-- Complete source validation precedes expression elaboration.
Recursive groups stay unsupported. -/
@[expose] def check (bundle : SourceBundle) (root : SourceRoot) (fuel : Nat := 1000) :
    Except ImportError (TypedTerm []) := do
  let _ ← liftCheck ({ bundle with roots := [root] }.checkScopes fuel)
  let globals := bundle.groups.filterMap fun
    | .nonrecursive declaration => some declaration
    | .recursive _ => none
  let ⟨(_, expected)⟩ ← liftCheck
    ((root.schema.instantiate fuel [] []).mapError (⟨["root schema"], ·⟩))
  let result ← (elaborate fuel globals [] [] root.expression).mapError (⟨["expression"], ·⟩)
  let term ← (expect expected result).mapError (⟨["root type"], ·⟩)
  return ⟨coreType expected, term⟩

/-- Acceptance of the expression-typing gate for a particular intrinsically typed output. -/
structure Certificate (bundle : SourceBundle) (root : SourceRoot) where
  /-- Explicit checking budget; exhaustion rejects rather than supplying a default. -/
  budget : Nat
  /-- Checked result type and resolved term. -/
  result : TypedTerm []
  /-- Kernel-checkable connection to the exact input bundle and expression. -/
  accepted : check bundle root budget = .ok result

/-- A successful elaboration retains its acceptance equation. -/
@[expose] def certify (bundle : SourceBundle) (root : SourceRoot) (fuel : Nat := 1000) :
    Except ImportError (Certificate bundle root) :=
  match h : check bundle root fuel with
  | .ok result => .ok ⟨fuel, result, h⟩
  | .error error => .error error

end Cryptol.Translation.SourceElaboration
