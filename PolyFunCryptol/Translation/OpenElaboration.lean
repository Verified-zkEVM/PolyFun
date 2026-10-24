/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.OpenTypes
public import PolyFunCryptol.Translation.ConstraintEvidence
public import PolyFunCryptol.Model.PolyConstructors

/-!
# Elaboration into finite ordered polymorphic syntax

Global references are typed variables in a shared context. Abstractions retain
one finite body; recursive groups are elaborated under all their declared
schemes before any type instantiation. Unknown syntax is an explicit failure.
-/

public section

namespace Cryptol.Translation.OpenElaboration

open Polymorphic

/-- A checked expression and its ordered result scheme. -/
abbrev TypedTerm (w : Scope) (Γ : List w.ValueSort) := (s : w.ValueSort) × Term w Γ s

/-- Source names attached to typed binding positions. -/
abbrev Names (w : Scope) (Γ : List w.ValueSort) :=
  List ((s : w.ValueSort) × (Reference.Name × Var Γ s))

/-- Enter a value binder, preserving the positions of older bindings. -/
@[expose] def Names.extend {w : Scope} {Γ : List w.ValueSort} (names : Names w Γ)
    (name : Reference.Name) (s : w.ValueSort) : Names w (s :: Γ) :=
  ⟨s, name, .zero⟩ :: names.map (fun ⟨t, name, x⟩ => ⟨t, name, .succ x⟩)

/-- Reindex name bindings when entering numeric or value-type quantifiers. -/
@[expose] def Names.reindex {w z : Scope} {Γ : List w.ValueSort} (names : Names w Γ)
    (f : w.ValueSort → z.ValueSort) : Names z (Γ.map f) :=
  names.map fun ⟨s, name, x⟩ => ⟨f s, name, x.map f⟩

/-- Extend an environment with a block in its original declaration order. -/
@[expose] def Names.extendMany {w : Scope} {Γ : List w.ValueSort} (names : Names w Γ) :
    (ds : List (Reference.Name × w.ValueSort)) → Names w (ds.map Prod.snd ++ Γ)
  | [] => names
  | (name, s) :: ds => (names.extendMany ds).extend name s

/-- Construct typed names for a complete declaration context. -/
@[expose] def Names.ofSignatures {w : Scope} (ds : List (Reference.Name × w.ValueSort)) :
    Names w (ds.map Prod.snd) :=
  List.append_nil (ds.map Prod.snd) ▸ Names.extendMany (w := w) (Γ := []) [] ds

/-- A source identity must match its complete recorded spelling. -/
@[expose] def lookup {w : Scope} {Γ : List w.ValueSort} (names : Names w Γ)
    (name : Reference.Name) : Except String (TypedTerm w Γ) := do
  match names.find? (fun entry => entry.2.1.id == name.id) with
  | none => throw s!"unbound typed value {name.origin}"
  | some ⟨s, known, x⟩ =>
      unless known == name do throw "inconsistent typed value identity"
      return ⟨s, .var x⟩

/-- Check the expected ordered scheme before transporting a typed term. -/
@[expose] def expect {w : Scope} {Γ : List w.ValueSort} (s : w.ValueSort)
    (term : TypedTerm w Γ) : Except String (Term w Γ s) :=
  if h : term.1 = s then .ok (h ▸ term.2) else .error "open expression scheme mismatch"

/-- Lift a small syntax-checking result to the universe containing polynomial terms. -/
@[expose] def liftCheck {α : Type} : Except String α → Except String (ULift.{1} α)
  | .ok a => .ok ⟨a⟩
  | .error e => .error e

/-- Declared local schemes are checked before any recursive body. -/
@[expose] def signatures {w : Scope} (params : OpenTypes.Parameters w.numbers w.types)
    (fuel : Nat) (ds : List Reference.Decl) : Except String (List (Reference.Name × w.ValueSort)) :=
  ds.mapM fun d =>
    (do return (d.name, ← OpenTypes.scheme params fuel d.schema)).mapError
      (fun message => s!"{d.name.origin}: {message}")

/-- Retain the expression of an ordinary definition or an explicit foreign fallback. -/
@[expose] def definitionBody (d : Reference.Decl) : Except String Reference.Expr :=
  match d.definition with
  | .expression body | .foreign _ (some body) => .ok body
  | .primitive => .error s!"primitive {d.name.origin} requires an interpretation"
  | .foreign _ none => .error s!"foreign declaration {d.name.origin} has no reference body"

mutual

  /-- Elaborate source binders, references, applications and simultaneous recursive groups. -/
  @[expose] def elaborate : Nat → {w : Scope} → {Γ : List w.ValueSort} →
      OpenTypes.Parameters w.numbers w.types → Names w Γ → Reference.Expr →
      Except String (TypedTerm w Γ)
    | 0, _, _, _, _, _ => .error "open elaboration budget exhausted"
    | fuel + 1, w, _, params, names, expression => do
        match expression with
        | .var name => lookup names name
        | .typeAbs p body =>
            match p.kind with
            | .number =>
                let ⟨s, term⟩ ← elaborate fuel (w := w.bindNum) (params.bindNum p.id)
                  (names.reindex (Scheme.subst (ParameterSubstitution.weakenNum _ _))) body
                return ⟨.allNum s, .numAbs term⟩
            | .value =>
                let ⟨s, term⟩ ← elaborate fuel (w := w.bindType) (params.bindType p.id)
                  (names.reindex (Scheme.subst (ParameterSubstitution.weakenType _ _))) body
                return ⟨.allType s, .typeAbs term⟩
            | _ => throw "unsupported abstraction kind"
        | .typeApp function argument =>
            match ← elaborate fuel params names function with
            | ⟨.allNum _, f⟩ =>
                let ⟨a⟩ ← liftCheck
                  (OpenTypes.numeric params fuel argument >>= OpenTypes.totalNumeric)
                return ⟨_, .numApp f a⟩
            | ⟨.allType _, f⟩ =>
                let ⟨a⟩ ← liftCheck (OpenTypes.value params fuel argument)
                return ⟨_, .typeApp f a⟩
            | _ => throw "type application requires an ordered quantifier"
        | .proofAbs assumption body =>
            let ⟨c⟩ ← liftCheck (OpenTypes.constraint params fuel assumption)
            let ⟨s, term⟩ ← elaborate fuel (w := w.assume c) params names body
            return ⟨.guard c s, .proofAbs c term⟩
        | .proofApp function =>
            match ← elaborate fuel params names function with
            | ⟨.guard c s, f⟩ =>
                match ConstraintEvidence.prove w c with
                | some h => return ⟨s, .proofApp f h.down⟩
                | none => throw s!"unresolved constraint entailment: {reprStr c}"
            | _ => throw "proof application requires an assumption binder"
        | .abs name type body =>
            let ⟨a⟩ ← liftCheck (OpenTypes.value params fuel type)
            match ← elaborate fuel params (names.extend name (.mono a)) body with
            | ⟨.mono b, term⟩ => return ⟨.mono (.arrow a b), .lam term⟩
            | _ => throw "value abstraction requires a monomorphic result"
        | .app function argument =>
            let f ← elaborate fuel params names function
            let x ← elaborate fuel params names argument
            match f with
            | ⟨.mono (.arrow a b), f⟩ => return ⟨.mono b, .app f (← expect (.mono a) x)⟩
            | _ => throw "value application requires a function"
        | .ite condition yes no =>
            let c ← elaborate fuel params names condition >>= expect (.mono .bit)
            let ⟨s, y⟩ ← elaborate fuel params names yes
            let n ← elaborate fuel params names no >>= expect s
            return ⟨s, .ite c y n⟩
        | .whereE body [] => elaborate fuel params names body
        | .whereE body (.nonrecursive d :: rest) =>
            let ⟨s⟩ ← liftCheck (OpenTypes.scheme params fuel d.schema)
            let ⟨rhs⟩ ← liftCheck (definitionBody d)
            let value ← elaborate fuel params names rhs >>= expect s
            let ⟨t, term⟩ ← elaborate fuel params (names.extend d.name s) (.whereE body rest)
            return ⟨t, .letE value term⟩
        | .whereE body (.recursive ds :: rest) =>
            let ⟨sigs⟩ ← liftCheck (signatures params fuel ds)
            let names' := names.extendMany sigs
            let rhs ← bodies fuel params names' ds sigs
            let ⟨s, term⟩ ← elaborate fuel params names' (.whereE body rest)
            return ⟨s, .letRec (sigs.map Prod.snd) rhs term⟩
        | _ => throw s!"unsupported open expression constructor {expression.constructorName}"

  /-- Check each body against the signature registered for its source identity. -/
  @[expose] def bodies : Nat → {w : Scope} → {Γ : List w.ValueSort} →
      OpenTypes.Parameters w.numbers w.types → Names w Γ → List Reference.Decl →
      (sigs : List (Reference.Name × w.ValueSort)) →
      Except String ((i : Fin (sigs.map Prod.snd).length) → Term w Γ (sigs.map Prod.snd)[i])
    | 0, _, _, _, _, _, _ => .error "declaration elaboration budget exhausted"
    | _ + 1, _, _, _, _, _, [] => .ok (fun i => Fin.elim0 i)
    | fuel + 1, _, _, params, names, ds, (name, s) :: sigs => do
        let some d := ds.find? (fun d => d.name == name)
          | throw s!"missing source declaration {name.origin}"
        let ⟨body⟩ ← liftCheck (definitionBody d)
        let term ← (elaborate fuel params names body >>= expect s).mapError
          (fun message => s!"{name.origin}: {message}")
        let rest ← bodies fuel params names ds sigs
        return Fin.cases term rest

end

end Cryptol.Translation.OpenElaboration
