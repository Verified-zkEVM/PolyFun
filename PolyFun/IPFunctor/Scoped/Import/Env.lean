/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import PolyFun.IPFunctor.Scoped.Import.Quote
import PolyFun.IPFunctor.Scoped.StackedInterpretation

/-!
# Environments of imported declarations

An imported declaration is a term in the context of its dependencies' sorts, nearest first, the
value context of its `Scope`. A frontend gives the declaration a meaning by interpreting the term
in an environment of its dependencies' meanings, and relates two meanings of it, such as a lazy
meaning and a native value, by the fundamental lemma at a proof of `Env.LiftRel` over the
dependencies' relations.

* `Scope.env` builds the environment of the value context from its values, as a chain of
  `Env.cons` over `Env.empty`, writing each tail of the context from the scope's list suffixes.
* `Scope.liftRel` builds the proof of `Env.LiftRel R` between two such environments from proofs
  of `R` at each position, by `Env.LiftRel.cons` over `Env.liftRel_empty`.

Both write terms with every implicit argument explicit. They infer only the universe level of
each carrier, and never the type of a value or a proof, so the values and proofs may be constants
that the import adds later. The kernel checks the result.

`EnvReader` goes the other way, for a printer that shows a meaning with its environment read off.
`EnvReader.values?` lists the values of an explicit environment, built from `Env.cons` and
`Env.single` over `Env.empty`, and `EnvReader.varIndex?` reads the position of a variable, a chain
of `ScopedVar.succ` over `ScopedVar.zero`. `EnvReader.lookup?` replaces a lookup `ρ a v` of a
chain of `Env.cons`, as `Scope.env` builds it, by the entry. The readers are syntactic: the kernel
checks any statement written with them.
-/

public meta section

namespace IPFunctor.Import

open Lean Meta

/-- The universe level `z` of a carrier `V : S → Type z`. -/
def Scope.carrierLevel (V : Expr) : MetaM Level := do
  forallTelescopeReducing (← inferType V) fun xs _ => getDecLevel (mkAppN V xs)

/-- The environments of the scope's value context and of each of its tails at the carrier `V`,
whose values live in `Type z`: entry `k` is `Env.cons xs[k] (… (Env.cons xs[n-1] Env.empty))`,
and the last entry is `Env.empty`. There must be one value per sort. -/
def Scope.envTails (sc : Scope) (V : Expr) (z : Level) (xs : Array Expr) :
    MetaM (Array Expr) := do
  let n := sc.sorts.size
  unless xs.size == n do
    throwError "environment of {xs.size} values for a context of {n} sorts"
  let mut tails := #[mkApp2 (mkConst ``ScopedSignature.Env.empty [sc.level, z]) sc.sortType V]
  for i in [0:n] do
    let k := n - 1 - i
    tails := tails.push (mkAppN (mkConst ``ScopedSignature.Env.cons [sc.level, z])
      #[sc.sortType, V, sc.suffixes[k + 1]!, sc.sorts[k]!, xs[k]!, tails.back!])
  return tails.reverse

/-- The environment `Env.cons xs[0] (Env.cons xs[1] (… Env.empty))` of the scope's value context
at the carrier `V`, with the values `xs`, nearest first, one per sort. -/
def Scope.env (sc : Scope) (V : Expr) (xs : Array Expr) : MetaM Expr := do
  return (← sc.envTails V (← Scope.carrierLevel V) xs)[0]!

/-- The proof of `Env.LiftRel R (sc.env V xs) (sc.env W ys)` from proofs `hs[k] : R a xs[k] ys[k]`
at the sorts `a` of the scope's value context, nearest first, one per sort. -/
def Scope.liftRel (sc : Scope) (V W R : Expr) (xs ys hs : Array Expr) : MetaM Expr := do
  let n := sc.sorts.size
  unless hs.size == n do
    throwError "relation of {hs.size} proofs for a context of {n} sorts"
  let z ← Scope.carrierLevel V
  let z' ← Scope.carrierLevel W
  let ηs ← sc.envTails V z xs
  let ζs ← sc.envTails W z' ys
  let mut h := mkAppN (mkConst ``ScopedSignature.Env.liftRel_empty [sc.level, z, z'])
    #[sc.sortType, V, W, R]
  for i in [0:n] do
    let k := n - 1 - i
    h := mkAppN (mkConst ``ScopedSignature.Env.LiftRel.cons [sc.level, z, z'])
      #[sc.sortType, V, W, sc.suffixes[k + 1]!, R, ηs[k + 1]!, ζs[k + 1]!, h, sc.sorts[k]!, xs[k]!,
        ys[k]!, hs[k]!]
  return h

namespace EnvReader

/-- The values of an explicit environment, nearest first: a chain of `Env.cons` and `Env.single`
over `Env.empty`. -/
partial def values? (ρ : Expr) : Option (Array Expr) := do
  let ρ := ρ.headBeta
  if ρ.isAppOfArity ``ScopedSignature.Env.cons 6 then
    return #[ρ.getArg! 4] ++ (← values? (ρ.getArg! 5))
  if ρ.isAppOfArity ``ScopedSignature.Env.single 4 then return #[ρ.getArg! 3]
  if ρ.isAppOfArity ``ScopedSignature.Env.empty 2 then return #[]
  none

/-- The position of a variable: a chain of `ScopedVar.succ` over `ScopedVar.zero`. -/
partial def varIndex? (v : Expr) : Option Nat :=
  if v.isAppOfArity ``ScopedVar.zero 3 then some 0
  else if v.isAppOfArity ``ScopedVar.succ 5 then (varIndex? (v.getArg! 4)).map (· + 1)
  else none

/-- Entry `i` of a chain of `Env.cons`. -/
partial def entry? (ρ : Expr) (i : Nat) : Option Expr := do
  let ρ := ρ.headBeta
  guard (ρ.isAppOfArity ``ScopedSignature.Env.cons 6)
  if i = 0 then return ρ.getArg! 4 else entry? (ρ.getArg! 5) (i - 1)

/-- A lookup `ρ a v` of a chain of `Env.cons`, as its entry. -/
def lookup? (x : Expr) : Option Expr := do
  guard (x.isAppOfArity ``ScopedSignature.Env.cons 8)
  entry? (mkAppN x.getAppFn (x.getAppArgs.extract 0 6)) (← varIndex? (x.getArg! 7))

end EnvReader

end IPFunctor.Import
