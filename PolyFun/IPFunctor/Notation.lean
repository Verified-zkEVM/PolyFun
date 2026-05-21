/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Basic
public import Lean.Elab.Do
meta import Lean.Parser.Do

/-!
# `do`-notation for `IPFunctor.FreeM`

`IPFunctor.FreeM P s α` has a state-polymorphic bind:

```
FreeM.bind : FreeM P s α → ((s' : I) → α → FreeM P s' β) → FreeM P s β
```

The continuation must accept the per-leaf post-state `s'`, so a standard
`Bind (FreeM P s)` instance cannot express it. This file plugs into the
Lean 4.29 extensible do-elaborator (`@[doElem_elab …]`) to make ordinary
`do { let x ← e; … }` blocks elaborate to the right `FreeM.bind`-tree,
threading a fresh post-state through each step.

## Activating the new elaborator

Lean 4.29 ships *two* `do` elaborators: the legacy one (active by default)
and a new extensible one. Our overrides plug into the new one, so users
must opt in by setting

```
set_option backward.do.legacy false
```

at the top of any file that wants `do`-notation for `FreeM`. To opt in
*project-wide*, add the option to your `lakefile.toml`:

```toml
[leanOptions]
backward.do.legacy = false
```

Other monads in the same file continue to work — our elaborators check
the expected type and `throwUnsupportedSyntax` for non-`FreeM` monads,
falling back to the builtin.

**Roadmap.** `backward.do.legacy` is a transitional flag (note the
`backward.` prefix). When upstream Lean flips the default to `false`
and eventually retires the option, the `set_option` lines in the test
sections of these files come out and the docstrings are updated. A
`grep -rn 'backward.do.legacy' PolyFun/` finds every site that needs
touching.

## Supported subset

* `let x ← e; …` and `let x : T ← e; …` (single-identifier `doIdDecl`).
* `let _ ← e; …` (anonymous bind, the simple underscore form).
* `e1; e2` (sequencing).
* Terminal `pure x` / `return x` (uses the existing `Pure (FreeM P s)`).
* Plain `let x := v` and `have x := v` (non-monadic binders).
* `do { … }` nested inside a `FreeM` do-block.
* `if c then e1 else e2` and `match x with | … => …` — *provided every
  arm lands at the same post-state*. This is a structural property of the
  new elaborator (`if`/`match` produces a single `m γ` for both branches)
  and cannot be relaxed from a `doElem` hook alone.

## Unsupported

* `let mut`, `:=` reassignment, `for`/`break`/`continue`, `try`/`catch`,
  `dbg_trace`, `assert!` — all require typeclasses (`Bind`, `Monad`,
  `MonadExcept`, `ForIn`) `FreeM P s` does not provide.
* Pattern bindings in `let (a, b) ← e` (the default desugaring uses
  `Bind`).

## Error messages

Two custom diagnostics are emitted when elaboration of a `FreeM`
do-block fails for the common reasons:

* **State mismatch** — when `let x ← e` is written at a step whose
  pre-state doesn't unify with the previous step's post-state. The
  message names both states.
* **Non-polymorphic remainder** — when the rest of the block forces the
  fresh post-state metavariable to a concrete value that the framework
  cannot abstract over. The message asks the user to pattern-match on
  the previous step's response or use `FreeM.bind` explicitly.

## When the constraint bites: alternatives

Because `FreeM.bind`'s continuation is universally quantified over the
post-state, only *polymorphic* tails compose. For chains where each step
lands at a concrete state, see one of the parallel notation files:

* [`PolyFun/IPFunctor/Notation/Indexed.lean`](Notation/Indexed.lean) —
  `do`-notation for `FreeM₂`, the two-index variant whose bind threads
  pre/post-states statically with no universal quantifier.
* [`PolyFun/IPFunctor/Notation/Deterministic.lean`](Notation/Deterministic.lean)
  — single-index `FreeM` plus a `DeterministicTransitions P` class that
  specializes `liftA`-style steps to a concrete post-state.
-/

@[expose] public section

namespace IPFunctor.FreeMNotation

open Lean Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Lean.Parser.Term

/-! ## Monad-info detection -/

/--
If `m` is (definitionally) `@IPFunctor.FreeM I P s` for some `I, P, s`,
return those three arguments together with the universe levels on the
`FreeM` constant; otherwise `none`. Called at the top of every
elaborator override so that non-`FreeM` monads fall through to the
builtin via `throwUnsupportedSyntax`.

This is the canonical detector — `Notation/Deterministic.lean` imports
and reuses it via `open IPFunctor.FreeMNotation`, so the two single-index
elaborators recognize exactly the same monad shapes.
-/
meta def isFreeMMonad? (m : Expr) :
    MetaM (Option (Expr × Expr × Expr × List Level)) := do
  let m ← whnf m
  let fn := m.getAppFn
  unless fn.isConstOf ``IPFunctor.FreeM do return none
  let args := m.getAppArgs
  unless args.size = 3 do return none
  return some (args[0]!, args[1]!, args[2]!, fn.constLevels!)

/-! ## State-polymorphic bind builder -/

/--
Build `@IPFunctor.FreeM.bind` for `e : FreeM P s α` followed by the
continuation in `dec`, abstracting the fresh post-state `s'` into the
continuation lambda. Mirrors `DoElemCont.mkBindUnlessPure` (without the
`pure`-contraction shortcuts) but swaps `monadInfo.m` to `FreeM P s'`
while elaborating the body, so further `let ←` steps see the new
pre-state and our overrides keep firing.
-/
meta def mkBindUnlessPureFreeM
    (dec : DoElemCont) (lvls : List Level)
    (I P s e : Expr) : DoElabM Expr := do
  let xType := dec.resultType
  let declKind := Lean.LocalDeclKind.ofBinderName dec.resultName
  withLocalDeclD `s' I fun s'FVar => do
    let newM := mkAppN (mkConst ``IPFunctor.FreeM lvls) #[I, P, s'FVar]
    withLocalDecl dec.resultName .default xType (kind := declKind) fun xFVar => do
      let β := (← read).doBlockResultType
      let body ← withReader (fun c =>
          { c with monadInfo := { c.monadInfo with m := newM } }) do
        let bodyRaw ← dec.k
        let bodyTyped ← Term.ensureHasType (mkApp newM β) bodyRaw
        -- Force any pending typeclass synthesis (most importantly `Pure
        -- (FreeM P s'FVar)` for a terminal `pure x`) before exiting the
        -- `withLocalDeclD` scope, since postponed synthesis would later
        -- run in a context where `s'FVar` is out of scope.
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars bodyTyped
      let kLam ← try
        mkLambdaFVars #[s'FVar, xFVar] body
      catch _ =>
        throwError "FreeM `do`-notation: non-polymorphic continuation \
          after `let {dec.resultName} ← …`.\n\
          The remainder of this `do`-block requires a specific post-state, \
          but `FreeM.bind` provides a fresh post-state per branch. If the \
          previous step's post-state depends on a response, pattern-match \
          on the response first, or write the `FreeM.bind` explicitly."
      return mkAppN (mkConst ``IPFunctor.FreeM.bind lvls)
        #[I, P, xType, β, s, e, kLam]

/-! ## Elaborators -/

/--
Override of `doExpr` (terminal monadic expression, also the RHS of
`let x ← rhs` once it bottoms out at a term). When the expected monad
is `FreeM P s α`, elaborate the term at that type and chain the rest
of the block through our state-polymorphic bind builder. On a type
mismatch where the actual type is `FreeM P s' α` for a different `s'`,
emit a *state mismatch* diagnostic naming the two pre-states.
-/
@[doElem_elab Lean.Parser.Term.doExpr]
meta def elabFreeMExpr : DoElab := fun stx dec => do
  let some (I, P, s, lvls) ← isFreeMMonad? (← read).monadInfo.m
    | throwUnsupportedSyntax
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  -- Elaborate the term, throwing instead of sorry-ifying on type errors so
  -- we can catch a state mismatch and emit a friendlier diagnostic. On
  -- success, this incurs no extra cost vs. the default elaboration path.
  let eExpr ← try
    Term.withoutErrToSorry <| Term.elabTermEnsuringType e mα
  catch ex =>
    let saved ← saveState
    let actual? : Option Expr ← try
      let e' ← Term.elabTerm e none
      let t ← whnf (← inferType e')
      match (← isFreeMMonad? t.appFn!) with
      | some (_, _, sActual, _) => pure (some sActual)
      | none => pure none
    catch _ => pure none
    saved.restore (restoreInfo := true)
    match actual? with
    | some sActual =>
      let sExpected ← instantiateMVars s
      let sActualN ← instantiateMVars sActual
      unless ← Lean.Meta.isDefEq sExpected sActualN do
        let expectedExpl :=
          if sExpected.isFVar then
            m!"expected pre-state: any post-state of the previous \
               `let ← …` step (bound here as `{sExpected}`; \
               `FreeM.bind` quantifies over it universally)"
          else
            m!"expected pre-state: {sExpected}"
        throwErrorAt e
          "FreeM `do`-notation: state mismatch in this `do`-block step.\n  \
           {expectedExpl}\n  \
           actual pre-state:   {sActualN}\n\
           `FreeM.bind`'s continuation has type `(s' : I) → α → FreeM P s' β`, \
           so every step after a `let ← …` must typecheck for an arbitrary \
           post-state — but this step is fixed at the concrete state above. \
           Use a state-polymorphic helper, pattern-match on the previous \
           response, or write `FreeM.bind` explicitly."
    | none => pure ()
    throw ex
  mkBindUnlessPureFreeM dec lvls I P s eExpr

/--
Override of `doLetArrow` for the `doIdDecl` form `let x ← rhs` and
`let x : T ← rhs`. The actual `FreeM.bind` is constructed inside
`mkBindUnlessPureFreeM`, invoked by `elabFreeMExpr` when `rhs` resolves
to a term — this keeps all bind-construction logic in one place.

Pattern bindings (`let (a, b) ← e`) and `mut` bindings fall through to
the builtin, which fails informatively. The simple underscore form
`let _ ← e` is handled here too.
-/
@[doElem_elab Lean.Parser.Term.doLetArrow]
meta def elabFreeMLetArrow : DoElab := fun stx dec => do
  unless (← isFreeMMonad? (← read).monadInfo.m).isSome do throwUnsupportedSyntax
  let `(doLetArrow| let $[mut%$mutTk?]? $decl) := stx | throwUnsupportedSyntax
  if mutTk?.isSome then throwUnsupportedSyntax
  match decl with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    let xType ← Term.elabType (xType?.getD (Lean.mkHole x))
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      Term.addLocalVarInfo x (← getFVarFromUserName x.getId)
      dec.continueWithUnit
  | `(doPatDecl| _%$pat ← $rhs) =>
    -- The simple underscore case: introduce a fresh name and discard it.
    let x := mkIdentFrom pat (← mkFreshUserName `__x)
    let xType ← Term.elabType (Lean.mkHole x)
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      dec.continueWithUnit
  | _ => throwUnsupportedSyntax

end IPFunctor.FreeMNotation

/-! ## Tests

These live outside the `IPFunctor.FreeM` namespace so that `pure` resolves
to `Pure.pure` (via the typeclass instance) rather than to the `FreeM.pure`
constructor (which has an explicit state argument and would shadow). -/

set_option backward.do.legacy false

namespace IPFunctorNotationTests

/-- A tiny `IPFunctor` over `Bool`. At state `false` only a trivial "flip"
shape is available, which transitions to state `true`; at state `true`
only a "read" shape is available, returning a `Nat` and staying at `true`. -/
private def demoP : IPFunctor Bool where
  A
    | false => Unit
    | true  => Unit
  B
    | false, _ => Unit
    | true,  _ => Nat
  st
    | false, _, _ => true
    | true,  _, _ => true

/-- Lift the `flip` shape into a `FreeM` action at state `false`. -/
private def flip : IPFunctor.FreeM demoP false Unit :=
  IPFunctor.FreeM.liftA false ()

/-- Lift the `read` shape into a `FreeM` action at state `true`. -/
private def read : IPFunctor.FreeM demoP true Nat :=
  IPFunctor.FreeM.liftA true ()

/-! ### Positive tests

These exercise the supported subset: a single state-changing bind followed by
a polymorphic continuation (purely `pure` / `return` / control-flow over pure
arms). The constraint comes from `FreeM.bind`'s state-polymorphic continuation
`(s' : I) → α → FreeM P s' β`: every later step must typecheck *for every
post-state `s'`*, which in practice means it must use only `Pure.pure` or
helpers that are polymorphic in the state index. -/

-- Basic `let _ ← e; pure ()`.
example : IPFunctor.FreeM demoP false Unit := do
  let _ ← flip
  pure ()

-- `let _ ← e; pure y` with an arbitrary terminal value.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  pure 42

-- A bound name available in the terminal pure.
example : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  pure (n + 1)

-- `return` form (resolves through the `Pure` instance).
example : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  return n + 1

-- Mixed pure `let :=` after a monadic bind.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let k := 17
  pure k

-- `have` (non-monadic) binder.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  have k : Nat := 3
  pure k

-- Terminal `pure` derived from intermediate result.
example : IPFunctor.FreeM demoP true Bool := do
  let n ← read
  pure (n > 0)

-- `if`-then-else over `pure` arms (branches share the post-state).
example (b : Bool) : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  if b then pure n else pure (n + 1)

-- `match` with `pure` arms.
example (b : Bool) : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  match b with
  | true  => pure n
  | false => pure (n + 1)

-- A do-block with no monadic step at all (just pure).
example : IPFunctor.FreeM demoP false Nat := do
  let x := 1
  let y := 2
  pure (x + y)

/-! ### Negative tests

These show the elaborator's custom diagnostic for state mismatches. Chaining
two `read`s after `flip` is the canonical failure mode: the post-state of
`flip` is a fresh `s'`, but `read`'s pre-state is the literal `true`. -/

/--
error: FreeM `do`-notation: state mismatch in this `do`-block step.
  expected pre-state: any post-state of the previous `let ← …` step (bound here as `s'`; `FreeM.bind` quantifies over it universally)
  actual pre-state:   true
`FreeM.bind`'s continuation has type `(s' : I) → α → FreeM P s' β`, so every step after a `let ← …` must typecheck for an arbitrary post-state — but this step is fixed at the concrete state above. Use a state-polymorphic helper, pattern-match on the previous response, or write `FreeM.bind` explicitly.
-/
#guard_msgs in
example : IPFunctor.FreeM demoP false Nat := do
  flip
  read

/--
error: FreeM `do`-notation: state mismatch in this `do`-block step.
  expected pre-state: any post-state of the previous `let ← …` step (bound here as `s'`; `FreeM.bind` quantifies over it universally)
  actual pre-state:   true
`FreeM.bind`'s continuation has type `(s' : I) → α → FreeM P s' β`, so every step after a `let ← …` must typecheck for an arbitrary post-state — but this step is fixed at the concrete state above. Use a state-polymorphic helper, pattern-match on the previous response, or write `FreeM.bind` explicitly.
-/
#guard_msgs in
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let n ← read
  pure n

/-! ### `erase` interop

On a `[Unique I]` index, `FreeM.erase` collapses `do`-block trees built
via the single-index elaborator to the corresponding `PFunctor.FreeM`
trees. The `@[simp]` lemmas `erase_punit_pure` / `erase_punit_roll` in
`Free/Basic.lean` do the simplification. -/

/-- A `PUnit`-indexed `IPFunctor`. Single-index `FreeM`'s universal
state-polymorphism constraint is vacuous here, since every leaf state
is forced to `PUnit.unit`. -/
private def demoQ : IPFunctor PUnit where
  A _ := Bool
  B _ _ := Nat
  st _ _ _ := PUnit.unit

/-- A pure-only `do`-block erases to a pure leaf — no `liftA` involved
so the universal-quantification limit doesn't bite. -/
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit
        (do let k := 17; pure k : IPFunctor.FreeM demoQ PUnit.unit Nat)
    = PFunctor.FreeM.pure (P := demoQ.toPFunctor) 17 := by
  rfl

section Regression

-- Other monads still elaborate via the builtin elaborator. These confirm
-- our overrides don't claim non-`FreeM` `do`-blocks (the `isFreeMMonad?`
-- guard returns `none`, and we `throwUnsupportedSyntax`).
example : Id Nat := do
  let x := 1
  pure (x + 1)

example : List Nat := do
  let x ← [1, 2, 3]
  pure (x + 1)

example : Option Nat := do
  let x ← some 5
  pure (x + 1)

end Regression

end IPFunctorNotationTests
