# Public APIs under Lean's module system

Lean module mode makes a declaration's name, signature dependencies, and body
three distinct parts of the API. PolyFun uses that distinction to keep
ordinary imports useful without making every implementation reducer public.

## Import choices

- `public import A` means declarations from `A` occur in this module's public
  signatures or are intentionally re-exported.
- `import A` is for implementation-only dependencies.
- `import all A` makes `A`'s opaque bodies and its private declarations
  available to the importing module's proofs. Write it immediately before the
  corresponding `import A` or `public import A`, and name in a one-line comment
  what the proofs need from it — the definitions whose bodies they unfold, or
  the private declarations they reference. Say which: a private theorem is
  referenced, not unfolded, and reading the annotation is how the next author
  learns whether narrowing that import means publishing an equation or
  publishing a lemma. An `import all` that supplies neither is dead and is
  removed.
  Outside proof modules it is a code smell: a downstream `import all PolyFun...`
  is an API audit signal, never the normal integration surface.

Changing `import` to `public import` does not expose declaration bodies. It
changes the signature/re-export boundary only.

### Who may open whose bodies

`scripts/check-modules.sh` enforces these boundaries:

| Opener | May `import all` | May not `import all` |
|---|---|---|
| `PolyFun/` proof modules | sibling `PolyFun` modules, for a named definition | any `ComplexityBackends` module |
| `ToCslib/` | nothing (upstream staging stays ordinary-import clean) | `PolyFun`, `ComplexityBackends` |
| `ComplexityBackends/` | its own modules | `PolyFun`, `ToCslib` |
| `Examples/`, `PolyFunParliamentMain.lean`, consumer packages | nothing | everything |
| `PolyFunTest/` worked examples | `ComplexityBackends` modules; `PolyFun` modules only in the grandfathered `PolyFunTest/Interaction/` examples listed in the script | `PolyFun` elsewhere |
| `PolyFunTest/ModuleAPI/` canaries | nothing | everything |

Staging opens nothing because its modules are meant to be lifted into cslib
unchanged, and cslib has no access to this repository's bodies. Tutorials, the
case-study executable and the consumer packages open nothing because they are
the evidence that the ordinary-import surface is usable.

Tests may open a backend because backend regressions legitimately inspect
machine constructions. They reach the generic library through its public API so
that the ordinary-import surface is what gets exercised; the grandfathered list
shrinks as those examples migrate to public laws and never grows.

### Two module-system facts

- A `@[simp]`- or `dsimp`-registered `rfl` theorem about a definition that is
  not exposed is rejected in the *defining* module, because the theorem is
  exported. Prove it by `simp [def]`, or expose the definition.
- `import all` rescues proofs, never definitions or exported statements. A
  `def` whose body or type needs the definitional unfolding of an imported
  non-exposed definition fails even under `import all`, and so does an exported
  theorem statement. Such dependencies force `@[expose]` upstream or a public
  equation.

## Choosing the public reducer surface

Use the smallest pattern that supports the intended consumer:

| Intended use | Preferred API |
|---|---|
| Consumers only state or apply facts about a definition | Opaque `def` plus named theorems |
| Consumers recurse or simplify one constructor at a time | Opaque recursive `def` plus public constructor equations |
| An ergonomic wrapper such as `TypeTree.node` sits over a raw constructor | Publish both the raw and wrapper-facing equations |
| Consumers construct or destruct a proposition by its literal witness shape | Expose that predicate, or provide explicit intro/elim theorems and document that spelling |
| Definitional equality is itself a promised interoperability feature | Add `@[expose]` to that declaration only; use `@[reducible]` only when unification must unfold it |

The `TypeTree.samplePath` and open-process boundary-trace APIs illustrate the
recursive pattern: the bodies stay opaque, while done, raw `liftBind`, and
`TypeTree.node` equations are public. `Observation.Refines` illustrates the
predicate exception: its documented `⟨factor, proof⟩` witness is the API, so
that one definition is exposed.

A public `p x ↔ ...` theorem is often sufficient for rewriting, but it does not
make constructor notation against opaque `p x` elaborate automatically. Test
the exact consumer spelling instead of assuming those interfaces are
equivalent under module transparency.

## Ordinary-import canaries

Module-boundary regressions need tests that do not already expose the imported
bodies. Put representative examples under `PolyFunTest/ModuleAPI/` and use only
ordinary `import` lines. Good canaries exercise:

- a downstream constructor or pattern spelling;
- a recursive reducer through its public equation;
- a theorem whose implicit arguments cross universes;
- a facade theorem by the same dot-notation path a consumer uses.

An example that imports the target with `import all` tests the implementation,
not the public API. Existing worked examples may still use `import all` for
their own proof needs; the dedicated module canary must not.

## Migration workflow

When a consumer needs `import all`:

1. Reduce the failure to a small file with an ordinary import.
2. Decide whether computation, rewriting, construction, or elimination is the
   actual requirement.
3. Add the narrow reducer or theorem to the owning module.
4. Add an ordinary-import canary using the original downstream spelling.
5. Remove the consumer's implementation import.

When hardening an older broadly exposed module, apply the same process in
reverse: inventory real consumers, publish laws for load-bearing reductions,
add canaries, and only then narrow exposure. The whole-file `@[expose] public
section`s in `PFunctor/`, `IPFunctor/`, `ITree/`, `Control/` and most of
`Realizability/` are a standing decision, not a target: every `import all`
inside `PFunctor/` and `IPFunctor/` opens a module that is already fully
exposed, so nothing there depends on hidden bodies today. Narrow a module only
after recording in its docstring whether definitional computation is part of
its contract; the per-directory status and the migration of `Realizability/`
are tracked in issue #244.

## Ongoing audit rule

### Dependent indices and node spellings

`FreeM.liftBind a next` and `(FreeM.lift a).bind next` denote the same
tree, but a dependent application mixing these index spellings can be accepted
by ordinary elaboration and rejected by rewriting's implicit-transparency
check. Use the public equation directly, or align the hypothesis with the
equation's index before rewriting:

```lean
-- path : FreeM.Path (FreeM.liftBind a next)
change FreeM.Path ((FreeM.lift a).bind next) at path
rw [FreeM.Path.cons_head_tail]
```

Direct application `FreeM.Path.cons_head_tail a next path` also works. This
does not require exposing the path representation or changing imported
`FreeM.bind` / `lift` attributes. The same distinction applies to dependent
transport: use an existing transport theorem directly when its conclusion
already matches, instead of asking `convert` to compare its types again.
The ordinary-import examples in `PolyFunTest/ModuleAPI/DependentPaths.lean`
exercise both forms, general dependent families, path composition, and the
structural replay consumers used downstream.

### Monoid traces and dependent events

Use `TraceList.positions_mul`, `occurrences_mul`, and the generator lookup
equations to observe traces. Use `TraceList.mapPartial_comp` and
`Trace.mapPartial_comp` to reason about filtering and wiring. A consumer that
needs list operations should cross the boundary explicitly with
`FreeMonoid.toList`; `TraceList.toList_mapPartial` exposes the filtered list.
Induct on a generic trace with `FreeMonoid.recOn`, whose cases are `one` and
`of_mul`, to keep the induction hypothesis on the monoid carrier.

When constructing a generator from a dependent position/answer pair, specify
the event type: `FreeMonoid.of (α := P.Idx) ⟨a, answer⟩`. Otherwise inference
can select the raw Sigma carrier before it sees the surrounding monoid
operation. Even with the explicit type, a rewrite that reconstructs the pair
can fail at implicit transparency. Direct theorem application or retaining a
named `event : P.Idx` can avoid that extra comparison. The remaining local
`Idx` overrides in trace and supply name the concrete failures and their
removal conditions; they do not justify a `FreeMonoid` override in consumers.
`PolyFunTest/ModuleAPI/Traces.lean` exercises the public laws and concrete
dependent payloads without either override.

### Cross-package consumers

Treat each cross-package `import all PolyFun...` in a downstream repository as
a bug report with four possible resolutions: expose a genuinely computational
definition, add public equations, add a constructor/eliminator or
characterization theorem, or change the downstream proof. Re-run the consumer
census at each Lean/Mathlib release upgrade; module-system changes and release
skew otherwise make old workaround counts look like current API defects.

A theorem belongs in PolyFun only when its statement can avoid `OracleSpec`,
probability, and cryptographic policy; otherwise route it one dependency level
at a time (VCVio candidates stay in VCVio), so "upstreamable" does not
collapse everything to the lowest dependency.

For a facade that reuses quotient structures, preserve instance coherence as
well as declaration names. When `inferInstanceAs` shares a hierarchy containing
data (such as `HasUnit` and `HasIdWire`), declare those instances before the
stronger law classes. Otherwise separate generated data wrappers can prevent
instance search from matching a predicate indexed by that data, even when
ordinary `rfl` proves the values equal. Test a consumer that combines the full
law instance with a data-indexed predicate; `SubTheory.IsStructural` under
free-syntax interpretation exercises this boundary.

## The `ToCslib` staging layer

`ToCslib/` is the lowest production library. It holds what PolyFun intends to upstream, written
so that the upstream pull request is a move rather than a rewrite:

- every declaration lives in the namespace it will have upstream (`PFunctor.FreeM`, `Cslib`,
  `Cslib.IsMonadHom`, `Lean.Order`, `Std.Internal`), so cslib's `topNamespace` linter and
  downstream call sites do not change when it lands;
- a lemma that duplicates an open upstream pull request carries an `-- upstream:` comment
  naming it and copies that request's statement shape; it is deleted when the request lands
  and the pin moves (cslib#856's `IsMonadHom` landed in cslib `v4.34.0`, so the hypothesis-form
  transport lemmas it superseded are gone and the remaining `forIn` transport is stated on
  `Cslib.IsMonadHom`);
- a lemma with no upstream twin yet is marked `-- upstream candidate`;
- `ToCslib` imports core, cslib, and Mathlib only — never PolyFun or `ComplexityBackends`, and
  never `Std.WP`, `Std.Do`, or `Std.Tactic.Do` directly (`scripts/check-modules.sh`
  enforces both; cslib's `IsMonadHom` module brings the legacy `Std.Do.WP` classes in
  transitively, which the fence does not police);
- PolyFun modules import `ToCslib` modules directly (`public import`) and keep no local copy of
  a lemma that lives there; ordinary-import canaries for the moved lemmas stay in
  `PolyFunTest/ModuleAPI/`, and behavioural canaries in `PolyFunTest/ToCslib/`;
- headers say `PolyFun Contributors` here and are rewritten to the individual authors at
  upstream pull-request time, when the file also gains `import Cslib.Init` and a
  `CslibTests/` entry.

Concrete machine models are not staging material: they live in the optional
`ComplexityBackends` library above PolyFun, and PolyFun never imports them
(`scripts/check-modules.sh` enforces this too).
