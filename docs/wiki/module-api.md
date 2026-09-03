# Public APIs under Lean's module system

Lean module mode makes a declaration's name, signature dependencies, and body
three distinct parts of the API. PolyFun uses that distinction to keep
ordinary imports useful without making every implementation reducer public.

## Import choices

- `public import A` means declarations from `A` occur in this module's public
  signatures or are intentionally re-exported.
- `import A` is for implementation-only dependencies.
- `import all A` makes opaque bodies from `A` available to the importing
  module's proofs. It is acceptable inside PolyFun proof modules when the body
  dependence is deliberate. A downstream `import all PolyFun...` is an API
  audit signal and should not be the normal integration surface.

Changing `import` to `public import` does not expose declaration bodies. It
changes the signature/re-export boundary only.

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
add canaries, and only then narrow exposure. Do not make PFunctor, IPFunctor,
ITree, or Control opaque wholesale; their broad sections predate the selective
Interaction policy and may hide legitimate definitional dependencies.

## Ongoing audit rule

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

## The `ToCslib` staging layer

`ToCslib/` is the lowest production library. It holds what PolyFun intends to upstream, written
so that the upstream pull request is a move rather than a rewrite:

- every declaration lives in the namespace it will have upstream (`PFunctor.FreeM`, `Cslib`,
  `Lean.Order`, `Std.Internal`), so cslib's `topNamespace` linter and downstream call sites do
  not change when it lands;
- a lemma that duplicates an open upstream pull request carries an `-- upstream:` comment
  naming it (for example `cslib#716`, `cslib#856`) and copies that request's statement shape;
  it is deleted when the request lands and the pin moves;
- a lemma with no upstream twin yet is marked `-- upstream candidate`;
- `ToCslib` imports core, cslib, and Mathlib only — never PolyFun, and never `Std.Do`,
  `Std.Internal.Do`, or `Std.Tactic.Do` (`scripts/check-modules.sh` enforces this);
- PolyFun modules import `ToCslib` modules directly (`public import`) and keep no local copy of
  a lemma that lives there; ordinary-import canaries for the moved lemmas stay in
  `PolyFunTest/ModuleAPI/`, and behavioural canaries in `PolyFunTest/ToCslib/`;
- headers say `PolyFun Contributors` here and are rewritten to the individual authors at
  upstream pull-request time, when the file also gains `import Cslib.Init` and a
  `CslibTests/` entry.

