# Pinned Cryptol typed-AST exporter

This executable links Cryptol 3.6.0 at commit
`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`, with an explicitly identified optional
case-binder compatibility patch. It exports full dependency closures from the
official typed AST, retaining ordered type/proof binders, schemes, recursive
declaration groups, guards, comprehension branches and foreign fallback bodies.
It also retains the official `Cryptol::Reference` fallback definitions for
polynomial arithmetic and folds/scans. Locations on expressions are erased;
declaration identities and module content hashes remain.

The supported build uses GHC 9.6.7 and Cabal 3.12.1.0. `cabal.project.freeze`
records the resolved dependencies and Hackage index state. Z3 must be on `PATH`
for the frontend's type checker. The executable is threaded because Cryptol's
solver process needs the threaded Haskell runtime.

```bash
cd PolyFunCryptol/exporter
cabal build cryptol-lean-export
cabal list-bin cryptol-lean-export
```

## Modes

| Invocation | Output |
|---|---|
| `cryptol-lean-export SEARCH FILE ROOT...` | A closed bundle for the instantiated roots and their dependency closure |
| `--specialize SEARCH FILE ROOT...` | The original bundle and an untrusted candidate from Cryptol's own specializer, with primitive instantiations kept explicit |
| `--module SEARCH FILE` | The census record: public declarations, property pragmas, parameters, interfaces, provenance and locations |
| `--module-bundle SEARCH FILE` | Version 3 of `cryptol-module-bundle`: private declarations, simultaneous groups, module parameters, synonyms, nominal definitions and case alternatives |
| `--numeric`, `--classes` | The numeric and class/literal cases used to compare Lean's numeric semantics and class resolution |

`SEARCH` is the module search directory, normally the pinned Foundation checkout.
Reference fallback definitions are loaded through Cryptol's internal loader without
resetting the requested module's environment. Foreign interfaces carry canonical
ABI metadata, without checkout paths from compiler debug output.

The drivers in [`../scripts`](../scripts) call these modes. The
[tooling guide](../docs/tooling.md) lists them and their committed outputs.

## Building the identified compatibility frontend

Keep the original pinned checkout available. Create a separate worktree at the
same revision and apply `patches/case-binder-types.patch` there. In a local Cabal
project, name that checkout and this exporter as `packages`, retain Cryptol's
`-ffi -relocatable` flags, and add:

```cabal
package cryptol-lean-export
  flags: +case-binder-types
```

`python3 PolyFunCryptol/scripts/frontend.py /path/to/compatibility/cryptol`
checks that the tracked diff is exactly the committed patch and prints its
identity. The digest identifies the canonical Git diff with seven-character
object abbreviations; the stored patch omits space prefixes on empty context
lines to avoid trailing whitespace (Git accepts both representations). The
exporter records that digest in `frontend_patches`. The export drivers reject a
flag/source mismatch or any other source modification. The default Cabal project
still builds the unmodified pin with an empty patch list; that frontend retains
the known case-annotation failure. Constructor tags use exhaustive explicit
matches, independent of upstream `Show` formatting.

This provenance check does not verify Haskell or prove which source produced
an arbitrary binary. The identified frontend and serializer remain external
assumptions; Lean checks the exact artifact it receives. The negative fixture
`artifacts/regressions/case-binder-unpatched.json` is copied from the unmodified
frontend and is not repaired by the Lean checker.

## Licensing

The exporter is Apache-2.0. The compatibility patch modifies Cryptol, which is
BSD-3-Clause; see [`../NOTICE.md`](../NOTICE.md).
