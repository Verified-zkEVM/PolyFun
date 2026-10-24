# Foundation status

[`foundation-status.json`](../artifacts/foundation-status.json) measures how much of
the pinned [Foundation](https://github.com/NationalSecurityAgency/Foundation) library
(`7d0528bd998682788f4e23661f2829298f9e47db`) the open importer can type. It
covers every one of the 155 module instances in its 135 tracked files. It
reports typed elaboration only: semantic import, native views, source
correspondence and property proofs are separate stages. The file is regenerated
by `scripts/corpus.py --all` and checked under `./scripts/validate.sh
--cryptol-external`. When this page and the file disagree, the file is
authoritative.

## How blockers are found

For each instance, the importer links the declaration closure and then diagnoses
it (`polyfun-cryptol source module-diagnose`, backed by
`ModuleBundle.diagnose`):

- **Primitive inputs.** Each explicit primitive input is checked on its own. A
  primitive whose declared scheme fails is recorded and left out.
- **Declaration groups.** Every group is elaborated under the declared schemes of
  all groups before it. A group whose body fails keeps its declared scheme, so
  its dependents remain checkable. A group whose scheme fails is left out, and
  its dependents' "unbound value" failures are not counted again.
- **Whole-module failures.** Failures in the module's own parameters and
  constraints stop the diagnosis.

Each independent blocker is mapped to the language feature its message asks for.
An instance is accepted exactly when its diagnosis has no blockers.

## Features and their reach

| Feature | Instances that need it |
|---|---:|
| List literals (`expr:list`) | 131 |
| Partial numeric types, such as `fromTo`'s length | 118 |
| Comprehensions | 108 |
| Scheme equality after numeric normalization, for example `iterate`'s `[1 + inf]a` against `[inf]a` | 101 |
| Tuple types | 95 |
| Symbolic constraint entailment, such as `Logic [n]` or `fin n` from assumptions | 94 |
| Tuple and record selection | 79 |
| Record types | 74 |
| Guards | 68 |
| Nominal types and newtypes | 28 |
| The `PTrue` constraint | 27 |
| `Z n` | 19 |
| `PField` | 15 |
| `PPrime` | 4 |
| `case` | 4 |
| `Rational` | 2 |

Ten instances are accepted today. No single feature unblocks more than seven
more: almost every instance needs several features together, mostly through
the prelude and `Cryptol::Reference` bodies it links (`scanl`, `generate`,
`map`, `splitAt`, `zip`, `updates`, …).

The summary's `unblock_order` lists features greedily by the number of instances
they complete together with the features before them. List literals, `PPrime`,
comprehensions, scheme equality, partial numerics, entailment, tuples, selection
and records reach 58 instances. Guards and `PTrue` then reach 115, and nominal
types, `Z n`, `PField`, `case` and `Rational` complete all 155.

Supplying the 23 failing prelude and `Cryptol::Reference` declarations natively,
instead of elaborating their bodies, mainly removes the comprehension
requirement (108 to 36 instances). The algorithm modules themselves still use
lists, tuples, records, selection, guards and partial numerics.
