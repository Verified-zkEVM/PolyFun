# Notation Reference

PolyFun is small enough that almost all notation lives in two places. This
page is the cross-reference; the canonical definitions live in the
referenced Lean source.

## UC Composition Notations

Scoped to `Interaction.UC` (activated by `open Interaction.UC`). Defined
in
[`PolyFun/Interaction/UC/Notation.lean`](../../PolyFun/Interaction/UC/Notation.lean).

### Boundary-level

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `Δ₁ ⊗ᵇ Δ₂` | `PortBoundary.tensor Δ₁ Δ₂` | `\otimes ^b` |
| `Δᵛ` | `PortBoundary.swap Δ` (dual / flip) | `\^v` |

### Expression-level (typeclass-backed)

Works for `Raw`, `Expr`, and `Interp` via `HasPar` / `HasWire` / `HasPlug`
typeclasses. Each type has `@[simp]` bridge lemmas (e.g. `Raw.hasPar`)
that normalize `HasPar.par e₁ e₂` back to `Raw.par e₁ e₂`, so existing
simp lemmas (`interpret_par`, etc.) fire transparently.

| Notation | Meaning | Prec | Input method |
|----------|---------|------|--------------|
| `e₁ ∥ e₂` | `HasPar.par e₁ e₂` (parallel) | 70r | `\parallel` |
| `e₁ ⊞ e₂` | `HasWire.wire e₁ e₂` (wire) | 65r | `\boxplus` |
| `e ⊠ k` | `HasPlug.plug e k` (plug / close) | 60r | `\boxtimes` |

Precedence ensures `A ∥ B ⊞ C ⊠ K` parses as `((A ∥ B) ⊞ C) ⊠ K`.

## Polynomial (PFunctor) Notation

The polynomial algebra uses the Spivak–Niu book surface, scoped to the
`PFunctor` namespace (activated by `open scoped PFunctor`). The named
definitions (`PFunctor.monomial`, `purePower`, `comp`, `compNth`,
`sigma`, `pi`, …) remain the canonical API; every glyph below is sugar
that elaborates to (and pretty-prints from) the named form. Everything
is defined next to its definition in
[`PolyFun/PFunctor/Basic.lean`](../../PolyFun/PFunctor/Basic.lean)
unless noted.

| Notation | Meaning | Prec | Input method |
|----------|---------|------|--------------|
| `y` | identity/variable polynomial (unit for `◃` and `⊗`) | — | plain `y` |
| `A y^ B` | `monomial A B` | 82r | ASCII |
| `y^ B` | `purePower B` (representable) | 100 | ASCII |
| `C A` | constant polynomial | — | plain `C` |
| `P + Q`, `P * Q` | `sum` / `prod` (ring-style instances, with `0` / `1` units) | std | ASCII |
| `Σₚ i, F i` | `sigma F` (indexed sum) | body 60 | `\Sigma\_p` |
| `Πₚ i, F i` | `pi F` (indexed product) | body 60 | `\Pi\_p` |
| `P ⊗ Q` | `tensor` (Dirichlet/parallel product) | 70l | `\otimes` |
| `P ◃ Q` | `PFunctor.comp` (substitution) | 80l | `\smallsub` |
| `P ◃^ n` | `compNth P n` (composition power, book `p^{◁n}`) | 85l | `\smallsub ^` |
| `P ^ Q` | `exp` (cartesian exponential) | std | ASCII |
| `q ⊸ r` | `ihom` (tensor internal hom, [`InternalHom.lean`](../../PolyFun/PFunctor/InternalHom.lean)) | 60r | `\multimap` |
| `P ∥ Q` | `parallelSum` ([`Parallel.lean`](../../PolyFun/PFunctor/Parallel.lean)) | 62r | `\parallel` |
| `P ≃ₚ Q` | `PFunctor.Equiv` | 25l | `\equiv p` |

Conventions and glyph rationale:

- **Precedence:** the monomial infix (82) binds tighter than `◃` (80),
  so `A y^ B ◃ q` parses as `(A y^ B) ◃ q`; `◃^` (85) binds tighter
  still, so `p ◃^ n ◃ q` is `(p ◃^ n) ◃ q`.
- **The `y^` token is contiguous.** Write binary `^` (cartesian
  exponential, Mathlib style) with surrounding spaces; a variable named
  `y` immediately followed by `^` would re-tokenize as the prefix.
- **Composition powers are `◃`-marked.** `p ◃^ n` is `n`-fold `◃`, not
  `n`-fold `*` — overloading ring `^` would clash with the semiring
  reading of `+` / `*` (compare Mathlib's marked iterate `f^[n]`). The
  compatibility `NatPow` instance lives only in
  [`Deprecated.lean`](../../PolyFun/PFunctor/Deprecated.lean).
- **`◃` is composition, not the container former.** The glyph renders
  the book's composition product `p ◁ q`; it is deliberately *not*
  U+25C1 `◁` (Mathlib's monoidal whiskering) and must not be confused
  with the containers-school/Agda former `S ▷ P`, which PolyFun spells
  with the anonymous constructor `⟨S, P⟩`.
- The transitional `X`-spelling (deprecated aliases, parse-only `A X^ B`)
  lives in [`Deprecated.lean`](../../PolyFun/PFunctor/Deprecated.lean)
  and is slated for removal once downstream projects migrate.

## FreeM and Dynamical Notation

- `FreeM` uses standard monadic `do`-notation. There is no separate
  surface syntax for `liftBind` / `pure`; reach for `PFunctor.FreeM.lift`
  and `PFunctor.FreeM.liftPos` when you need to embed a single
  polynomial step.
- `Responder S q` and the game formers in
  `PolyFun/PFunctor/Dynamical/{Responder, Game}.lean` are dynamical
  systems over `q ⊸ y` and `q ⊸ r`; the positions of `q ⊸ r` are the
  lenses `q ⇆ r` (Spivak–Niu Ex 4.78).
- Diagrammatic composition `f ⨟ g` (input `\;;`, U+2A1F) applies `f` first
  and then `g`. It is available for lenses (`l₁ ⨟ l₂ = l₂ ∘ₗ l₁`), charts
  (`c₁ ⨟ c₂ = c₂ ∘c c₁`), and lens-defined dynamical systems. The `\;;`
  translation is a PolyFun workspace setting in
  [`.vscode/settings.json`](../../.vscode/settings.json), rather than a
  built-in Lean input abbreviation. Sequential returning computations use the
  named operation `DynComputation.seqComp`; there is no overloaded machine
  notation for it, and its associativity law is observational (`ObsEq`) rather
  than structural equality of nested sum-state representations.
- Qualitative program implementation `M ⊨ program` (input `\models`, U+22A8)
  abbreviates `DynComputation.Implements M program`. It is opt-in via
  `open scoped PFunctor.DynComputation`; the symbol deliberately says nothing
  about resource bounds.
- Support satisfaction judgments, opt-in via `open scoped MonadAttach` for any
  monad with a core `MonadAttach` instance: `x ⊨ₐ p` (`AllOutputs p x`, every
  possible output satisfies `p`), `x ⊨ₛ p` (`SomeOutput p x`, some possible
  output satisfies `p`), and `x ⊭ p` (`NoOutput p x`, no possible output
  satisfies `p`; input `\nvDash`, U+22AD). All three are definitionally the
  corresponding bounded quantifier over `MonadAttach.support x`, itself the
  `Set`-valued view of core's `CanReturn`; see
  [`program-logic.md`](program-logic.md).

New notation should follow the same pattern: scoped to the owning
namespace, declared next to the definition it abbreviates, with the
named form remaining the canonical API. Custom operator clusters are
reserved for the polynomial algebra above, the UC-composition algebra,
and the book-order composition of lenses, charts, and lens-defined
systems.
