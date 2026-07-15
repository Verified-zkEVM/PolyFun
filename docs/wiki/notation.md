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

## PFunctor and FreeM Notation

Most `PFunctor` / `FreeM` definitions are written in long form rather
than via custom notation, to keep elaboration predictable. Specifically:

- Sum, product, sigma, pi, tensor, and composition of polynomial
  functors all use named definitions
  (`PFunctor.sum`, `PFunctor.prod`, `PFunctor.sigma`, `PFunctor.pi`,
  `PFunctor.tensor`, `PFunctor.comp`) and the corresponding ring-style
  instance notation `+`, `*`, etc. defined in
  [`PolyFun/PFunctor/Basic.lean`](../../PolyFun/PFunctor/Basic.lean).
- Lens equivalence `P ≃ₚ Q` (input `\equiv p`) is defined in
  [`PolyFun/PFunctor/Equiv/Basic.lean`](../../PolyFun/PFunctor/Equiv/Basic.lean).
- `FreeM` uses standard monadic `do`-notation. There is no separate
  surface syntax for `liftBind` / `pure`; reach for `PFunctor.FreeM.lift`
  and `PFunctor.FreeM.liftPos` when you need to embed a single
  polynomial step.
- The internal hom of the tensor product `q ⊸ r` (input `\multimap`,
  U+22B8) is `PFunctor.ihom`, defined in
  [`PolyFun/PFunctor/InternalHom.lean`](../../PolyFun/PFunctor/InternalHom.lean)
  at `infixr:60`, scoped to the `PFunctor` namespace. Its positions are
  the lenses `q ⇆ r` (Spivak–Niu Ex 4.78); `Responder S q` and the game
  formers in `PolyFun/PFunctor/Dynamical/{Responder, Game}.lean` are
  dynamical systems over `q ⊸ X` and `q ⊸ r`.
- Machine sequential composition `M₁ ⨟ M₂` (input `\;;`, U+2A1F) is
  `IOMachine.seqComp`, defined in
  [`PolyFun/PFunctor/Dynamical/IOMachine.lean`](../../PolyFun/PFunctor/Dynamical/IOMachine.lean)
  at `infixl:75`. This is the book's diagrammatic composition order
  (left machine runs first), the same `⨟` used throughout
  `docs/reading/`; its intentional use is recorded as a narrow exception in
  `scripts/nolints-style.txt`. The `\;;` translation is a PolyFun workspace
  setting in [`.vscode/settings.json`](../../.vscode/settings.json), rather than
  a built-in Lean input abbreviation. Because the operator is left-associative,
  `M₁ ⨟ M₂ ⨟ M₃` parses as `(M₁ ⨟ M₂) ⨟ M₃`, whose state is
  `(M₁.State ⊕ M₂.State) ⊕ M₃.State`. This parsing convention does not
  assert that the two possible associations of machine composition are
  definitionally equal. Note `∘ₗ` on lenses is in function-composition
  order (`l ∘ₗ l'` applies `l'` first); the same `⨟` is
  available diagrammatically on lenses (`l₁ ⨟ l₂ = l₂ ∘ₗ l₁`) and charts
  (`c ⨟ c' = c' ∘c c`), and so on dynamical systems themselves.
- Qualitative program implementation `M ⊨ program` (input `\models`, U+22A8)
  abbreviates `DynComputation.Implements M program`. It is opt-in via
  `open scoped PFunctor.DynComputation`; the symbol deliberately says nothing
  about resource bounds.

If you find yourself wishing for new notation in PolyFun, consider
whether the underlying name suffices first: this library leans toward
explicit names and standard Mathlib notation, and reserves custom
operators for the UC-composition algebra above (plus the book's `⨟`
for machine composition).
