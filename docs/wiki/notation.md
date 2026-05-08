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
  surface syntax for `roll` / `pure`; reach for `PFunctor.FreeM.lift`
  and `PFunctor.FreeM.liftPos` when you need to embed a single
  polynomial step.

If you find yourself wishing for new notation in PolyFun, consider
whether the underlying name suffices first: this library leans toward
explicit names and standard Mathlib notation, and reserves custom
operators for the UC-composition algebra above.
