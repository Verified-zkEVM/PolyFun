# Reading notes — Spivak–Niu §4.5 + Chapter 5

Source: `spivak-niu.pdf` (arXiv:2312.00990v2, Aug 2024). Book page = PDF page − 12.
Unit R1 of the reading plan (`docs/reading/roadmap.md`). Medium depth: statements
and formalization notes, not proofs. PolyFun names in backticks refer to the
current library.

## §4.5 Closure of ⊗ (pp. 125–129)

**The internal hom for the parallel product.** (4.75), p. 125:

```
[q, r] := ∏_{j ∈ q(1)} r ◁ (q[j]·y)
```

**Prop 4.85** (p. 127): `Poly(p ⊗ q, r) ≅ Poly(p, [q, r])`, natural in all three
variables. Proof is a Yoneda/universal-property chain (no machinery beyond
what PolyFun's `Lens` layer already has).

⚠ **Not the same object as PolyFun's `exp`.** `PFunctor.exp P Q =
Π_{a : Q.A} P ◁ (y + Q.B a)` matches (5.28), the *cartesian* exponential
`r^q = ∏_j r ◁ (y + q[j])` — a different closed structure (§5.3 below). The
⊗-hom `[q, r]` does not exist in PolyFun yet. Both deserve to exist, with
distinct names/notations.

**The Lean-friendly presentation.** Exercise 4.78, (4.79), p. 126:

```
[q, r] ≅ Σ_{f ∈ Poly(q,r)} y^{Σ_{j ∈ q(1)} r[f₁ j]}
```

i.e. *positions of `[q,r]` are exactly lenses `q ⇆ r`*, and directions at `f`
are pairs of a `q`-position `j` with an `r[f₁ j]`-direction. This is the
natural Lean definition (`⟨Lens q r, fun f => Σ j, r.B (f.toFunA j)⟩`): it
makes Exercise 4.87 (`Poly(p, q) ≅ [p, q]` evaluated at `1`, p. 127) definitional and avoids
the `∏∘◁` encoding entirely.

Useful facts:
- Ex 4.77 (p. 126): `[p₁ + p₂, q] ≅ [p₁, q] × [p₂, q]`.
- Example 4.81 (p. 126): `[y^A, y] ≅ Ay`, `[Ay, y] ≅ y^A`, and (4.82)
  `[p, y] ≅ Γ(p)·y^{p(1)}` where `Γ(p) = ∏_i p[i]` is the set of sections.
  So a position of `[p, y]` is a section — cf. PolyFun `Section p`; the whole
  object `[p, y]` is "the oracle interface for `p`" (this is the polynomial
  VCVio's `WireK`/`ProbResponder` implicitly inhabits).
- **eval** (4.88, p. 127): `eval : [q, r] ⊗ q → r`, with the universal
  property (p. 128): for every `f : p ⊗ q → r` there is a unique
  `f′ : p → [q, r]` with `(f′ ⊗ q) ⨟ eval = f` (currying).
- Ex 4.90 (p. 128): the do-nothing section `Sy^S → y` and the four wiring
  lenses κᵢⱼ of Example 4.70 all arise as `⊗` of identity and eval lenses —
  evidence that eval + ⊗ generate practical wiring diagrams.
- Example 4.92 (p. 128): `[q, r]` = "the environment of `q` as it affects
  `q`"; a dynamical system with interface `[q, r]` chooses interaction
  patterns `q → r` state-by-state.
- Example 4.93 (p. 129): Chu-space "with" operation
  `φ₁&φ₂ : (p₁ × p₂) ⊗ (q₁ + q₂) → r` built from closure + Ex 4.77.
- p. 125: `Poly(p, [q₁ ⊗ ⋯ ⊗ q_k, r]) ≅ Poly(p ⊗ q₁ ⊗ ⋯ ⊗ q_k, r)`: a system
  whose interface is a hom-object *selects the interaction pattern* among the
  `qᵢ` inside wrapper `r`.

## §5.1 Special polynomials and adjunctions (pp. 145–148)

- **Prop 5.2 / 5.3**: constants `I ↦ I` and linears `I ↦ Iy` are fully
  faithful `Set → Poly`.
- **Thm 5.4** (p. 146): adjoint quadruple, via three hom-isos
  `Poly(Iy, q) ≅ Set(I, q(1))`, `Poly(q, I) ≅ Set(q(1), I)`,
  `Poly(I, q) ≅ Set(I, q(0))`; i.e. `linear ⊣ (−)(1) ⊣ constant ⊣ (−)(0)`.
- **Prop 5.8** (p. 147): two-variable adjunction
  `Poly(I·p, q) ≅ Set(I, Poly(p, q)) ≅ Poly(p, q^I)`.
- **Cor 5.10**: for each set `A`: `I ↦ Iy^A ⊣ q ↦ q(A)`.
- **Prop 5.12** (p. 148): `Γ ⊣ y^(−)` with `Poly(p, y^A) ≅ Set(A, Γ(p))`,
  `Γ(p) := Poly(p, y) ≅ ∏_i p[i]`.
- **Cor 5.15** (principal monomial): `Poly(p, Iy^A) ≅ Set(p(1), I) × Set(A, Γ(p))`,
  i.e. `p ↦ (p(1), Γ(p)) : Poly → Set × Set^op` is left adjoint to
  `(I, A) ↦ Iy^A`. (§5.7 notes this composite is distributive monoidal;
  connections to entropy [Spi22] and strategic games [Cap22].)

Formalization note: all six hom-isos are small `Equiv`s between `Lens` types
and function types; none needs category-theory packaging to be useful.
`Poly(q, I) ≅ Set(q(1), I)` and `Poly(Iy, q) ≅ Set(I, q(1))` are the ones
implicitly used all over the dynamical layer (`Point`, event maps).

## §5.2 Epi–mono factorization (pp. 149–152)

- **Prop 5.18**: `f` mono ⟺ `f₁` injective and every `f♯ᵢ` surjective.
- **Prop 5.21**: `f` epi ⟺ `f₁` surjective and every induced
  `f♭ⱼ : q[j] → ∏_{i : f₁ i = j} p[i]` injective.
- Ex 5.22: `p → y` fails to be epi only for `p = 0`.
- **Prop 5.27**: Poly has epi–mono factorization (explicit: image on
  positions, then per-position epi–mono factorization on directions).
- Ex 5.24 asks whether Poly is balanced (mono + epi ⇒ iso), via "iso ⟺
  `f₁` iso and all `f♯ᵢ` iso".

## §5.3 Cartesian closure (pp. 152–153)

- (5.28): `r^q := ∏_{j ∈ q(1)} r ◁ (y + q[j])` — **this is PolyFun's `exp`
  (`instHPowPFunctor`), verbatim**.
- **Thm 5.31**: `Poly(p, r^q) ≅ Poly(p × q, r)`. Proof: Yoneda chain through
  `(3.61)`, `(3.7)`.
- Ex 5.32: evaluation `eval : r^q × q → r`.

PolyFun has the object but neither the adjunction nor eval — a self-contained
gap with an existing definition to attach lemmas to.

## §5.4 Limits and colimits (pp. 153–158)

- **Thm 5.33**: all small limits. Equalizer: positions = equalizer,
  directions = coequalizer. Mnemonic (Example 5.35, p. 154): *positions of a
  limit are the limit of positions; directions are the colimit of directions*
  — (5.36)/(5.37).
- Example 5.38 (p. 155): pullbacks explicitly — positions pull back,
  directions push out. (This is the construction the vertical–cartesian and
  base-change sections lean on.)
- **Thm 5.43**: all small colimits; coequalizers are genuinely involved
  (positions = connected components; directions = a limit over the category
  of elements of the component).
- Example 5.45 (p. 157): colimits in Poly ≠ pointwise colimits in Set^Set
  (`y² ⇉ y` has colimit `1` in Poly but a non-polynomial pointwise colimit).
  Cautionary: Poly is reflective-ish for limits but *not* for colimits.
- Ex 5.47: canonical `ε : p(1)y → p`, `η : p → y^{Γ(p)}`, and the pushout
  square (5.48) — `p` sits in a canonical vertical/cartesian bowtie between
  its linear approximation and its representable approximation.
- **Prop 5.49 / Cor 5.50** (p. 158): `p ⊗ q` is the pushout of
  `p ⊗ q(1)y ← p(1)y ⊗ q(1)y → p(1)y ⊗ q`; hence a lens `p ⊗ q → r` is
  exactly two lenses `p ⊗ q(1)y → r`, `p(1)y ⊗ q → r` agreeing on positions,
  and n-ary ⊗ is a wide pushout. **This is a wiring-diagram construction
  principle**: to wire a juxtaposition, specify each component's view with
  the others frozen to position-only shadows.

## §5.5 Vertical–cartesian factorization (pp. 158–162)

- **Def 5.51**: `f` *vertical* ⟺ `f₁` bijective; *cartesian* ⟺ every `f♯ᵢ`
  bijective. (PolyFun has `IsCartesian`; no `IsVertical` yet.)
- **Prop 5.52**: (vertical, cartesian) is a factorization system; middle
  object is explicitly `Σ_{i ∈ p(1)} y^{q[f₁ i]}` — vertical then cartesian.
- **Prop 5.53**: verticals satisfy 2-out-of-3; if `g` cartesian then
  `f ⨟ g` cartesian ⟺ `f` cartesian.
- **Prop 5.59**: cartesian ⟺ the (5.55) square is a pullback ⟺ `f` is a
  cartesian natural transformation (all naturality squares pullbacks).
- **Prop 5.63**: `+`, `×`, `⊗` preserve vertical and preserve cartesian.
- **Prop 5.64**: pullbacks preserve vertical (resp. cartesian) lenses.

## §5.6 Monoidal ∗-bifibration over Set (pp. 162–166)

Flagged in-text as "even more technical … we won't use it again in the book".
- (5.65): for `f : A → p(1)`, the pullback `f*p ≅ Σ_{a ∈ A} y^{p[f a]}`
  (re-index the position set). Note: this is literally "select/rename a
  family of oracles" at the `OracleSpec` level.
- **Thm 5.68**: cartesian lenses are exponentiable: pullback
  `f* : Poly/q → Poly/p` has a right adjoint `f_*` (formula 5.69).
- **Prop 5.72 / Thm 5.73** (p. 164–165): base change on `A.Poly`
  (polynomials with `p(1) ≅ A`): adjoint triple `f! ⊣ f* ⊣ f_*`,
  `f!p = Σ_b y^{∏_{a ↦ b} p[a]}`, `f_*p = Σ_b y^{Σ_{a ↦ b} p[a]}`; `⊗`
  preserves op-cartesian arrows, making `p ↦ p(1)` a monoidal ∗-bifibration
  [Shu08]. Intuition: `f_*` merges oracles by answer-tupling (∏), `f!` by
  answer-summing… note the counterintuitive variance (left adjoint uses ∏).

## Formalization tickets emitted (→ `roadmap.md`, Phase A unless noted)

- **A1. ⊗-internal hom.** New `PFunctor.ihom q r` via the Ex-4.78 encoding
  (positions = `Lens q r`); `eval : ihom q r ⊗ q ⇆ r`; `curry`/`uncurry`
  equivalence `Lens (p ⊗ q) r ≃ Lens p (ihom q r)` + β/η lemmas;
  `ihom_sum` (Ex 4.77), `ihom_X` (`[p,y] ≅ Γ(p)y^{p(1)}`, tie to `Section`).
- **A2. Cartesian-closure lemmas for existing `exp`.**
  `Lens p (exp r q) ≃ Lens (p * q) r`, `eval : exp r q * q ⇆ r` (Thm 5.31,
  Ex 5.32). Disambiguated from `ihom` by namespace: the cartesian transposes
  live in `PFunctor.CartesianClosed`, the tensor ones in `PFunctor.Lens`.
- **A3. `IsVertical` + factorization.** Predicate, 2-out-of-3 (Prop 5.53),
  explicit vertical–cartesian factorization with middle
  `Σ_i y^{q[f₁ i]}` (Prop 5.52), preservation by `+`/`×`/`⊗` (Prop 5.63)
  extending the existing `IsCartesian` closure lemmas; fixes the
  `Lens/Cartesian.lean` docstring over-promise.
- **A4. Adjunction pack (cheap glue).** The hom `Equiv`s of Thm 5.4,
  Prop 5.8, Prop 5.12, Cor 5.15 as standalone `Equiv`s.
- **A5. ⊗-gluing (wiring principle).** Prop 5.49/Cor 5.50 as a constructor:
  build `Lens (p ⊗ q) r` from compatible `Lens (p ⊗ q(1)y) r`,
  `Lens (p(1)y ⊗ q) r`; n-ary version for `Wiring₂`-style APIs.
- **B-track (defer until a consumer exists):** epi–mono factorization
  (Prop 5.27), balancedness, general limits/colimits, base change
  `f!/f*/f_*` (§5.6), exponentiability of cartesian lenses (Thm 5.68 — note
  possible relevance to `SubSpec` refinement, revisit after G0).
