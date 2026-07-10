# Spivak–Niu Ch. 6 — The composition product (reading unit R2)

Deep-read notes for Chapter 6 (book pp. 177–224; PDF pages = book + 12).
Statements keep the book's numbering so claims are checkable against the PDF.
PolyFun anchors use current declaration names (verified 2026-07-10).

Book notation ↔ PolyFun: `y` ↔ `X`; `p ◁ q` ↔ `P ◃ Q` (`PFunctor.comp`);
lens `⇆`; horizontal product of lenses `f ◁ g` ↔ `Lens.compMap` (`◃ₗ`).

## 6.1 Definition and basic structure

- **Def 6.1 / Prop 6.2 / Cor 6.5.** `p ◁ q` is functor composition `p(q(−))`,
  again polynomial, with formula
  `p ◁ q ≅ Σ_{i∈p(1)} Σ_{j̄ : p[i]→q(1)} y^{Σ_{a∈p[i]} q[j̄(a)]}` (6.7).
  `(Poly, y, ◁)` is monoidal. PolyFun: `PFunctor.comp`, `compNth`,
  `Lens.compAssoc`, `Lens.compX` — objects and equivalences present.
- **Positions/directions (6.16)–(6.17).**
  `(p◁q)(1) ≅ Σ_{i∈p(1)} Set(p[i], q(1))`; a direction at `(i, j̄)` is a pair
  `(a, b)` with `a ∈ p[i]`, `b ∈ q[j̄(a)]`. Matches PolyFun's `comp` fields
  definitionally.
- **Ex 6.10 (+ solution p. 215).** `y^A ◁ q ≅ [Ay, q]` where `[−,−]` is the
  ⊗-hom (4.75). First bridge between ◁ and the closure of ⊗ — a good early
  sanity lemma once ticket A1 (ihom) lands.
- **Def 6.11 / Ex 6.13.** `f ◁ g` = horizontal composition of natural
  transformations; the two composition orders agree by naturality.
- **Remark 6.15 (terminology).** *Composite lens* = vertical `h ⨟ j`
  (category composition); *composition product of lenses* = horizontal
  `f ◁ g` (monoidal product on morphisms). PolyFun: `Lens.comp` vs
  `Lens.compMap`.
- **Ex 6.19, formulas (6.20)/(6.21).** Explicit on-positions/on-directions of
  `f ◁ g`: on positions `(i, j̄) ↦ (f₁ i, f♯ᵢ ⨟ j̄ ⨟ g₁)`; on directions
  `(a', b') ↦ (f♯ᵢ a', g♯_{j̄(f♯ᵢ a')} b')`. This is exactly `Lens.compMap`;
  any simp-normal form lemmas for `compMap` should mirror (6.20)/(6.21).
- **Ex 6.29.** `φ ◁ X` (constant `X`) = the `X`-component of `φ` as a natural
  transformation.
- **Ex 6.33 (+ solution p. 218) — coherence trap.** For arbitrary
  `φ : q ⇆ p ◁ q` and `ψ : q ⇆ q ◁ r`, the square
  `φ ⨟ (p ◁ ψ) = ψ ⨟ (φ ◁ r)` does **not** commute in general
  (counterexample with `q := 2`, two constant lenses `2 → 2`). Interchange
  between "act on the left" and "act on the right" is a *property of
  comodule structures* (Ch 8), not a free coherence. Do not conjecture it as
  a `simp` lemma.

## 6.1.4 Dynamical systems and ◁ ("◁ makes the clock tick")

- `φ^{◁n} : (Sy^S)^{◁n} ⇆ p^{◁n}` models `n` steps of the system
  (pp. 188–191). PolyFun gap: `compNth` exists on objects only; there is
  **no** lens-level `Lens.compNthMap : Lens p q → Lens (compNth p n)
  (compNth q n)` yet (roadmap A7a). *(Correction: earlier notes claimed a
  `speedup` combinator exists in `Dynamical/`; it does not.)*
- **Why this is not enough (p. 191) + Example 6.38.** `(Sy^S)^{◁n}` has junk
  positions: arbitrary regraftings `f : S' → S` that "move to the wrong
  state". `φ ◁ φ` carries misleading data at those positions. Poly alone
  cannot yet rule them out — the fix is the canonical transition lens and,
  in Ch 7, the comonoid laws.
- **Example 6.44 — the transition lens** `δ : Sy^S ⇆ Sy^S ◁ Sy^S`
  (pp. 198–201), with the three polybox arrows named:
  - `δ₀ = id_S` (on positions; remembers the start state),
  - `δ₁ = tgt : S × S → S`, `(s₀, s₁) ↦ s₁` (mid positions: each direction
    is relabeled as the state it points to),
  - `δ₂ = run : S × S × S → S`, `(s₀, s₁, s₂) ↦ s₂` (on directions:
    transitive coherence — two hops from `s₀` through `s₁` to `s₂` equal one
    direction `s₀ → s₂`).
  Then `δ ⨟ (φ ◁ φ) : Sy^S ⇆ p ◁ p` is the honest 2-step system, and the
  book poses (p. 201): ε-compatibility and coassociativity of δ are needed
  so that all extensions to `n` steps agree — the Ch 7 comonoid laws.
- **Ex 6.46.** δ read as a standalone dynamical system: return current
  state, receive `s₁`, return `s₁`, receive `s₂`, update to `s₂`.
- VCVio hook: `RunLimit`'s `n`-step truncations are semantically
  `δ^{(n)} ⨟ φ^{◁n}` (§7.1.5 makes `δ^{(n)}` canonical); the PolyFun-generic
  ticket is B3, but δ itself needs no comonoid vocabulary and can land in
  Phase A (A7b).

## 6.2 Lenses to composites

- **(6.6)/(3.7).** `Poly(p, q₁ ◁ ⋯ ◁ qₙ) ≅ Π_{i} Σ_{j₁} Π_{b₁} ⋯ Σ_{jₙ}
  Π_{bₙ} p[i]` — the polybox protocol. Slogan (p. 194): *a lens
  `p → q₁ ◁ ⋯ ◁ qₙ` is a multi-step policy: ask `q₁`, then `q₂`, …, then
  interpret the results.*
- **Example 6.40 — destructor triple.** A lens `φ : p ⇆ q ◁ r` is
  equivalently a triple `(φ^q, φ^r, φ^♯)`:
  `φ^q : p(1) → q(1)`; `φ^r_i : q[φ^q(i)] → r(1)`;
  `φ^♯_i : Σ_{b∈q[φ^q i]} r[φ^r_i b] → p[i]`.
  Roadmap A6: provide this as an `Equiv` (`Lens.toCompTriple`), the workhorse
  for building/destructing protocol lenses without unfolding `comp`.
- **Example 6.41 — composite-interface machines ("cascading menus").**
  A system `Sy^S ⇆ q ◁ r` returns a `q`-position, receives `b`, returns an
  `r`-position (depending on `s` and `b`), receives `c`, then updates state
  on `(s, b, c)`. Generalizes to `q₁ ◁ ⋯ ◁ qₙ`. This is exactly the
  two-phase machine shape VCVio's `IsPolyTime.bind` needs (query phase ◁
  respond phase with a shared mid-boundary). Roadmap A7c.
- **Polybox equation-reading (p. 198).** `g ⨟ (f ◁ f') = h` for
  `g : r ⇆ p ◁ p'`, `h : r ⇆ q ◁ q'` unfolds to exactly three componentwise
  equations (positions, mid, directions) — the template for the `ext`-lemma
  proving equalities of lenses into composites.

## 6.3 Categorical properties of ◁

- **Prop 6.47 — left distributivity.** `(p+q) ◁ r ≅ p◁r + q◁r` (6.48),
  `(pq) ◁ r ≅ (p◁r)(q◁r)` (6.49), with Σ/Π versions (6.50)/(6.51).
  Ex 6.55: `A(p ◁ q) ≅ (Ap) ◁ q`. **Right distributivity fails** (Ex 6.56,
  solutions p. 220): with `p := y+1, q := 1, r := 0`:
  `p ◁ (qr) ≅ 1` vs `(p◁q)(p◁r) ≅ 2`, and `p ◁ (q+r) ≅ 2` vs
  `(p◁q)+(p◁r) ≅ 3`. Roadmap A10 lemma pack; the failures belong in
  docstrings, not conjectures.
- **Prop 6.57 (Meyers) — left coclosure.** `⌈q\p⌉ := Σ_{i∈p(1)} y^{q(p[i])}`
  (book writes a column bracket `[q p]ᵀ`; (6.59)) with
  `Poly(p, r ◁ q) ≅ Poly(⌈q\p⌉, r)` (6.58). So `(− ◁ q)` is a **right**
  adjoint; hence **Prop 6.68**: ◁ preserves all limits on the left.
  Ex 6.63 (Trimble): `⌈q\p⌉` is the left Kan extension of `p` along `q`.
  Roadmap A8.
- **Ex 6.64.** (6.65): `Poly(Ay^B, p) ≅ Set(A, p(B))` — lenses out of a
  monomial are just functions on positions into an application. (6.66):
  `Poly(Ay ◁ p ◁ y^B, q) ≅ Poly(p, y^A ◁ q ◁ By)` — shifting linear/
  representable factors across the hom.
- **Example 6.67 — coalgebra bridge.** Taking `A = B = S` in (6.65):
  dynamical systems `Sy^S ⇆ p` ≅ `p`-coalgebras `S → p(S)` (Jacobs [Jac17]).
  **Already formalized in PolyFun** — the `DynSystem`/`Coalg` core is this
  equivalence; (6.65) in full generality is a cheap and worthwhile lemma.
  Footnote 6 distinguishes coalgebra-for-a-functor (this) from
  coalgebra-for-a-comonad (§7.3.3) — the class design in roadmap B1 must
  keep these apart.
- **Prop 6.73 / Ex 6.77 — left multiadjoint to `(q ◁ −)`.**
  `p ⌢_f q := Σ_{i∈p(1)} q[f(i)] · y^{p[i]}` for `f : p(1) → q(1)`, with
  `Poly(p, q ◁ r) ≅ Σ_{f : p(1)→q(1)} Poly(p ⌢_f q, r)` (6.78).
  Reading: fix the position-level policy `f`, and the residual data is an
  ordinary lens. Likely the cleanest Lean route *into* `Poly(p, q ◁ r)`.
- **Thm 6.80 / Ex 6.81 / Prop 6.83 — connected limits.** ◁ preserves
  connected limits on both sides; polynomial functors `Set → Set` preserve
  connected limits; concrete corollary (6.82):
  `p ◁ (qr) ≅ (p ◁ q) ×_{p◁1} (p ◁ r)` — a self-contained equivalence worth
  formalizing without any limit apparatus. ⊗ also preserves connected
  limits on each side (6.83).
- **Ex 6.84 (+ solution p. 223) — ⊗ vs ◁ catalogue.** Isos that hold:
  `Ay ⊗ By ≅ Ay ◁ By`, `y^A ⊗ y^B ≅ y^A ◁ y^B`, `By ⊗ p ≅ By ◁ p`,
  `p ⊗ y^A ≅ p ◁ y^A`. Non-isos with canonical cartesian lenses one way:
  `A ◁ B ≅ A` vs `A ⊗ B ≅ AB`; `y^A ⊗ p → y^A ◁ p`; `p ⊗ By → p ◁ By`.
  Every canonical lens in the catalogue is cartesian.
- **Example 6.85 — ordering lens.** `o_{p,q} : p ⊗ q ⇆ p ◁ q`, cartesian;
  image = the order-independent positions of `p ◁ q`; the `o_{p,q}` form a
  lax monoidal functor `(Poly, y, ⊗) → (Poly, y, ◁)`. Practical use:
  a hard-to-read lens `q ◁ r ⇆ p` precomposed with `o_{q,r}` becomes an
  ordinary ⊗-interaction pattern.
- **Duoidality (6.86)/Prop 6.87.** Natural interchange lens
  `(p ◁ p') ⊗ (q ◁ q') ⇆ (p ⊗ q) ◁ (p' ⊗ q')`: run two multi-step protocols
  in parallel by interleaving phase-by-phase. This is the algebra behind
  "parallel composition of two-phase games". Roadmap A9.
- **§6.3.5 — interaction with the factorization system.**
  Prop 6.88: `φ, ψ` cartesian ⟹ `φ ◁ ψ` cartesian (proof: pullback
  naturality squares + Thm 6.80). Ex 6.89: `iso ◁ vertical` is vertical, but
  `vertical ◁ id` can fail to be vertical (`φ : y ⇆ 1`, `q := 0` gives
  `0 ⇆ 1`). So the vertical class is only left-stable under isos — record
  both facts next to A3's factorization work.

## Chapter summary takeaways for PolyFun

1. The chapter's formalizable core is small and concrete, as the R0 pass
   predicted: destructor triple (6.40), transition lens δ (6.44), left
   coclosure (6.57)+(6.78), distributivity pack (6.47), ⊗/◁ catalogue (6.84)
   + ordering lens (6.85) + duoidality (6.86), cartesian preservation
   (6.88). No abstract limit machinery is needed for any of these.
2. δ is the single most important object: it is the germ of the state
   comonoid (Ch 7), the semantic content of VCVio's `RunLimit` truncations,
   and it needs only `Sy^S` to define. Land it in Phase A.
3. Two negative results to keep as guardrails: right distributivity fails
   (6.56); the ◁-action interchange square fails for arbitrary lenses
   (6.33). Both are cheap `example`-style counterexamples for
   `PolyFunTest/`.
4. The coalgebra bridge (6.65)/(6.67) confirms the DynSystem unification was
   the right call — the book derives it from the same adjunction PolyFun
   already uses.
