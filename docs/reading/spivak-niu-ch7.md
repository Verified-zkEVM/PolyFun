# Spivak–Niu Ch. 7 — Comonoids and retrofunctors (reading unit R3)

Deep-read notes for Chapter 7 (book pp. 225–288; PDF pages = book + 12).
Read: pp. 225–277 (§7.5 exercise solutions pp. 277–288 only spot-checked).
Statements keep book numbering. Companions: `spivak-niu-ch6.md` (δ's origin),
`overview.md` (Ch 8 preview of where this goes).

## 7.1 State systems, categorically

- **§7.1.1 do-nothing section.** `ε : s ⇆ y` picks a direction `id_s` at each
  state (7.1). Ex 7.2: possessing such a lens just says every position has a
  chosen direction (`s ≅ y · s'` factorization on directions).
- **§7.1.2 transition lens.** `δ : s ⇆ s ◁ s` with arrows `tgt` (mid) and
  `run` (top) (7.4). For genuine state systems `tgt(s₀, −) : s[s₀] → s(1)` is
  a *bijection* — a property the book deliberately does not encode in the
  comonoid laws. Notation: `s → t` is the unique direction at `s` targeting
  `t`. Law (7.5): `tgt(s₀, run(s₀, d₁, d₂)) = tgt(tgt(s₀, d₁), d₂)`.
- **§7.1.3 counit laws.** `δ ⨟ (ε ◁ s) = id = δ ⨟ (s ◁ ε)` (diagram (7.7)):
  on positions, δ's bottom arrow is the identity on `s(1)`; on directions,
  `run(s, id_s, s→t) = s→t = run(s, s→t, id_t)`.
- **§7.1.4 coassociativity.** `δ ⨟ (δ ◁ s) = δ ⨟ (s ◁ δ)` (7.10) ⟺
  associativity of `run` + the target law (7.5). Ex 7.11: the 5
  parenthesizations of `s ⇆ s^{◁4}` all agree given (7.10).
- **§7.1.5 running.** `Run_n(φ) := δ^{(n)} ⨟ φ^{◁n} : s ⇆ p^{◁n}`, with
  conventions `δ^{(0)} := ε`, `δ^{(1)} := id` so `Run_0(φ) = ε`,
  `Run_1(φ) = φ` (Ex 7.12). **Example 7.13**: return every other position of
  a stream system by `Run_2(φ) ⨟ π₂` — regular-interval skipping/sampling as
  a one-line composite (ready-made `PolyFunTest/` example). Drawback noted
  p. 235: one morphism per `n`, related by coherences — packaging all runs
  into a single morphism is Ch 8's cofree comonoid.

## 7.1.6–7.2 Comonoids and the Ahman–Uustalu theorem

- **Def 7.14 comonoid** in `(C, y, ◁)`: carrier `c`, eraser `ε : c → y`,
  duplicator `δ : c → c ◁ c`; left/right erasure laws (7.15) +
  coassociativity (7.16). Remark 7.18: comonoids in the functor category
  w.r.t. ◁ *are* comonads; the book (and we) stay in the positions/
  directions presentation.
- **Prop 7.20 (δ^{(n)}).** `δ^{(0)} := ε`,
  `δ^{(n+1)} := δ ⨟ (δ^{(n)} ◁ c)`; then (a) `δ^{(n)} : c ⇆ c^{◁n}`,
  (b) `δ^{(1)} = id`, (c) `δ^{(2)} = δ`, (d) *canonicity*
  `δ^{(n)} = δ ⨟ (δ^{(k)} ◁ δ^{(n−k)})` for all `k ≤ n`. This is the exact
  recursion + API for roadmap B3's `Run_n`.
- **Example 7.19.** Every state system is a comonoid (ε = do-nothing,
  δ = transition). **Example 7.22**: not every comonoid is a state system —
  the laws do not force `cod : c[i] → c(1)` to be bijective ("a feature, not
  a bug"; comonoids = *generalized* state systems). **Example 7.23 / 7.34**:
  the walking-arrow category carried by `y² + y` is the smallest
  non-state-system comonoid.
- **Thm 7.28 (Ahman–Uustalu [AU16]).** Polynomial comonoids ↔ small
  categories, one-to-one and isomorphism-preserving (Remark 7.32: on the
  strict reading, equalities). Dictionary: `c(1) = Ob 𝒞` (7.29),
  `c[i] = Σ_j 𝒞(i,j)` (7.30) — the *domain-centric* carrier (Def 7.31).
  Correspondence table (p. 243): eraser = identities; duplicator = codomains
  (mid arrow `cod`) + composition (top arrow `⨟`); erasure laws = identity
  laws + `cod id_i = i`; coassociativity = `cod(f⨟g) = cod g` + associativity.
  `δ^{(n)}` = unbiased `n`-ary composition (p. 247).
- **Examples as comonoids (§7.2.2).** Preorders; **Example 7.38**: the state
  system `Sy^S` is the *codiscrete/contractible groupoid* ("state category
  on S"). Ex 7.39 asks whether `Sy^S` carries other comonoid structures —
  comonoid structure on a fixed carrier is *data, not property* (e.g. the
  carrier `ny^n` also carries `⊔_n ℤ/n` [my example; printed solution not
  checked]). **Example 7.40**: representable comonoids `y^M` = monoids;
  Example 7.42 cyclic lists `y^{ℤ/n}`; Examples 7.43–7.44: right monoid
  actions `α : S × M → S` = comonoids on `Sy^M` (action categories);
  **Example 7.45**: B-streams `B^ℕ y^ℕ` with shift action — returns as
  Example 8.38 (it is the cofree comonoid on `By`). Def 7.47: degree of an
  object = arrows out; linear = degree 1.

## 7.3 Comonoid morphisms are retrofunctors

- **Def 7.49.** Comonoid morphism = carrier lens commuting with erasers
  (7.50) and duplicators (7.51); `Comon(C)`. Crucial: `Comon(Poly)` is *not*
  `Cat` — morphisms correspond to **retrofunctors**, not functors.
- **Def 7.55 retrofunctor** `F : 𝒞 ⇸ 𝒟`: forward on objects, backward on
  morphisms (`F♯_c : 𝒟[Fc] → 𝒞[c]`), such that F (i) preserves identities
  (7.56), (ii) preserves codomains (7.57), (iii) preserves composites
  (7.58). `Cat♯ ≅ Comon(Poly)`. Slogan (p. 257): *forward on objects,
  backward on morphisms; codomains are objects (preserved forward),
  identities and composites are morphisms (preserved backward).* History:
  first defined (opposite orientation, "cofunctors") by Aguiar [Agu97];
  "retrofunctor" follows Paré [Par23] (retromorphism of monads in Span,
  Remark 7.59). Prop 7.61: retrofunctors preserve isomorphisms; Ex 7.62:
  isos in `Cat♯` = isos in `Cat`.
- **§7.3.2 highlights** (pp. 258–267; first half read last session):
  - Arrow fields (7.71); `Mon^op ↪ Cat♯` (Prop 7.79);
    `Cat♯(𝒞, Ay) ≅ Set(Ob 𝒞, A)` (Prop 7.80); ODE flows (7.82).
  - **Retrofunctors `Sy^S ⇸ Ty^T` = very-well-behaved lenses**
    (Example 7.85): laws (7.56)–(7.58) become get-put, put-get, put-put.
    Sharper (pp. 266–267): the laws hold **iff `get` is a product
    projection** — there is `U := {u : T → S | get∘u = id, put(u t, t') =
    u t'}` with `S ≅ T × U` and `get = proj_T`; `put` is recoverable from
    the bijection (constant-complement form). Ex 7.86: converse (every
    projection extends uniquely); Ex 7.87: counting corollaries (none exist
    when `|T| ∤ |S|`). The retrofunctor bridge is now formalized as
    `Comonoid.Hom.stateLensEquiv`; the remaining B5 work is the product-
    projection/constant-complement characterization and the wider §7.3.3
    quadruple.
  - Example 7.88: canonical retrofunctor `(Ob 𝒞)y^{Ob 𝒞} ⇸ 𝒞` (send each
    morphism to its codomain). Example 7.90/Ex 7.91: objects are *not*
    representable in `Cat♯`. Example 7.92: retrofunctors into `ℝy^ℝ` =
    additive flows (`c_0 = c`, `(c_r)_s = c_{r+s}`) — real-time semantics.
- **§7.3.3 — four equivalent notions** (pp. 270–276). Fix a comonoid 𝒞 with
  carrier `c`. The following carry the same data (p. 276), and (2)–(4) are
  equivalent *categories*:
  1. retrofunctors `Sy^S ⇸ 𝒞`;
  2. **𝒞-coalgebras** `(S, α : S → c ◁ S)` with counit/coaction laws (7.97)
     (Def 7.96, Prop 7.98) — coalgebra *for the comonad*, refining Ch 6's
     coalgebra-for-the-functor (Example 6.67);
  3. discrete opfibrations `π : 𝒮 → 𝒞` with `Ob 𝒮 = S` (Def 7.99,
     Prop 7.103);
  4. copresheaves `I : 𝒞 → Set` with `Ob ∫I = S` (Def 7.104, Prop 7.108).
  Prop 7.109: discrete opfibrations = "dynamical systems on 𝒞" — and its
  proof factors `Sy → c` as vertical ⨟ cartesian, i.e. it *consumes* the
  Ch 5 factorization system (dependency: roadmap A3 → B5). More
  characterizations promised in Prop 8.68.

## Takeaways for PolyFun / VCVio

1. **B1/B2 design confirmed and sharpened.** `Comonoid` is a data-carrying
   structure on `(Poly, X, ◃)` (structure not Prop-class: Ex 7.39 —
   carriers admit multiple structures); the state comonoid on
   `selfMonomial S` is the canonical instance; state systems are
   characterized *among* comonoids by bijective `cod` (Example 7.22) — a
   predicate `IsStateSystem`, never a field.
2. **B3 has its exact spec.** `δ^{(n)}` by Prop 7.20's recursion with (d) as
   the canonicity lemma; `Run_n := δ^{(n)} ⨟ φ^{◁n}`; conventions
   `Run_0 = ε`, `Run_1 = φ`; Example 7.13 (every-other-position sampling) as
   the worked test. VCVio's `RunLimit` truncations are `Run_n` at the state
   comonoid; the ω-limit packaging question is answered by Ch 8's `𝒯_p`.
3. **B5 bridge landed; quadruple remains.** Using the implemented
   `IsVeryWellBehaved ↔ Retrofunctor (Sy^S) (Ty^T)` equivalence, formalize the
   product-projection/constant-complement theorem (pp. 266–267) — it is
   self-contained, classical (lens folklore made precise), and a crisp
   standalone result. The §7.3.3 quadruple gives machine semantics three
   more faces: coalgebra (α : S → c ◁ S — the runnable form), discrete
   opfibration (the reachable-state graph one draws), copresheaf
   (**protocol-state-indexed implementations** — the categorical home of
   "oracle implementation indexed by session state", relevant to paper 3's
   UC layer and to the `IPFunctor` story).
4. **Dependency edge discovered:** Prop 7.109's proof runs through the
   vertical–cartesian factorization, so ticket A3 is load-bearing for
   Phase B, not just Phase A hygiene.
5. **Citations to carry into papers:** comonoids-=-categories is
   Ahman–Uustalu [AU16]; retrofunctors originate with Aguiar [Agu97] and
   the name with Paré [Par23]; vwb lenses [nLa22]. Any mechanization claim
   must check prior art for [AU16] specifically (G0 agent 4 task).
