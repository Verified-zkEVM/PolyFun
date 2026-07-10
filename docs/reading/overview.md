# Spivak–Niu breadth pass (R0): sketch-map of Chapters 6–9

Source: `spivak-niu.pdf` (arXiv:2312.00990v2). Book page = PDF page − 12.
Sketch-level: numbered statements and Lean anchors only; R2–R4 deepen each
chapter into its own notes file. Companion files: `spivak-niu-ch5.md` (unit
R1, done), `roadmap.md`, `corrections.md`.

## The shape of Part II

Ch 6 upgrades `◁` from data to a theory (hom-sets into composites, adjoints,
duoidality). Ch 7 shows the structure that makes a state system *runnable* —
the do-nothing section `ε : Sy^S → y` and transition lens
`δ : Sy^S → Sy^S ◁ Sy^S` — satisfies comonoid laws, and that ◁-comonoids are
exactly small categories (Ahman–Uustalu), with comonoid morphisms =
retrofunctors (`Cat♯`). Ch 8 builds the cofree comonoid `𝒯_p` (the category
of `p`-trees) and shows `U : Cat♯ → Poly` has right adjoint `𝒯_₋`; then
comodules/bicomodules identify categories-acting-on-polynomials with functors
`𝒞 → Poly`, copresheaf topoi, and parametric right adjoints. Ch 9 is open
problems.

## Ch 6 — the composition product (pp. 177–224)

- **§6.1.4 (p. 188–191)**: a system `φ : Sy^S → p` iterates as
  `φ^◁n : (Sy^S)^◁n → p^◁n` — "φ tells us how the machine can run, but ◁
  makes the clock tick." Bare `(Sy^S)^◁n` has *junk positions* (arbitrary
  re-associations of states to directions); the fix is the transition lens
  (§6.2.2 / Ch 7).
- **§6.2.1 (p. 192–194)**: hom-formula (6.6)/(3.7):
  `Poly(p, q₁◁⋯◁qₙ) ≅ Π_i Σ_{j₁} Π_{b₁} ⋯ Σ_{jₙ} Π_{bₙ} p[i]` — a lens into a
  composite is a multi-step interaction policy. Example 6.40: `p → q ◁ r`
  destructs into `(φ^q : p(1) → q(1), φ^r_i : q[φ^q i] → r(1), φ♯)`. **This
  triple is the canonical constructor for two-phase machines.**
- **§6.2.2, Example 6.44 (p. 198–201)**: the transition lens
  `δ : Sy^S → Sy^S ◁ Sy^S` with components `(id_S, tgt, run)`; pure data.
- **§6.3.1, Prop 6.47 (p. 202)**: `(− ◁ r)` preserves +, ×, Σ, Π. Right
  distributivity fails (Ex 6.56); the repair is (6.82):
  `p ◁ (qr) ≅ (p◁q) ×_{p◁1} (p◁r)`.
- **§6.3.2, Prop 6.57 (p. 204, Meyers)**: left coclosure
  `[q/p] := Σ_{i∈p(1)} y^{q(p[i])}` with `Poly(p, r◁q) ≅ Poly([q/p], r)`;
  so `(−◁q)` is a right adjoint. Ex 6.64 (6.65): `Poly(Ay^B, p) ≅ Set(A, p(B))`
  — with `A = B = S` this is "dynamical systems are `p`-coalgebras"
  (Example 6.67), the bridge PolyFun's `DynSystem.out`/`Coalg` already lives
  on.
- **§6.3.3 (p. 206–211)**: Prop 6.73: `(q◁−)` has a left *multi*adjoint
  `p ⌢^f q := Σ_i q[f i]·y^{p[i]}`; Thm 6.80: ◁ preserves connected limits on
  both sides (needed later for `𝒯_p`).
- **§6.3.4 (p. 211–213)**: cartesian "ordering" lens `o_{p,q} : p ⊗ q → p ◁ q`
  (lax monoidal `(Poly,⊗) → (Poly,◁)`); duoidal interchange (6.86)
  `(p◁p′) ⊗ (q◁q′) → (p⊗q) ◁ (p′⊗q′)` — fully explicit regrouping, pure data
  (Prop 6.87 coherence is heavier and the book itself skips the diagrams).
- **§6.3.5, Prop 6.88 (p. 213)**: ◁ preserves cartesian lenses (◁ does *not*
  preserve vertical in the right variable, Ex 6.89).

## Ch 7 — comonoids and retrofunctors (pp. 225–288)

- **§7.1 (p. 225–239)**: `ε : s → y` (do-nothing), `δ : s → s ◁ s`
  (`tgt` bijective per state for genuine state systems), counit laws
  `δ ⨟ (ε◁s) = id = δ ⨟ (s◁ε)`, coassociativity `δ⨟(δ◁s) = δ⨟(s◁δ)`;
  `δ^(n) : s → s^◁n` canonical (Prop 7.20; `δ^(0) = ε`, `δ^(1) = id`).
  **§7.1.5 (p. 233–235): `Run_n(φ) := δ^(n) ⨟ φ^◁n : s → p^◁n`** — run a
  system `n` steps; `Run_0 = ε`, `Run_1 = φ`. Def 7.14: comonoid in
  `(Poly, y, ◁)`; Example 7.19: state systems are comonoids; **Example 7.22:
  not every comonoid is a state system** (comonoid laws do not force `tgt`
  bijective) — a Lean `Comonoid` class must not bake bijectivity in.
- **§7.2, Thm 7.28 (p. 240, Ahman–Uustalu)**: polynomial comonoids ≅ small
  categories. Dictionary: positions = objects; `c[i] = Σ_j 𝒞(i,j)`
  (domain-centric morphisms); ε picks identities; δ's position map = `cod`,
  direction map = composition; counit laws = identity laws, coassociativity =
  `cod(f⨟g) = cod g` + associativity. Examples: `Sy^S` = contractible
  groupoid on S (7.38); monoids = representable comonoids `y^M` (7.40);
  `B`-streams `B^ℕ y^ℕ` (7.45).
- **§7.3 (p. 253–276)**: Def 7.49/7.55: comonoid morphisms = retrofunctors
  (forward on objects, *backward* on morphisms, preserving id/cod/comp);
  `Cat♯ := Comon(Poly)`. Prop 7.61: retrofunctors preserve isos.
  §7.3.2 examples: retrofunctors to discrete `Sy` = state labelings (7.63);
  **arrow fields** = retrofunctors `𝒞 ⇸ y^ℕ` (7.71; monoid of these is
  functorial, Prop 8.62); `Mon^op ↪ Cat♯` fully faithful (Prop 7.79);
  `Cat♯(𝒞, Ay) ≅ Set(Ob 𝒞, A)` (Prop 7.80); **ODE flows are retrofunctors**
  `ℝⁿy^{ℝⁿ} ⇸ y^ℝ` (7.82 — continuous time = a different clock monoid);
  retrofunctors `Sy^S ⇸ 𝒞` = 𝒞-coalgebras (**Example 7.84**, with the
  coalgebra-for-functor vs coalgebra-for-comonad distinction in a footnote);
  retrofunctors `Sy^S ⇸ Ty^T` = **very-well-behaved lenses** (**Example
  7.85**, p. 265: (7.56)–(7.58) = get-put/put-get/put-put) — direct bridge to
  PolyFun's `Lens/State.IsVeryWellBehaved`. §7.4 (p. 276): four equivalent
  notions — retrofunctor `Sy^S ⇸ 𝒞` ≅ 𝒞-coalgebra ≅ discrete opfibration ≅
  copresheaf.

## Ch 8 — cofree comonoids and comodules (pp. 289–348)

- **§8.1.1 (p. 290–301)**: `p`-trees = **exactly `PFunctor.M p`**
  (Ex 8.14/8.16: limit of `1 ← p(1) ← p^◁2(1) ← ⋯` = terminal `p`-coalgebra).
  Prop 8.18: the cofree carrier is `t_p = Σ_{T ∈ tree_p} y^{vtx(T)}` —
  **positions = `M p`, directions = finite rooted paths** (an inductive
  family over the coinductive `M p`; the M-type analogue of `FreeM.Path`).
  Projections `ε_p^(n) : t_p → p^◁n` = depth-`n` truncations.
- **§8.1.2 (p. 301–313)**: comonoid structure: ε = empty path,
  δ = path concatenation + subtree-at-endpoint (`cod v = T(v)`).
  Prop 8.33: `𝒯_p` is a category (objects = trees, morphisms = paths).
- **§8.1.3, Thm 8.45 (p. 314)**: **`U ⊣ 𝒯_₋`** (forgetful left, cofree
  right): `Poly(c, p) ≅ Cat♯(𝒞, 𝒯_p)`. The mate's object map is
  **`M.corec`**; uniqueness is M-finality; counit is `ε_p^(1)`. A dynamical
  system `Sy^S → p` extends uniquely to a retrofunctor `Sy^S ⇸ 𝒯_p`, which
  packages *all* the `Run_n` at once (§8.1.4).
- **§8.3.1–8.3.3 (p. 327–335)**: Def 8.83/8.86/8.98: left/right comodules and
  `(𝒞,𝒟)`-bicomodules (coactions `λ : m → c ◁ m`, `ρ : m → m ◁ d` +
  coherence). Prop 8.90: left 𝒞-comodules ≅ functors `𝒞 → Poly`.
  **Thm 8.102**: eight equivalent categories (functors `𝒞 → Set` ≅ discrete
  opfibrations ≅ cartesian retrofunctors ≅ 𝒞-coalgebras ≅ constant/linear
  left comodules ≅ `(𝒞,0)`-bicomodules ≅ representable right comodules);
  `𝒞Mod₀` is the copresheaf topos on 𝒞.
- **§8.3.4 (p. 335–336)**: Prop 8.106 (Garner): `(𝒞,𝒟)`-bicomodule ≅
  parametric right adjoint `Set^𝒟 → Set^𝒞` (prafunctor) ≅ connected-limit-
  preserving functor; data-migration reading. (Bicomodule *composition* lives
  here, not in §8.3.2.)
- **§8.3.5 (p. 336–338)**: dynamics via bicomodules: a graph gives
  `Vy ◁— g —◁ Vy`; a cellular automaton is a bicomodule map
  `g ⨟ T ⇒ T`; running = composing the bicomodule `k` times. §8.4 also
  notes: colimits in `Cat♯` are created in Poly; limits are strange
  (the product of the walking arrow with itself has infinitely many objects).

## Ch 9 — open problems (pp. 349–350), condensed

14 questions; the ones that touch this project: internal logic of the topos
`[𝒯_p, Set]` of `p`-dynamical systems (Q2/Q3) and Gödel-coding its
propositions into languages machines can "work with" (Q14); ×/⊗-(co)monoids
in Poly/Cat♯/Mod (Q5); spans in Poly → Mod (Q6); dynamical systems
reading/writing databases (Q7/Q8); HoTT variant (Q9); comonoids in all of
Set^Set (Q1/Q10); monads in Poly as generalized operads (Q11); limits in
Cat♯ combinatorially (Q12); monomorphisms in Cat♯ (Q13).

## Vision adjustments after the breadth pass

1. **Phase C is more concrete than planned.** The cofree comonoid needs no
   new coinductive machinery: carrier = `⟨M p, MPath p⟩` where `MPath` is a
   small inductive family over `M p`; ε/δ are `nil`/`append`+`follow`; the
   adjunction's content is `M.corec` + M-finality, both already in
   Mathlib/PolyFun. The genuinely new object is `MPath` and the comonoid-law
   lemmas about path concatenation.
2. **The Run_n ladder should move early (Phase B core).**
   `δ^(n)`, `Run_n(φ) = δ^(n) ⨟ φ^◁n`, and the truncation projections
   `ε_p^(n)` are pure data + small lemmas, and they are the exact generic
   skeleton under VCVio's `RunLimit` (`runK` = probabilistic shadow of
   `Run_n`, `runLimit` = shadow of the limit (8.1)).
3. **Ch 6's formalizable core is small and high-leverage**: the
   `p → q ◁ r` destructor triple (Ex 6.40), the transition lens, left
   distributivity, the left coclosure adjunction (6.57), `o_{p,q}`, and the
   duoidal interchange lens (6.86) — all data + hom-set equivalences, no
   limits needed. Defer Thm 6.80 (connected limits) until `𝒯_p` forces it.
4. **A Lean `Comonoid` class must be comonoid-first** (Ex 7.22): state
   systems are the special case where `tgt` is bijective per state, not the
   definition.
5. **The `IPFunctor ≅ bicomodules-over-discrete-comonoids` claim is *not*
   stated in the book** in the sections read; it is folklore via
   Ahman–Uustalu–Garner. Treat as a conjecture to verify against the
   directed-containers literature during R4/G0 before citing it anywhere.
6. **⊗-hom ≠ cartesian exponential** (see `spivak-niu-ch5.md`): PolyFun's
   `exp` is the §5.3 object; the §4.5 `[q,r]` (positions = lenses) is new.
