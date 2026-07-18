# Spivak–Niu Ch. 8 — Cofree comonoids and comodules (reading unit R4)

Deep-read notes for Chapter 8 (book pp. 289–348; PDF = book + 12). Read:
pp. 289–334 this pass, §8.3.4–8.3.5 (pp. 335–339) in the R0 breadth pass;
§8.4 summary and exercise solutions skipped. Companions:
`spivak-niu-ch7.md` (comonoid layer), `coalgebra-related-work.md` (§1.5's
trace-equivalence directive, revisited in §8.3 below).

## 8.1 The cofree comonoid 𝒯_p

- **Carrier as a limit (8.1).** `t_p := lim (1 ← p◁1 ← p^◁2◁1 ← ⋯)` with
  the vertical lenses `p^◁n → p^◁n ◁ 1`. Since the verticals are isos on
  positions, positions-of-limit = limit-of-positions and directions =
  colimit of directions.
- **Def 8.2 / Def 8.6 / Example 8.8.** `p`-tree = rooted tree, each vertex
  labeled by a position `i` with children ≅ `p[i]` (bijectively); stage-n
  *pretree* = element of `p^◁n(1)` ("stage" not "height": branches may
  terminate early); trimming `p^◁n(!) : p^◁(n+1)(1) → p^◁n(1)`.
  `tree_p = lim` of the trimming chain (Ex 8.14), and **Ex 8.16:
  `tree_p` is the terminal `p`-coalgebra** — in Lean this is exactly
  Mathlib's `PFunctor.M p`; Ex 8.16(3) is `M.dest` a bijection. So the
  Lean route to `t_p` is `M p` directly, with the limit description as a
  derived lemma, not the definition.
- **Prop 8.18.** `t_p := Σ_{T ∈ tree_p} y^{vtx(T)}` — directions at `T` =
  vertices of `T` ≅ **finite rooted paths** of `T` (infinite "paths" are
  *rays* and are excluded). Projections `ε_p^{(n)} : t_p ⇆ p^◁n`: stage-n
  pretree on positions, height-n leaf ↦ length-n rooted path on
  directions. In Lean this is the universe-polymorphic structural recursion
  `CofreeP.projectionN`; its backward map is proved to return a vertex of
  exactly depth `n`.
- **Comonoid structure (§8.1.2, Prop 8.33).** Eraser `ε_p : t_p ⇆ y` =
  the limit projection to `y`: picks each tree's **root** = empty rooted
  path = `id_T`. Duplicator `δ_p : t_p ⇆ t_p ◁ t_p` is induced by
  connected-limit preservation (Prop 6.68 + Thm 6.80 rebuild `t_p ◁ t_p`
  as the limit of the `p^◁ℓ ◁ p^◁m` grid (8.28)), uniquely characterized
  by the **workhorse equation (8.32)**:
  `δ_p ⨟ (ε_p^{(ℓ)} ◁ ε_p^{(m)}) = ε_p^{(ℓ+m)}`.
  Concretely: `cod v := T(v)` (the subtree rooted at `v`) and composition
  = concatenation of rooted paths. Comonoid laws follow purely formally
  from (8.32) + the limit universal property — in Lean, with `M p` as
  carrier, direct path induction is available as the alternative; keep
  (8.32) as the stated spec either way.
- **The category 𝒯_p** (Prop 8.33): objects = `p`-trees, morphisms out of
  `T` = rooted paths, codomain = subtree at the path's end, identity =
  empty path, composition = concatenation. Example 8.34 is the paper-2
  narrative in one page: 𝒯_p is the *free* refinement of positions into
  states and directions into composable transitions ("states and
  transitions for (co)free").
- **Examples (§8.1, worked).** `𝒯_1 ≅ y` (terminal category); `𝒯_y` =
  `(ℕ, 0, +)` with carrier `y^ℕ`; **Example 8.38**: `t_{By} ≅ B^ℕ y^ℕ`,
  the B-streams category of Example 7.45 — the cofree comonoid on `By`;
  Example 8.39 / Ex 8.40: `t_{By^A} ≅ B^List(A) y^List(A)` (B-labeled
  A-ary trees). These are the `PolyFunTest/` instances.

## 8.1.3–8.1.6 The adjunction and its faces

- **Theorem 8.45 (forgetful–cofree).** `U : Cat♯ → Poly` has right
  adjoint `𝒯_₋`, with natural iso `Poly(c, p) ≅ Cat♯(𝒞, 𝒯_p)`; counit
  `ε_p^{(1)} : t_p ⇆ p`. The mate `F` of `φ : c ⇆ p` has components
  `δ^{(n)} ⨟ φ^{◁n}`; uniqueness by recovering the n-th component.
- **Prop 8.49 — the point of it all.** `f ⨟ ε_p^{(n)} = Run_n(φ)`:
  *the mate is the single morphism packaging every `Run_n`* — the answer
  to §7.1.5's drawback, and the semantic justification for VCVio's
  `RunLimit` being one object rather than a family. In Lean the mate is
  `M.corec`-built and is essentially the existing `DynSystem.behavior`.
  `CofreeP.extend_comp_projectionN` proves the general full-lens equation;
  `DynSystem.cofreeMate_comp_projectionN` is its `Run_n` specialization.
- **Examples 8.50–8.53.** For a halting DFA `φ : Sy^S ⇆ 2y^A`, the mate
  sends `s₀` to an element of `2^List(A)` = **the language the automaton
  accepts**, and backward on morphisms sends each word to the state
  reached (Example 8.51). For a Moore machine `Sy^S ⇆ By^A`: `F(s₀) :
  List(A) → B` converts direction-sequences to position-sequences
  *non-recursively* (Example 8.52) — this is PolyFun's `behavior`
  verbatim. Example 8.53: the mate re-read as a copresheaf on 𝒯_p
  (database instance; one table per tree). Flagship worked example for
  paper 2: "the behavior of an oracle machine is the protocol tree it
  accepts."
- **§8.1.5 functoriality.** `𝒯_φ : 𝒯_p → 𝒯_q` for `φ : p ⇆ q` (recursive
  relabeling); **Prop 8.72**: `φ` cartesian ⟹ `𝒯_φ` cartesian.
- **§8.1.6.** Prop 8.57: `𝒯_p` is **free on a graph** (vertices = trees,
  arrows = root-corolla directions); Cor 8.58: every morphism monic+epic.
  Prop 8.59–Thm 8.61: `y^ℕ` is a ×-monoid in Cat♯; arrow fields
  `Cat♯(𝒞, y^ℕ)` form a monoid; the arrow-fields functor `Cat♯ → Mon^op`
  is right adjoint to `Mon^op ↪ Cat♯` (Prop 7.79). Prop 8.62/8.63:
  `Cat♯_rep ≅ Mon^op`; Ex 8.64/Prop 8.65: `Cat♯_lin ≅ Set` with left
  adjoint `(c◁1)y` = connected components.

## 8.2 Cat♯ inherits Poly's structure

- **Prop 8.66 — factorization lifts.** Every retrofunctor factors
  vertical ⨟ cartesian *in Cat♯* (the intermediate carrier gets a
  category structure). **Prop 8.68**: cartesian retrofunctors ≅ discrete
  opfibrations (wide subcategories) — the promised extra characterization
  from §7.3.3. **Prop 8.69**: vertical retrofunctors ≅ (bijective-on-
  objects functors)^op. So the Ch 5 factorization system descends to
  Cat♯ as (boo^op, dopf) — one more consumer of ticket A3.
- **Prop 8.73 (Porst) / Cor 8.74 / Cor 8.78.** `U` is comonadic; Cat♯ has
  all small colimits (created by `U`) and all small limits (equalizers
  are connected, so ◁ preserves them; [Por19]). Record, don't formalize,
  until a consumer appears.
- **§8.2.4 ⊗ on Cat♯ (Prop 8.77 current; 8.79 in earlier-edition notes).**
  `(y, ⊗)` extends to Cat♯; `U` strong
  monoidal; **`𝒞 ⊗ 𝒟` is the product of categories in Cat**, with
  `δ_{𝒞⊗𝒟}` built from the **duoidal interchange (6.86)** — ticket A9's
  duoidal lens is literally the constructor of product protocol
  categories (UC parallel composition target). Prop 8.79 in the current
  edition (8.81 in earlier-edition notes): `𝒯_₋` is lax
  monoidal, `t_p ⊗ t_q ⇆ t_{p⊗q}` (doctrinal adjunction).

## 8.3 Comodules and bicomodules

- **Def 8.83 / Def 8.86.** Left 𝒞-comodule `λ : m ⇆ c ◁ m`; right
  𝒟-comodule `ρ : m ⇆ m ◁ d`; laws (8.84)/(8.87). Ex 8.85:
  **𝒞-coalgebras = constant left 𝒞-comodules.** Ex 8.89: left/right
  y-comodules ≅ Poly.
- **Prop 8.90.** Left 𝒞-comodules ≃ **functors 𝒞 → Poly**. (Positions of
  `m` graded over objects of 𝒞 via `|−| : m(1) → c(1)`.) Prop 8.91:
  right 𝒟-comodules ≈ functors into indexed sets. Prop 8.92/8.93: free
  right-comodule constructions (`y^G ◁ c`; free 𝒞-set on generators).
  Ex 8.94: for an object `i`, the vertical–cartesian factorization of
  `i : y ⇆ c` is `y → y^{c[i]} → c`, and `δ^i : y^{c[i]} ⇆ y^{c[i]} ◁ c`
  (δ restricted to one starting position) is a right comodule — the
  coslice as a comodule.
- **Def 8.98 bicomodule** `𝒞 ⊲–m–⊲ 𝒟`: compatible left+right coactions,
  coherence (8.99); polybox (8.100) makes the two-sided action one
  unambiguous picture. Ex 8.101: `Poly ≅ yMod_y`.
- **Theorem 8.102 — the eight-fold way.** For a comonoid 𝒞, equivalent
  categories: (1) functors 𝒞 → Set; (2) dopf(𝒞); (3) cartesian
  retrofunctors to 𝒞; (4) 𝒞-coalgebras; (5) constant left 𝒞-comodules;
  (6) (𝒞,0)-bicomodules; (7) linear left 𝒞-comodules; (8) representable
  right 𝒞-comodules (op). All but (1) isomorphic. Proof consumes:
  base change `α₁*c` (Prop 5.72) for 3≅4, adjunction Thm 5.4 for 5≅7,
  and (6.66) for 7≅8 — Phase A tickets A3/A4/A8 are the proof
  ingredients, again.
- **§8.3.4–8.3.5 (from R0).** Prafunctors (Prop 8.106, Garner):
  bicomodules `𝒞 ⊲–⊲ 𝒟` = parametric-right-adjoint functors
  Set^𝒟 → Set^𝒞; composition = data migration; dynamics as bicomodule
  composition, cellular automata as the worked example.

## Takeaways for PolyFun / VCVio

1. **C1–C3 route confirmed and simplified.** Carrier = `M p` (Ex 8.16
   *is* M-type terminality); directions = an inductive `MPath` with
   `follow` (subtree) and `append`; ε = root/nil, δ = (subtree, append);
   state the workhorse spec (8.32) `δ ⨟ (ε^{(ℓ)} ◁ ε^{(m)}) = ε^{(ℓ+m)}`
   and derive comonoid laws from it; adjunction C3 = mate/`M.corec` +
   Prop 8.49 (`mate ⨟ ε^{(n)} = Run_n`) + uniqueness by M-finality.
   `behavior`/`trajectory` get recast as the mate (Example 8.52).
2. **C4 resolution shape.** The true theorem is `U ⊣ 𝒯_₋` between Cat♯
   and Poly (Thm 8.45) — *not* a monad-comonad adjunction "FreeM ⊣
   Cofree". The honest companion is Libkind–Spivak's module structure
   (EPTCS 429). Fix `Interaction/Basic/TypeTree.lean:83` + `REFERENCES.md`
   wording accordingly when C3/C4 land (corrections item 1).
3. **A-ticket consumers multiplied.** A3 (factorization): consumed by
   Prop 7.109, Prop 8.66/8.68/8.69, Thm 8.102(3≅4), Ex 8.94. A9
   (duoidal): consumed by Prop 8.77 in the current edition (8.79 in
   earlier-edition notes; ⊗ on Cat♯ = product categories —
   the UC parallel-composition constructor). A8/(6.66): consumed by
   Thm 8.102(7≅8). Phase A is the load-bearing floor of everything.
4. **Worked examples with paper value:** DFA mate = accepted language
   (Example 8.51); Moore mate = `List(A) → B` behavior (Example 8.52);
   `t_{By}` = B-streams (Example 8.38). All three are `PolyFunTest/`
   candidates with one-line crypto readings (protocol tree an oracle
   machine accepts; transcript function of a deterministic responder).
5. **Trace-equivalence directive (G0 §1.5) status:** Ch 8's bicomodule
   layer gives homes for *structure* (dynamics as bicomodule
   composition) but the book does not treat monad-weighted trace
   equivalence; CryptHOL's determinization functor remains the design
   source for that. Noted so R4 doesn't over-promise.
