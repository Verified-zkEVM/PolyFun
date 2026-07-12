# PolyFun ↔ Spivak–Niu ↔ VCVio roadmap

Living document: reading progress, formalization tickets keyed to the book,
VCVio payoffs, publication trajectory, and an honest running assessment of
whether the abstraction is earning its keep. Companions:
`overview.md` (Ch 6–9 sketch-map), `spivak-niu-ch5.md` (R1 notes),
`corrections.md` (announced-vs-actual ledger).

Book: `spivak-niu.pdf`, arXiv:2312.00990v2 (book page = PDF page − 12).
Announced VCVio baseline: `2026-899.pdf` (ePrint 2026/899).

## Coverage snapshot (2026-07-09)

| Book | PolyFun status |
|---|---|
| Ch 1–3 lens/chart calculus, monoidal ops | Deep (`PFunctor/{Basic,Equiv,Lens,Chart}`) |
| Ch 4.1–4.4 dynamical systems, wiring | Deep (`PFunctor/Dynamical/*`, coalgebra core) |
| Ch 4.5 ⊗-closure `[q,r]`, eval | **Done (A1)**: `ihom`/`eval`/`curry`/`curryEquiv`/`ihomSum` in `PFunctor/InternalHom.lean` (note: `exp` is the §5.3 cartesian exponential, not this) |
| Ch 5 factorizations, adjunctions, (co)limits | **Done**: full vertical–cartesian factorization (A3, `Lens/Factorization.lean`), trivial-interface adjunction pack (A4, `Adjunctions.lean`), cartesian-closure equivalence `CartesianClosed.curryEquiv` (A2, `CartesianClosed.lean`); general (co)limits + A5 gluing open |
| Ch 6 ◁ theory (composites, coclosure, duoidal) | **Done**: direct composite-lens projections, `compNthMap`, δ/`twoStep` (A6/A7a/A7b), left-distributivity + `(6.65)` (A10, `Lens/Distributivity.lean`), ordering + duoidal interchange lens (A9, `Lens/Duoidal.lean`); coclosure/multiadjoint (A8) + duoidal coherence open |
| Ch 7 comonoids = categories, retrofunctors | **Done (B1/B2/B3)**: `Comonoid` structure + `δ^(n)` (`PFunctor/Comonoid.lean`), state comonoid `Sy^S` + `IsStateSystem`, `Run_n`/`nStep` (`Dynamical/RunN.lean`), monad-parametric `runWith` + `seqComp` bind-law core + `IsSimulation` (`Dynamical/{PointedMachine,Simulation}.lean`); retrofunctors + §7.3.3 quadruple (B4/B5) open |
| Ch 8 cofree comonoid, Cat♯ ⊣ Poly, bicomodules | Missing (raw material: `M p`, `M.corec`, `FreeM.Path`) |

## Reading units

- [x] **R0** breadth pass Ch 6–8 → `overview.md` (2026-07-09)
- [x] **R1** §4.5 + Ch 5 → `spivak-niu-ch5.md` (2026-07-09)
- [x] **G0** coalgebras in other provers → `coalgebra-related-work.md`
      (2026-07-10; four verified surveys + Phase B design directives +
      novelty table). Landed before Phase B API freeze as required.
- [x] **R2** Ch 6 deep (pp. 177–224) → `spivak-niu-ch6.md` (2026-07-10)
- [x] **R3** Ch 7 deep (pp. 225–288) → `spivak-niu-ch7.md` (2026-07-10)
- [x] **R4** Ch 8 deep (pp. 289–348) → `spivak-niu-ch8.md` (2026-07-10)
- [x] **R5** Ch 9 retrospective (2026-07-10; Ch 9 itself read in R0 —
      see `overview.md` — informed refresh in Phase D / D5 below)

## Formalization phases and tickets (PolyFun side; crypto-free)

### Phase A — monoidal muscle (§4.5, Ch 5, Ch 6 data) → unblocks the branch

- **A1** ⊗-internal hom `ihom q r`, positions = `Lens q r` (Ex 4.78 form);
  `eval`; `curry/uncurry : Lens (p ⊗ q) r ≃ Lens p (ihom q r)`; `ihom_sum`;
  `[p,y] ≅ Γ(p)y^{p(1)}` tied to `Section`. *(WireK core.)*
- **A2** cartesian-closure lemmas for existing `exp`:
  `Lens p (exp r q) ≃ Lens (p * q) r`, `eval` (Thm 5.31/Ex 5.32).
- **A3** `IsVertical` + vertical–cartesian factorization (Prop 5.52/5.53,
  middle `Σ_i y^{q[f₁i]}`), preservation by +/×/⊗ (Prop 5.63); fixes the
  `Lens/Cartesian.lean` docstring promise.
- **A4** adjunction pack: hom-`Equiv`s of Thm 5.4 / Prop 5.8 / Prop 5.12 /
  Cor 5.15.
- **A5** ⊗-gluing constructor (Prop 5.49 / Cor 5.50) for wiring APIs.
- **A6** composite-lens destructor: `Lens p (q ◃ r)` ≃ triple
  `(φ^q, φ^r, φ♯)` (Example 6.40); `ext` lemma from the three polybox
  equations (p. 198); the fixed-policy route (6.78)
  `Poly(p, q◁r) ≅ Σ_{f:p(1)→q(1)} Poly(p ⌢_f q, r)` (Prop 6.73/Ex 6.77) as
  the constructor of choice. *(Two-phase machine constructor.)*
- **A7** multi-step and sequential machines, in three sub-tickets:
  **a.** `Lens.compNthMap : Lens p q → Lens (compNth p n) (compNth q n)`
  (φ^◁n, §6.1.4 — `compNth` exists on objects only; the earlier claim that a
  `speedup` combinator exists in `Dynamical/` was wrong);
  **b.** transition lens `δ : selfMonomial S ⇆ selfMonomial S ◃ selfMonomial S`
  = `(id, tgt, run)` (Example 6.44) + `DynSystem.twoStep := δ ⨟ (φ ◁ φ)` —
  needs no comonoid vocabulary, lands ahead of B2;
  **c.** pointed machine (state + init + partial readout, generalizing VCVio
  `OracleMachine`) as `PFunctor/Dynamical/PointedMachine.lean`; two-phase
  composition via A6 with a shared mid-boundary (Example 6.41 "cascading
  menus"); `Implements`/`IsSimulation` transfer lemmas.
  *(Direct `IsPolyTime.bind` unlock.)*
- **A8** left coclosure `⌈q\p⌉ = Σ_i y^{q(p[i])}` + adjunction
  `Poly(p, r◁q) ≅ Poly(⌈q\p⌉, r)` (Prop 6.57); corollary (6.65)
  `Poly(Ay^B, p) ≅ Set(A, p(B))` — recast `DynSystem.toLens/ofLens` as this
  equivalence's special case; concrete connected-limit corollary (6.82)
  `p ◁ (qr) ≅ (p◁q) ×_{p◁1} (p◁r)` if a consumer appears.
- **A9** ordering lens `o_{p,q} : p ⊗ q → p ◁ q` (cartesian, Example 6.85)
  and duoidal interchange lens (6.86); the ⊗/◁ catalogue of Ex 6.84 as
  small lemmas (all canonical lenses cartesian); Prop 6.88 (◁ preserves
  cartesian lenses) filed with A3; defer full duoidal coherence (Prop 6.87).
- **A10** left-distributivity pack: `(p+q)◁r`, `(pq)◁r`, Σ/Π forms
  (Prop 6.47, 6.48–6.51), `A(p◁q) ≅ (Ap)◁q` (Ex 6.55); right-distributivity
  failures (Ex 6.56) and the ◁-action interchange failure (Ex 6.33) as
  `PolyFunTest/` counterexamples + docstring guardrails.

### Phase A — implementation status (milestone 1: A1 + A3 + A6 + A7)

Landed 2026-07-10 (build + `lake lint` + `lake test` green, no `sorry`):

- **A1 ✅** `PFunctor/InternalHom.lean`: `ihom q r` (positions = `Lens q r`),
  `eval`, `curry`/`uncurry`, `curryEquiv` (hom-set adjunction), `eval_comp_curry`
  naturality, `ihomX` (`[y,r] ≅ r`), `ihom_X_A` (`[q,y]` positions = handlers).
  *Deferred:* `ihom_sum`; the bundled Mathlib `MonoidalClosed` instance (no
  consumer needs it — PolyFun's monoidal layer is à-la-carte).
- **A3 ✅ (core)** `PFunctor/Lens/Factorization.lean`: `IsVertical`
  (`toFunA` bijective) with `id`/`comp`; `factorMid`/`factorVert`/`factorCart`;
  `factorCart_comp_factorVert = l`; the two leg-class lemmas. *Deferred to a
  follow-on:* `equivOfVerticalCartesian` (the intersection = iso; needs
  dependent transport) and the `+/×/⊗/◃` preservation suite (Prop 5.63, 6.88).
- **A6 ✅** `PFunctor/Lens/Composite.lean`: direct `Lens.compOuter` /
  `compInner` / `compPullback` views of a lens into a composite (Example 6.40),
  without a second representation. The ordinary `Lens.ext` principle applies.
  *Deferred:* the (6.78) fixed-policy
  route (A8 refinement).
- **A7a ✅** `Lens.compNthMap` (φ^◁n) + `_zero`/`_succ`/`_id` (same file).
- **A7b ✅** `PFunctor/Dynamical/Speedup.lean`: `Lens.transitionLens` (δ, a
  cited alias of the pre-existing `Lens.fixState`) and `DynSystem.twoStep`
  (lifting the pre-existing `Lens.speedup`) with `twoStep_toLens`/`_state`.
  General `nStep` intentionally left to B3 (needs `δ^(n)`).
- **A7c ✅ (structural)** `PFunctor/Dynamical/PointedMachine.lean`: the
  `PointedMachine` structure (VCVio `OracleMachine`'s generic core); `seqComp` with
  `M₁.State ⊕ M₂.State` (Example 6.41 — the structural unlock for
  `IsPolyTime.bind` / `OracleMachine.seqComp`); phase `rfl` lemmas; fuelled
  `toComp`; `toComp_seqComp_inr` (second phase faithful to `M₂`);
  `DynSystem.ReachableIn` (in `Dynamical/Run.lean`, via `Prefix.last`).
  *Deferred (documented, not `sorry`):* the fuel-exact cross-phase `bind` law
  and the `IsSimulation`/`Implements`-via-`behavior_unique` transfer.

The **honest split** confirmed in code: A7c gives the *structural* half of
`IsPolyTime.bind`; the remaining half is the TM running-time bound
(`VCVio/ToMathlib/Computability/PolyTimeTM.lean:537-552`, a documented VCVio
`sorry`), which PolyFun does not own.

### Phase A — implementation status (milestone 2: A2 + A4 + A8·(6.65) + A9 + A10 + A1/A3 deferrals)

Landed 2026-07-10 (five parallel subagents; full `lake build` + `lake lint` +
`lake test` green, no `sorry`):

- **A2 ✅** `PFunctor/CartesianClosed.lean`: the cartesian exponential
  `exp`'s `CartesianClosed.eval`, `curry`, `uncurry`, the full forward
  round-trip `uncurry_curry`, the full reverse `curry_uncurry`, and the packaged
  `curryEquiv` (namespaced `PFunctor.CartesianClosed`, mirroring
  Mathlib's `CartesianClosed`/`MonoidalClosed` split against the ⊗-side
  `Lens.curry`).
- **A4 ✅** `PFunctor/Adjunctions.lean`: `homFromZero`/`homToOne`/`homFromX`/
  `homToConst`/`homToLinear` (trivial-interface hom-set `≃`s, Thm 5.4 family).
  **A5 (⊗-gluing) deferred** — the exact Prop 5.49/5.50 statement wasn't
  confirmable from the notes; noted, not stubbed.
- **A8 partial ✅** `(6.65)` `homMonomialEquiv : Lens (monomial A B) p ≃ (A → p.Obj B)`
  landed in `Lens/Distributivity.lean`. The coclosure `⌈q\p⌉` + multiadjoint
  (6.78) remain open.
- **A9 ✅** `Lens/Duoidal.lean`: `orderingLens` (+ `orderingLens_isCartesian`),
  the four ⊗/◁ catalogue isos, and the full `duoidalLens` interchange (6.86).
  Duoidal coherence (Prop 6.87) deferred by design.
- **A10 ✅** `Lens/Distributivity.lean`: `scalarCompDistrib` (Ex 6.55),
  lens-level `prodCompDistrib` (6.49), plus the Ex 6.56 right-distributivity
  **failure** proved (`IsEmpty` of a position bijection). `(6.48)`/Σ-form reused
  from pre-existing `sumCompDistrib`/`sigmaCompDistrib`. Π-form (6.51) open.
- **A1/A3 deferrals cleared ✅** in `InternalHom.lean` / `Lens/Factorization.lean`:
  `ihomSum` (full `≃ₗ`), `IsVertical`/`IsCartesian` closure under `+`/`×`/`⊗`,
  `IsCartesian.compMap` (Prop 6.88), and `equivOfVerticalCartesian` (the
  intersection = iso, via the existing `PFunctor.Equiv.toLensEquiv` bridge).

Two **math corrections to the plan** the agents caught (logged in
`corrections.md`): `ihomSum`'s target is the categorical product `*`, not `⊗`
(a Σ over a *sum* is a *coproduct* of sigmas); and the catalogue iso
`By ⊗ p ≅ By ◃ p` needs `linear B`, not the constant `C B` (which is false).

**Phase A remaining (open, lower urgency):** A5 (⊗-gluing), A8 coclosure +
multiadjoint (6.78), general Ch 5 (co)limits/base-change,
duoidal coherence (6.87), Π-distributivity (6.51). None block the VCVio
consumers; they are natural follow-ons or Phase B/C prerequisites.

### Phase B — comonoid layer (Ch 7) — API freeze after G0

- **B1** `Comonoid` on `(Poly, y, ◃)` as a data-carrying structure (not a
  Prop-class: carriers admit multiple structures, Ex 7.39; state-system-ness
  is the predicate of Ex 7.22, never a field); `δ^(n)` recursion +
  canonicity (Prop 7.20 (a)–(d)); counit/coassoc laws (7.15)/(7.16).
- **B2** state comonoid on `selfMonomial S` (`ε` = do-nothing, `δ` =
  `(id, tgt, run)`; Example 6.44 / 7.19 / 7.38 "contractible groupoid");
  `IsStateSystem` = per-state bijective `cod` (Example 7.22); representable
  comonoids `y^M` = monoids (Example 7.40) as second instance family.
- **B3** `Run_n(φ) := δ^(n) ⨟ φ^◁n` (§7.1.5) with conventions `δ^(0) = ε`,
  `δ^(1) = id` so `Run_0 = ε`, `Run_1 = φ` (Ex 7.12); truncation
  projections; monad-parametric run-truncation and ω-limit skeleton
  (generic core of VCVio `RunLimit`; SPMF ωCPO stays downstream). Worked
  test: every-other-position sampling `Run_2 ⨟ π₂` (Example 7.13).
- **B4** retrofunctors (Def 7.55, laws (7.56)–(7.58)) = `Comon(Poly)`
  morphisms (Def 7.49); `Cat♯` as a category; Prop 7.61 (isos pull back).
  Cite Aguiar [Agu97] (cofunctors) and Paré [Par23] (name).
- **B5** the state-machine semantics quadruple (§7.3.3, p. 276): for a
  comonoid 𝒞, the equivalent notions (1) retrofunctors `Sy^S ⇸ 𝒞`,
  (2) 𝒞-coalgebras `α : S → c ◁ S` (Def 7.96 / Prop 7.98 — the
  comonoid-interface upgrade of `DynSystem`), (3) discrete opfibrations
  (Prop 7.103), (4) copresheaves `𝒞 → Set` (Prop 7.108) —
  protocol-state-indexed implementations. Specialization:
  `Retrofunctor (Sy^S) (Ty^T) ≃ IsVeryWellBehaved` (Example 7.85: laws
  become get-put/put-get/put-put) *plus* the constant-complement theorem
  (pp. 266–267): vwb ⟺ `get` is a product projection `T × U → T`.
  **Depends on A3**: Prop 7.109's proof runs through vertical–cartesian
  factorization.
- **B6** `FreeM P` as ◁-monoid; handlers/`mapMHom` as monoid morphisms
  (universal property behind `simulateQ`).

### Phase B — implementation status (spine: B1 + B2 + B3 + PointedMachine finish)

Landed the K-L-prioritized machine spine (crypto-free):

- **B1 done** — `PFunctor.Comonoid` (Def 7.14) as an à-la-carte structure with
  counit/comult and the three lens laws through `compX`/`XComp`/`compAssoc`
  (`PFunctor/Comonoid.lean`). The `MonoidalCategory (Poly, ◃, y)` bundle and a
  `Comonoid.Hom` (retrofunctor) are deliberately deferred (B4).
- **B2 done** — `stateComonoid S` on `Sy^S` with `δ = fixState` and the stay-put
  counit; **all three comonoid laws are `rfl`** (discharges the laws
  `Speedup.lean` flagged unproved). `IsStateSystem` (Ex 7.22) as a predicate,
  proved for `stateComonoid`. `Comonoid.comultN` = `δ^(n)` (Prop 7.20) with its
  defining equations; full canonicity (all bracketings agree) deferred.
  Representable `y^M ≃ monoid` (Ex 7.40) deferred.
- **B3 done** — `DynSystem.nStep` = `Run_n` (`Dynamical/RunN.lean`), finishing
  the `Speedup.lean` `nStep` deferral; **`twoStep_toLens_eq` (the `n = 2`
  coherence with the existing `twoStep`) is `rfl`**. The monad-parametric run
  `PointedMachine.runWith = FreeM.mapM ∘ toComp` with `runWith_succ` (the `runLimit_fix`
  shadow) and `runWith_output_some` (fuel irrelevance, the
  `runK_eq_of_apply_none_eq_zero` shadow); the `Option`/fuel pays-rent instance
  is in `RunNExamples.lean`. The ω-limit `ωSup` stays downstream (SPMF ωCPO).
- **PointedMachine finish** — `toComp_seqComp_inl` fixes the first-phase operational
  behaviour (with `toComp_seqComp_inr` this is the structural `IsPolyTime.bind`
  content); the naive fuel-additive single-`bind` law is **false** (fuel threads
  continuously), so the fuel-exact form via reachability + fuel-irrelevance is a
  noted next increment. Generic `IsSimulation` + `behavior_eq_of_isSimulation`
  (via `behavior_unique`/`M.corec_eq_corec`) in `Dynamical/Simulation.lean`;
  the stutter-budget variant is deferred.

Full `lake build` + `lake lint` + `lake test` green with `--wfail`, no `sorry`.
Open Phase B remnants (B4/B5 retrofunctors + §7.3.3 quadruple, B6 ◁-monoid,
full Prop 7.20 canonicity, `runWith` = `toComp` at `m = FreeM`) are non-blocking
follow-ons; B4/B5 arrive with the Phase C cofree layer.

### Phase C — cofree comonoid and adjunctions (Ch 8.1–8.2)

- **C1** `MPath p : M p → Type` (finite rooted paths; inductive over
  coinductive) + `follow : (T : M p) → MPath p T → M p` (= `cod`, the
  subtree at a path's end) + append/assoc lemmas. Bridge lemma: `M p` *is*
  `tree_p` (Ex 8.16 — terminal `p`-coalgebra); trimming projections
  `ε_p^{(n)}` per Prop 8.18.
- **C2** carrier `t_p := ⟨M p, MPath p⟩` (Prop 8.18); ε = root/nil,
  δ = (follow, append); comonoid laws (Prop 8.33) derived from the
  workhorse spec (8.32) `δ ⨟ (ε^{(ℓ)} ◁ ε^{(m)}) = ε^{(ℓ+m)}` (or by
  direct path induction — decide by proof ergonomics). Instances:
  `t_1 ≅ y`, `t_y ≅ y^ℕ` = (ℕ,0,+), `t_{By} ≅ B^ℕ y^ℕ` = B-streams
  (Example 8.38), `t_{By^A} ≅ B^{List A} y^{List A}` (Ex 8.40).
- **C3** `U ⊣ 𝒯_₋` (Thm 8.45): `Lens c p ≃ Retrofunctor 𝒞 (𝒯_p)`; mate via
  `M.corec`; uniqueness via M-finality; **Prop 8.49**:
  `mate ⨟ ε_p^{(n)} = Run_n(φ)` — the mate packages every finite run.
  Functoriality `𝒯_φ` (§8.1.5) + `φ` cartesian ⟹ `𝒯_φ` cartesian
  (Prop 8.72); `𝒯_p` free on a graph (Prop 8.57); lax monoidality
  `t_p ⊗ t_q ⇆ t_{p⊗q}` (Prop 8.81). Worked tests with paper value:
  DFA mate = accepted language (Example 8.51); Moore mate =
  `List A → B` (Example 8.52) — recast `DynSystem.behavior` as the mate.
- **C4** honest statement replacing the `FreeM ⊣ Cofree` slogan: the true
  adjunction is `U ⊣ 𝒯_₋` between `Comon(Poly)` and `Poly` (Thm 8.45);
  the free-monad/cofree-comonad relationship is Libkind–Spivak's module
  structure (EPTCS 429). Fix `Interaction/Basic/Spec.lean:83` +
  `REFERENCES.md:65` wording; resolves `corrections.md` item 1; recast
  `behavior`/`trajectory` as induced universal maps.

### Phase D — comodules, bicomodules, research (Ch 8.3 + Ch 9)

- **D1** left/right comodules, bicomodules (Defs 8.83/8.86/8.98, laws
  (8.84)/(8.87)/(8.99)); `𝒞`-coalgebras = constant left comodules
  (Ex 8.85); left 𝒞-comodules ≃ functors `𝒞 → Poly` (Prop 8.90);
  `Poly ≅ yMod_y` (Ex 8.101).
- **D2** selected Thm 8.102 legs (start with the self-contained 5≅7≅8 —
  their proofs consume only Thm 5.4/A4 and (6.66)/A8); leg 3≅4 needs
  base change (Prop 5.72); copresheaf-topos statement recorded, not
  formalized, until a consumer. Cat♯-level factorization
  (Props 8.66/8.68/8.69: (boo^op, dopf) system) filed with B4 as its
  natural extension.
- **D3** prafunctor reading (Prop 8.106) + bicomodule composition; dynamics
  as bicomodule composition (§8.3.5) tied to `Interaction/Concurrent`.
  Note (from G0 §1.5): the book does *not* supply monad-weighted trace
  equivalence — CryptHOL's determinization functor stays the design
  source for observational equivalence; don't over-promise here.
- **D4** `IPFunctor I J` ↔ bicomodules over discrete comonoids. G0 found
  the citable sources (Garner's HoTTEST 2019 talk; Spivak *Functorial
  Aggregation* JPAA 2025; Lynch–Shapiro–Spivak Cat♯) — the statement is
  published math, never mechanized; Ahman–Uustalu don't use bicomodule
  language. Proceed as a formalization target with those citations.
- **D5** research tracks (each needs an explicit motivation memo before
  any Lean), refreshed after R4:
  - *Q2/Q3/Q14 — internal logic of `[𝒯_p, Set]`*: now concrete. By
    Thm 8.102(1) + Example 8.53, machine semantics (mates) literally
    *are* copresheaves on `𝒯_p`, so the topos `[𝒯_p, Set]` is the
    semantic home of machine behaviors, and its internal logic is a
    specification language for them. The bet: VCVio's Loom-style
    `wp`/`Triple` layer (`Control/Monad/Algebra`) is a fragment of that
    internal logic. Highest-value research track; natural paper-3
    companion.
  - *Q5 — ⊗-monoids in Cat♯*: grounded by Prop 8.79 (⊗ on Cat♯ =
    products of categories, built from the duoidal lens). ⊗-monoids =
    monoidal protocol categories — the multiparty/UC parallel-
    composition algebra.
  - *Q11 — monads in Poly as generalized operads*: multiparty wiring /
    session-typed composition; keep as exploratory.
  - Dropped for now: Q6/Q7/Q8 (spans, database dynamics), Q9 (HoTT),
    Q12/Q13 (Cat♯ combinatorics) — no VCVio consumer in sight.

## VCVio payoff map (downstream swaps happen on VCVio branches, not here)

| PolyFun ticket | VCVio consumer |
|---|---|
| A1 (`ihom`, eval, curry) | `WireK`/`ProbResponder` becomes wiring along eval; unify with UC `processSemanticsOracle` |
| A6+A7 (composite machines) | `IsPolyTime.bind`, `TwoPhaseGame` machine pipeline |
| A3 (vertical/cartesian) | `LawfulSubSpec` theory; paper's Thm 5.1 restated as factorization corollary |
| B2+B3 (`Run_n`, limits skeleton) | `RunLimit` (`runKT`/`runChain`/`runLimit`) as SPMF instance |
| B6 (handlers as monoid morphisms) | `simulateQ` universal property; handler-stack algebra |
| C3 (mate/corec) | `OracleComp.toITree` reverse bridge; machine behavior semantics |
| D3 (bicomodule dynamics) | UC environments/hybrids as composition (paper 3) |

## Publication trajectory

- **Paper 1 (announced, ePrint 2026/899)**: oracle effects & handlers,
  ordered-monad-algebra program logic, SSP, forking without rewinding
  axioms. Corrections tracked in `corrections.md`.
- **Paper 2 (candidate)**: coalgebraic adversaries — machines as pointed
  dynamical systems over the same polynomial substrate, TM-grounded PPT,
  run-truncation/limit semantics, two-phase composition. Narrative: programs
  in the free monad, behaviors in the cofree comonad, one substrate.
  Requires: Phases A–B + G0 related-work grounding.
- **Paper 3 (candidate)**: categorical UC (paper 1 §10 promise) via
  open-processes + comonoids/retrofunctors + bicomodule composition.
  Requires: Phases C–D matured.

## What sets us apart (differentiation, grounded by G0)

Two framings for two audiences; both rest on the same verified facts from
`coalgebra-related-work.md`. The uniqueness claim, stated carefully: each
neighbor holds one piece — CryptHOL has coinductive resumptions +
probability (no dependent interfaces, no package algebra, and third-party
users route around its coinductive layer); SSProve has the package algebra
(no coinduction — everything terminates by construction); the ITrees
lineage has coinduction + interp algebra (no crypto, no packages);
sinhp/Poly has categorical polynomial functors (no lenses-as-Homs, no
dynamics, no crypto). **PolyFun + VCVio is the only line composing all
four pieces, and the only one doing it over a single substrate with the
book's full lens/comonoid superstructure as the roadmap.** No other group
connects Poly to protocol or crypto semantics at all.

**For a formalization/math audience** (the Mathlib-style-abstraction
pitch): Mathlib has *no morphisms between `PFunctor`s at all* — the entire
category Poly, its three monoidal structures, closures, factorization
system, and comonoid theory are missing upstream; PolyFun is that layer,
built Mathlib-idiomatically. The G0 novelty scan found **no mechanization
in any proof assistant** of: ⊗-closure with eval/curry (A1),
vertical–cartesian factorization on the lens category (A3), ◁-comonoids =
small categories (B1, Ahman–Uustalu), retrofunctors ↔ vwb lenses + the
constant-complement theorem (B5), the cofree comonoid with its universal
property (C2/C3), the pattern-runs-on-matter module structure (C4), or
bicomodules (D1). Supporting technical distinction: strong bisimulation of
our ITrees is *definitional equality* via the M-type universal property —
eliminating the setoid/`Proper`/paco cost center that the Rocq ecosystem
documents at length, and refuting POPL 2020's printed judgment that Lean
is "seemingly inadequate to the task". Citation obligations: sinhp/Poly,
Ahman's Directed-Containers, Aberlé 2604.01303, 1lab, Finster et al.,
Mathlib QPF, Libkind–Spivak EPTCS 429.

**For a crypto audience** (the fewer-axioms/reusable-combinators pitch;
this audience is unmoved by "nice category theory", so lead with outcome
deltas): (1) **Rewinding without axioms** — EasyCrypt needed a four-paper
arc (2022–2026: choice-based reflection, the per-adversary `RewProp`
serialization axiom schema, an unmerged expected-cost fork, forgetful-
oracle scaffolding) to mechanize the forking lemma; in a syntax-tree
substrate every ingredient is definitional and only the probability
analysis remains. (2) **Structural induction over adversaries** — EasyUC
in print: "there's no way to do a structural induction over modules in
EASYCRYPT"; for us adversaries are values. (3) **Dependent oracle
interfaces natively** — CryptHOL's authors in print: in Lean "dependent
types would simplify the formalization of interfaces"; their `ℐ`+`WT`
typing discipline is a bolt-on we don't need. (4) **Unbounded/reactive
interaction** — SSProve terminates by construction and EasyUC's
functionality/adversary ping-pong broke termination-sensitive lemmas; our
coinductive layer handles both semantically. (5) **One substrate, two
readings** — the same polynomial classifies programs (`FreeM`) and
machines (`DynSystem`), so composition combinators are one-liners where
CryptHOL needed the `inline1`/`inline_aux` sum-type hack and 40-line
bespoke coinductions.

**The honest column** (goes in every paper): EasyCrypt's SMT-backed pRHL
and a decade of scheme libraries keep their proofs short — our
bisimulation/decoration lemma base must reach comparable ergonomics before
line counts flip; intrinsic time cost is a postulated model everywhere,
including here (only query counts are theorem-grade); CryptHOL's
third-party users avoiding the GPV layer is a standing adoption warning
for our machine layer; and Table 4 of our own paper already concedes the
current line-count deficit.

## Is the abstraction paying rent? (standing honest assessment)

The question to keep asking: *does the polynomial-functor framing change
outcomes, or does it re-describe things we could do without it?* Current
honest reading of the evidence:

**Where it demonstrably pays now.**
- *Dependent interfaces + lens calculus*: `OracleSpec`'s per-query answer
  types are genuinely dependent; the cartesian-lens condition giving
  probability preservation (paper Thm 5.1) is a crisp dividend of the
  positions/directions decomposition that FCF/CryptHOL handle ad hoc.
- *One substrate, two readings*: the same `p` classifies programs
  (`FreeM p`) and machines (`DynSystem p`), so the branch got
  `reduce/pair/juxtapose` as literal `wrap/pairing/tensor` one-liners
  instead of a bespoke combinator layer (CryptHOL needed dedicated
  `inline`/`exec_gpv` machinery for the analogous glue).
- *No-axiom rewinding*: the syntax-tree representation is what made
  transcript-replay forking work without rewindability axioms — an outcome
  difference vs. EasyCrypt, not a re-description.

**Where it is honestly just vocabulary (so far).**
- `OracleComp = FreeM` is standard algebraic effects; FCF had free-monad
  oracles with zero category theory. The Poly language adds nothing to that
  layer beyond a dictionary (which has expository value, not proof value).
- Line counts (paper Table 4) are currently *worse* than EasyCrypt's for
  overlapping material — the foundational+AI-verbosity price is real and
  should be stated, not hidden.

**Open bets (each phase carries a falsifiable pays-rent test).**
- Phase A bet: after A6/A7, the VCVio-side `IsPolyTime.bind` +
  `TwoPhaseGame` swap should *delete* more downstream lines than the new
  PolyFun generic layer adds, and the duoidal/coherence lemma inventory
  should be consumed (not decorative). If two-phase composition ends up
  hand-rolled anyway, the ◁ framing failed this test.
- Phase B bet: the generic `Run_n`/limit skeleton must make `RunLimit`
  strictly thinner and reusable for at least one non-probabilistic instance
  (e.g. `Option`/fuel), else it is over-engineering. **Verdict (2026-07-10,
  partial):** the reusability half is met — `runWith`/`runWith_output_some`
  instantiate to a deterministic `Option`/fuel run (`RunNExamples.lean`), so the
  ladder is genuinely monad-parametric, not SPMF-bespoke. The `RunLimit`-thinning
  half awaits the downstream VCVio swap (we do not edit VCVio).
- Phase C bet: `mate = M.corec` must actually discharge the ITree reverse
  bridge or machine-semantics uniqueness proofs; a cofree comonoid nobody
  calls is a museum piece.
- Phase D is *research*, not engineering; it is justified by understanding
  (and paper 3's UC story), and should be labeled so.
- G0 evidence that the bets are live: the CryptHOL authors *manually*
  rebuilt the coalgebra/behavior split ([CSF19]) and reported the
  state-hidden equations "much more concise" — i.e. the market already
  paid for Phase B's architecture once, by hand; and the §7.3.3 quadruple
  gives Phase B–C a semantic target (coalgebra/opfibration/copresheaf)
  no neighbor system can even state.

**Standing rules.** New abstract layers land only with a named consumer;
every phase review appends a verdict here (paid / mixed / didn't); line-count
and axiom-count comparisons go in papers verbatim, favorable or not.

## Session log

- 2026-07-09: R0 + R1 complete (`overview.md`, `spivak-niu-ch5.md`);
  corrections ledger seeded; roadmap created. Next: G0 survey, then R2 with
  Phase A tickets A1–A5 ready to start.
- 2026-07-10: R2 complete (`spivak-niu-ch6.md`); tickets A6–A9 pinned to
  book numbers, A7 split (compNthMap / transition lens δ / Machine.lean),
  A10 added; corrected the false "`speedup` exists in `Dynamical/`" claim.
  G0 survey re-launched (four agents; first run died on a session limit).
- 2026-07-10 (cont.): R3 complete (`spivak-niu-ch7.md`); B1–B5 sharpened
  (comonoid = data not property; Run_n conventions; §7.3.3 quadruple;
  constant-complement theorem for vwb; A3 → B5 dependency discovered).
- 2026-07-10 (cont.): G0 complete (`coalgebra-related-work.md`: CryptHOL,
  CertiCrypt/EasyCrypt, SSProve/ITrees, Poly-landscape + novelty table +
  ten Phase B design directives); differentiation section added above;
  corrections ledger grew items 7 (CUP not MIT Press) and the no-Tau
  watch entry. Remaining reading: R4 (Ch 8), R5 (Ch 9).
- 2026-07-10 (cont.): R4 complete (`spivak-niu-ch8.md`) and R5 done as an
  informed refresh of D5. C1–C4 pinned (M p = tree_p via Ex 8.16;
  workhorse spec (8.32); Prop 8.49 mate-packages-Run_n; C4's honest
  statement identified). D1–D4 pinned to Thm 8.102 legs with their
  Phase A ingredient list; Cat♯ factorization filed with B4.
  **Reading program R0–R5 + G0 is complete.** Next milestone: Phase A
  formalization (A1–A10), starting with A1 (ihom/eval/curry) and
  A7b (transition lens δ) as the highest-leverage openers.
- 2026-07-10 (cont.): **Phase A milestone 1 landed** — A1, A3 (core), A6,
  A7a/b/c implemented (five new modules under `PFunctor/`, four `PolyFunTest/`
  example files). Full `lake build` + `lake lint` + `lake test` green, no
  `sorry`. `vcv-connection.md` cleaned into a per-construct payoff ledger.
  Reuse wins: `Lens.fixState` already *was* δ and `Lens.speedup` the lens-level
  two-step, so A7b was a lift. Deferrals recorded above (A3 intersection-iso +
  preservation suite; A7c fuel-exact bind law + `IsSimulation`). Pays-rent
  verdict deferred until the downstream VCVio swap is attempted (the falsifiable
  test: does `seqComp`/`eval` delete more branch lines than PolyFun added?).
  Next: A3 follow-on (or A2/A4 adjunction/closure lemmas), then Phase B.
- 2026-07-10 (cont.): **Phase A milestone 2 landed** — A2, A4,
  A8·(6.65), A9, A10, and the A1/A3 deferrals, implemented by five parallel
  subagents into four new modules (`CartesianClosed`, `Adjunctions`,
  `Lens/Duoidal`, `Lens/Distributivity`) plus extensions to `InternalHom` and
  `Lens/Factorization`. Full `lake build` + `lake lint` + `lake test` green,
  no `sorry`. Agents caught two math errors in the plan (see `corrections.md`:
  `ihomSum` → `*` not `⊗`; catalogue `By⊗p≅By◃p` needs `linear B` not `C B`)
  and reused pre-existing repo lemmas (`sumCompDistrib`, `sigmaCompDistrib`,
  object-level `prodCompDistrib`, `PFunctor.Equiv.toLensEquiv`) instead of
  duplicating. Open Phase A remnants (A5, A8 coclosure/multiadjoint,
  (co)limits, 6.87 coherence, 6.51) are non-blocking follow-ons.
  **Phase A is substantially complete.** Next: Phase B (comonoids, `Run_n`).
- 2026-07-10 (cont.): **Phase B spine landed** — B1 (`Comonoid`), B2 (state
  comonoid `Sy^S` + `δ^(n)` + `IsStateSystem`), B3 (`nStep`/`Run_n` +
  monad-parametric `runWith` + fuel irrelevance), and the finished `Machine`
  deferrals (`toComp_seqComp_inl` operational law, generic `IsSimulation`),
  scoped by three read-only surveys to the live K-L blocker cluster (VCVio
  `RunLimit`/`IsPolyTime.bind`). Three new modules (`PFunctor/Comonoid.lean`,
  `Dynamical/{RunN,Simulation}.lean`) + a `Machine.lean` extension + three
  `PolyFunTest/` files. Full `lake build` + `lake lint` + `lake test` green with
  `--wfail`, no `sorry`. Canaries all `rfl`: the state-comonoid laws,
  `twoStep_toLens_eq` (`n = 2` coherence), and `runWith = mapM ∘ toComp`.
  Finding: the naive fuel-additive `seqComp` bind law is **false** (fuel threads
  continuously through the handoff), so the operational two-lemma
  characterization is shipped instead, with the fuel-exact form (via reachability
  + `runWith_output_some`) noted as the next increment. Pays-rent (partial):
  the `Option`/fuel `runWith` instance discharges the reusability half of the
  Phase B bet. Next: Phase C (cofree comonoid `t_p` + mate = `M.corec`) or the
  Cluster-3 interface-rebasing bridge (SemanticSecurity sorries).
