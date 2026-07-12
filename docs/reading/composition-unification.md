# Composition unification: the two `⨟` axes and the bicomodule endgame

Design memo for a prospective "bigger refactor" that unifies PolyFun's several
"run A then/beside B" composition operators. Investigation only — no refactor is
performed here. Companions: `roadmap.md` (Phase B–D tickets this deep-dives on the
composition thread), `overview.md` (Ch 6–8 sketch), `vcv-connection.md` (downstream
payoffs). Book: Spivak–Niu, *Polynomial Functors: A General Theory of Interaction*
(Cambridge University Press, LMS Lecture Note Series 498, 2025).

## The seam

The library spells `⨟` for two mathematically-different operations, and there are
in fact **three** disjoint "then/beside" substrates plus a fourth interface-composite
family. Only two composition primitives are genuinely bespoke (`choiceProd`,
`seqComp`); everything else is one of these dressed up.

- **(L) interface axis — lens `⨟`.** `Lens.comp` (`PFunctor/Lens/Basic.lean:53`,
  notation `:64`) and `Chart.comp` (`PFunctor/Chart/Basic.lean:86`) are **already**
  Mathlib `Category` instances on `PFunctor` (`PFunctor/Category.lean:27,36`) with
  associativity and unit laws all `rfl`. The monoidal/duoidal siblings `⊗ₗ`, `◃ₗ`,
  `⟨·,·⟩ₗ` and every `Dynamical/Combinators.lean` wrapper (`wrap`/`tensor`/`pairing`/
  `wire₂`, and the `Dynamical/Game.lean` wiring) are lens one-liners on this axis.
- **(A) program axis, syntactic — `FreeM.append`** (`PFunctor/Free/Path.lean:257`):
  the dependent tree-graft under *all* `Interaction/Basic` + `TwoParty` sequential
  composition (`append`/`replicate`/`stateChain`/`Chain`/`Telescope`, proven
  mutually derivable, `Interaction/Basic/Chain.lean:28-38`).
- **(M) program axis, machine — `PointedMachine.seqComp` (`⨟`)**
  (`PFunctor/Dynamical/PointedMachine.lean:102`, notation `:122`): the `⊕`-state
  two-phase machine of Example 6.41.
- **(◃) interface-composite family** — `CompTriple`/`toCompTriple`
  (`PFunctor/Lens/Composite.lean:53,60`, Example 6.40), the duoidal `orderingLens`/
  `duoidalLens` (`Lens/Duoidal.lean`), and `nStep`/`comultN` (`RunN.lean`,
  `Comonoid.lean`): lenses into, and static multi-step behaviour over, `◃`-composites.

## The naive merge fails

`seqComp` is **not** a lens, and **not** a `◃`-composite. Four concrete mismatches
(this corrects an earlier roadmap note that suggested a `CompTriple` re-expression):

1. **Arrow shape.** `ofCompTriple` produces a lens whose *codomain* is a composite
   `q ◃ r`. `seqComp`'s underlying lens is `selfMonomial(S₁⊕S₂) ⇆ p` — codomain the
   *plain* shared interface `p`; any composite would be on the *domain* (state) side.
2. **`⊕` vs `Σ`.** `seqComp.State = M₁.State ⊕ M₂.State` (a coproduct — "which
   phase"). A `◃`-composite's directions are `Σ u : q.B a, r.B (f u)` (a dependent
   pair — *both* phases fire). `selfMonomial(S₁⊕S₂) ≠ selfMonomial S₁ ◃ selfMonomial S₂`.
3. **Dynamic boundary.** The phase-1→phase-2 switch fires when `M₁.output` *becomes*
   `some m` — after an a-priori-unbounded number of steps, which is why the file needs
   *fuel* (`toComp`, `ResolvesIn`). A `◃`-composite has a static arity and no fuel.
4. **Invisible handoff.** The switch `M₁.output s = some m ↦ M₂.init m` lives in the
   *pointed* fields `init`/`output`/`Option` that the lens/`◃` layer cannot see.

## The two-axis diagnosis

The merge fails because `seqComp` and lens `⨟` compose along **orthogonal axes**:

- **Interface axis** (L, ◃): morphisms *between polynomials* — Poly is a `Category`,
  with the monoidal/duoidal `⊗`/`◃` structure layered on. This axis is *done*.
- **Program axis** (A, M): composition of *programs over a fixed interface `p`*.
  Here **(A) and (M) are the same operation.** `toComp` unrolls a machine to a
  free-monad program `FreeM p (Option β)` (`PointedMachine.lean:150`), and
  `runWith = mapM ∘ toComp`. `FreeM p` is a `LawfulMonad`, so its Kleisli
  composition is strictly associative. `append` is the *syntax* presentation
  (grafting `FreeM` trees); `seqComp` is the *machine* presentation (`⊕`-state);
  they are bridged by `toComp` / `behavior` (`M.corec`).

The two axes are joined by two families of maps already in the library:

- **`mapM` / handlers** move a program across interfaces (interpret `FreeM p` in a
  monad `m`, or along a monad morphism) — the just-landed **B6** naturality
  (`FreeM.mapMHom_unique`, `mapM_natural`, `Free/Basic.lean`).
- **the mate `behavior` = `M.corec`** moves a machine to its behaviour tree in `M p`
  (`Dynamical/Trajectory.lean:85`), with `behavior_unique` the finality universal
  property.

## Spike findings (de-risking prototypes)

Two throwaway spikes (branch `dtumad/spike-composition`,
`PolyFunTest/Spikes/Composition{ProgramAxis,Bicomodule}.lean`) tested the load-bearing
claims. Both compile.

- **Program axis (Spike 1).** The machine's fuelled program `prog M h k := fun x =>
  M.runWith h k (M.init x) : α → m (Option β)` is a Kleisli arrow in `OptionT m`, and
  `prog (M₁ ⨟ M₂) = optBind (prog M₁) (prog M₂)` is a *restatement of the existing*
  `runWith_seqComp_init` (`PointedMachine.lean:409`). `optBind_assoc` (from
  `LawfulMonad m`) supplies associativity. **Verdict: (A)≡(M) is real and cheap** —
  it reuses one existing lemma + the monad laws, no new coherence debt. The
  `⊕`-state non-associativity of `seqComp` is an artefact of the machine
  presentation; the underlying program associates by `LawfulMonad (OptionT (FreeM p))`.
- **Bicomodule path (Spike 2).** A retrofunctor `Retro C D` (comonoid morphism,
  Def 7.55) composes with all three `Cat♯` category laws `rfl`. A `LeftComod C`
  (Def 8.83) with coassociativity stated *through* the `◃`-associator
  `compAssoc.toLens` typechecks; the `stateComonoid` self-comodule discharges it by
  **`rfl`** (diagonal collapse), while a generic comonoid needs the honest `coassoc`
  field. No `cast`/`HEq` was needed at this depth. **Verdict:** the entry (B4
  retrofunctors) is cheap and the *state/machine* instances stay in the `rfl` regime;
  the coherence cost concentrates at *generic* (non-diagonal / cofree) bicomodule
  composition — exactly where the `◃`-associator stops being `rfl`.

## The maximal target: the bicomodule double category

The framework that unifies *both* axes under one composition is the double category
of comonoids and bicomodules (`Cat♯` / `Mod`, Ch 8.3). Comonoids are objects,
retrofunctors are the vertical morphisms, `(𝒞,𝒟)`-bicomodules are the horizontal
1-cells, and **bicomodule composition `⊳` is the single general `⨟`** (§8.3.5,
"dynamics as bicomodule composition; running = composing the bicomodule"). Every
existing substrate is a bicomodule instance:

| Existing operator | Bicomodule reading |
|---|---|
| lens `⨟` (L) | composition in `yMod_y` (`Poly ≅ yMod_y`, Ex 8.101) — the trivial-boundary case |
| `DynSystem` | a `p`-coalgebra = a `(Sy^S, 𝒯_p)`-bicomodule (Thm 8.102 / §8.1.4) |
| `seqComp` / `append` (M, A) | composition along a *data-boundary* comonoid (the I/O types), = Kleisli of `FreeM p` |
| UC `par` / `wire` / `plug` | one bicomodule composition parameterized by a wiring boundary (see below) |
| `nStep` / `Run_n` (◃) | the mate packaging every finite run (Prop 8.49) |

The picture: parallel composition is `⊗`, sequential-interface composition is `◃`,
sequential-program composition is Kleisli/`append`, and interpretation across
interfaces is `mapM` — all instances of, or 2-cells in, the bicomodule double
category, with the duoidal interchange (`Lens/Duoidal.lean`) the shadow of the
double category's interchange law. This is the "much more flexible" structure: n-ary
and dependent interleave, partial plugs, cross-substrate composition (drive a
`FreeM.append` protocol by a `seqComp` machine), and same-step-adaptive two-phase
games all become one operation parameterized by a boundary/wiring.

## Critical path (aligned to roadmap B4 → C → D1 → D3)

Everything below the `(◃)`/mate line is **greenfield** (confirmed absent by grep):
no `Comonoid.Hom`, no `MPath`, no cofree comonoid `t_p`, no mate `U ⊣ 𝒯`, no
comodule/bicomodule. Raw material present: `M p`/`M.corec`/`behavior`, the
*inductive* `FreeM.Path`, `stateComonoid`, `homMonomialEquiv` (6.65), and the ⊗-side
`curryEquiv` (a clean `Equiv`).

| Step | Builds | Subsumes / pays rent | Risk |
|---|---|---|---|
| **B4** retrofunctors + `Cat♯` | `Comonoid.Hom`, composition, isos | the "implementation morphism" vocabulary; `IsSimulation` gets a categorical home | low — spike shows all `rfl` |
| **C1–C2** `MPath` + cofree comonoid `t_p` | coinductive paths on `M p`; `t_p = ⟨M p, MPath p⟩` | recasts `behavior`/`trajectory` as universal maps | medium — coinductive-over-inductive family |
| **C3** mate `U ⊣ 𝒯`, Prop 8.49 | `mate = M.corec`; packages every `Run_n` | `DynSystem.behavior` as the mate; the ITree reverse bridge | medium |
| **D1** comodules / bicomodules | `LeftComod`/`Bicomodule` + coactions | `DynSystem` = bicomodule; the boundary algebra | **high — the `◃`-associator coherence** |
| **D3** bicomodule composition `⊳` | the unified `⨟` | UC `par`/`wire`/`plug`, `append`-family, `seqComp`, `choiceProd` all collapse to one op | **high — "running = composing" coherence** |

## Feasibility risks (measured)

1. **Diagonal universe pinning** — `Comonoid.carrier : PFunctor.{u,u}` (`Comonoid.lean:54`),
   the sub-universe closed under `◃`. A bicomodule layer inherits it. *Spike verdict:*
   no obstacle at the comonoid/retrofunctor/comodule layer; mixing genuinely different
   interface universes would need `PFunctor.ulift`, deferrable.
2. **`◃`-associativity only up to `Equiv`** — the associator is `Equiv.compAssoc`
   (`Equiv/Basic.lean:607`), a real sigma-reassociation, never `rfl`; `Comonoid.coassoc`
   is stated through it. *Spike verdict:* the statement typechecks; the `stateComonoid`
   diagonal case collapses to `rfl`, but generic comodule/bicomodule composition owes
   honest coherence — this is the single biggest cost, concentrated at D1/D3.
3. **`HEq`/`cast` in coaction laws** — routing coassoc through `compAssoc.toLens`
   invites the dependent-cast bookkeeping that stalled the cartesian `curryEquiv`
   (`CartesianClosed.lean:47-52`) and that `gotchas.md:135` bans from core defs.
   *Spike verdict:* not hit through D1's *statements* and the state instances; expected
   only where a composite `m ⊳ n` must *build* a new coaction over non-diagonal / cofree
   carriers (C2/D3). Mitigation: keep composites diagonal where possible; when not,
   push transports through named `Equiv`s (never raw `cast`) and grow `Logic/HEq.lean`.

## Falsifiable pays-rent tests (most concrete first)

- **UC `par`/`wire`/`plug` collapse to one wiring-parameterized composition.** They
  are *already* one `OpenProcess.interleave` call with three `ContextHom` pairs
  (`UC/OpenProcessModel.lean:76/82/88`), and `plug_eq_wire`/`Raw.plug`/`Raw.unit`
  already prove plug/unit are wire. A single `compose(wiring)` deletes three
  primitives *and* the three `IsLawful{Par,Wire,Plug}` classes (`OpenTheory.lean:232/258/289`).
  Strongest immediate target; does not even need full bicomodules.
- **`append`-family + `seqComp` unify on one former.** `Chain`/`Telescope` already
  carry the same datum — a `DynSystem σ Spec.stepPoly` coalgebra (`Telescope.lean:54`,
  `Chain.lean:81`) — and all reduce to `FreeM.append`; connecting substrate (A) to (M)
  via `toComp`/behaviour makes them instances of the program-axis composition.
- **`choiceProd` becomes an instance** (`Combinators.lean:130`, the sole bespoke
  dynamical combinator), so the whole Concurrent/UC interleave stack
  (`interleave_eq_wrap_choiceProd`) inherits the general operation.
- **Newly enabled:** same-step-adaptive two-phase games (`orderPair`'s documented
  limitation, `Game.lean:248`), n-ary/dependent interleave, partial plugs, and
  cross-substrate composition.

## Staged refactor proposal

Build toward the unified bicomodule `⨟` in dependency order, front-loading the cheap
high-value pieces the spike validated, and isolating the coherence work to the end:

1. **First increment (recommended): B4 retrofunctors + `Cat♯`.** Promote Spike 2's
   `Retro` to `PFunctor/Comonoid.lean` (or a new `Cat♯.lean`), with the state/monoid
   examples; give `DynSystem.IsSimulation`/`Implements` their categorical home. One PR,
   all `rfl`, a clean pays-rent story (the §7.3.3 "implementation morphism" vocabulary).
2. **Program-axis unification.** Land Spike 1's `prog`/Kleisli reading as real API
   (`PointedMachine`-as-`OptionT (FreeM p)`-Kleisli-arrow), then show the
   `Interaction/Basic` `append`-family are the same composition — resolving roadmap
   long-term item 2 (the `Interaction/Basic` ↔ `DynSystem` layering) as a byproduct.
3. **C1–C3** cofree comonoid + mate (recasts `behavior` as the universal map).
4. **D1 comodules** (diagonal-first, to stay in the `rfl` regime), then **D3
   bicomodule composition `⊳`** — the unified `⨟`. Discharge the pays-rent test:
   UC `par`/`wire`/`plug` collapse; `choiceProd` becomes an instance.

Each step lands with its pays-rent test recorded per the roadmap's standing rule
("new abstract layers land only with a named consumer"). The honest cost, stated up
front: D1/D3 carry genuine `◃`-associator coherence that the state instances hide;
the refactor is justified only if the collapse of UC's three-primitive / three-class
wiring algebra (and the `append`/`seqComp` unification) deletes more than the generic
bicomodule layer adds.
