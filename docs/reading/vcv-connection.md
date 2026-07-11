# Spivak–Niu → VCVio: what each construction buys

Construction-by-construction ledger of what each *Poly* (Spivak–Niu) result,
once formalized in PolyFun, concretely purchases in VCVio. This is the "why"
companion to the tickets in [`roadmap.md`](roadmap.md); the chapter notes
(`spivak-niu-ch5.md` … `-ch8.md`) hold the mathematics, and
[`coalgebra-related-work.md`](coalgebra-related-work.md) holds the honest column
(where the abstraction is only vocabulary, and where line counts still lose).

VCVio references are to branch `dtumad/k-l-examples` (read-only input; we do not
edit it). Each entry ends with an explicit **Payoff** naming the downstream
construct and its `file:line`.

The load-bearing honesty note up front: **PolyFun supplies structural /
categorical content only.** Anything that is genuinely about probability
(SPMF/ωCPO) or Turing-machine running time stays in VCVio. Two consequences
recur below — `IsPolyTime.bind` splits into a structural half (ours) and a
TM-time half (a documented VCVio `sorry`), and `RunLimit` is a Phase B item
(`Run_n`), not Phase A.

## Phase A — kills a specific hand-rolled construction

### ⊗-internal hom `[q,r]` + eval/curry (Ex 4.78, Prop 4.85 → A1)

The hom object's positions are the lenses `q ⇆ r`; `eval : [q,r] ⊗ q ⇆ r` is
the universal "consult a responder" wiring, and `curry`/`uncurry` package a
challenger as a single position of `[q,r]`. `[p,y] ≅ Γ(p)·y^{p(1)}` further says
handlers (`OracleHandler = PFunctor.Section`) are literally the *points* of a hom
object, so handler-transport lemmas come from currying rather than case analysis.

**Payoff:** `WireK.wireKStep` (`OracleComp/Coinductive/WireK.lean:131`) —
self-described in its own docstring as the hand-kept `eval : [p,y]⊗p → y` wiring
— and the UC layer's `processSemanticsOracle` (`Interaction/UC/Runtime.lean:224`)
become the *same* wiring along `eval`, with the SPMF-Kleisli lift as the only
VCVio-side residue. The two are flagged in-source as un-unified siblings
(`WireK.lean:42-44`); A1 is their common parent.

**Status (2026-07-11): upstream half landed.** `Responder S q`
(`PFunctor/Dynamical/Responder.lean`, systems over `q ⊸ X` with the
Kleisli–Mealy `equivStateHandler` bridge), the game formers
`DynSystem.game` / `closedGame` (`PFunctor/Dynamical/Game.lean`, wiring
along `eval`, with `game_eq_uncurry` the adjunction reading), the monadic
runs `kleisliStep` / `kleisliIterate` / `stepWith` / `iterWith`, and the
machine-vs-responder step law
`PointedMachine.runWith_run_succ_of_output_eq_none` are all in place, plus
the two-phase `Lens.eval₂` / `orderPair` / `game₂` (Eq 6.86 + Ex 6.85).
Remaining VCVio-side residue: the `m := SPMF` instance (ProbResponder as
the bundled Kleisli sibling) and `QueryLog` transcripts.

### Vertical–cartesian factorization (Prop 5.51–5.63 → A3)

Sub-spec inclusions in VCVio are cartesian lenses, and the paper's Thm 5.1
(probability preservation under sub-specs) is "cartesian lenses have pullback
naturality squares." A3 makes that a corollary and gives every spec morphism a
normal form: relabel queries (vertical), then restrict answers (cartesian).

**Payoff:** the `LawfulSubSpec` theory (`OracleComp/Coercions/SubSpec.lean`, the
consumer already named in `PFunctor/Lens/Cartesian.lean:37-42`) gets its
factorization; and — the payoff discovered while reading — three separate
Ch 7–8 theorems consume this factorization, so A3 is also the entry fee for the
machine-semantics results paper 3 needs.

### Destructor triple for `p ⇆ q ◃ r` (Example 6.40 → A6)

A lens into a composite *is* a triple `(φ^q, φ^r, φ♯)`: position policy,
mid-phase policy, joint answer map. This is the intro/elim rule for two-phase
games.

**Payoff:** `TwoPhaseGame` (`CryptoFoundations/Asymptotics/TwoPhaseGame.lean:58`,
commit-then-guess / CPA-CCA shape) stops unfolding `comp` by hand — it becomes
three typed functions plus an `ext` lemma.

### Sequential machine composition (Example 6.41 → A6 + A7)

Binding two machines that share an interface is a machine over `q ◃ r` with a
shared mid-boundary — the "cascading menus" example — realized as a state
machine with `M₁.State ⊕ M₂.State` that runs phase 1 to its output, then hands
off to phase 2. The transition lens δ (A7b, already present as `Lens.fixState`)
gives multi-step execution a canonical primitive.

**Payoff:** PolyFun now supplies the generic `PointedMachine.seqComp`, its
query-resolution certificate algebra, and the fuel-exact `runWith_seqComp_init`
bind law. VCVio specializes this to `OracleMachine.seqComp` and reuses the law
in `IsPolyTime.bind`, with `M₁.State ⊕ M₂.State` encoded by the already
scaffolded `finEncodingSum`. The sum stores only phase-local machine control;
a stateful handler monad threads one shared random-oracle cache or transcript
through both phases. **Honest split:** this is the *structural* and
semantic half of `IsPolyTime.bind`. The *remaining* half is a
TM running-time bound — the documented `sorry` in
`ToMathlib/Computability/PolyTimeTM.lean:537-552`
(`sumElim` / `time_sumElim_eval_le`, a length-changing streaming transducer).
That is computability content PolyFun neither has nor should own.

## Phase B — replaces families of per-instance lemmas with one universal property

### Comonoids = generalized state systems (Def 7.14, Ex 7.22 → B1/B2)

A comonoid is a protocol-state *category* where not every state is reachable from
every other — session structure, i.e. an oracle whose available transitions
depend on phase. VCVio's stateful wrappers (logging, query counting) become
comonoid-respecting decorations, with the ε/δ laws as their contract instead of
per-wrapper lemmas.

### `Run_n` + canonicity (Prop 7.20 → B3)

`runK` is the probabilistic shadow of `Run_n`, `runLimit` the shadow of the
limit. PolyFun keeps the monotone-truncation/ω-limit theory generic; VCVio keeps
only the SPMF-ωCPO instance. Canonicity (7.20d — every way of associating `n`
runs agrees) is the lemma that deletes bookkeeping from round-by-round hybrids.

**Payoff:** `RunLimit` (`OracleComp/Coinductive/RunLimit.lean:165`,
`runKT`/`runChain`/`runLimit = ωSup`) becomes the SPMF instance of a generic
skeleton (and the skeleton must earn its keep on ≥1 non-probabilistic instance,
e.g. `Option`/fuel, or it is over-engineering).

### Retrofunctors + the §7.3.3 quadruple (Def 7.55 → B4/B5)

Four interchangeable faces of "an implementation of an interface": the coalgebra
(what you run), the discrete opfibration (the reachable-state graph you state
invariants on), the copresheaf (implementation indexed by protocol state — what
a UC functionality is), and the retrofunctor (the simulation map).

**Payoff:** VCVio's `Implements`/`IsSimulation`
(`OracleComp/Coinductive/Machine.lean:241,299`) get a canonical home, and the
vwb-lens specialization ties lawful state accessors to the same theory.

## Phase C — behavior semantics with the quotient for free

### Cofree comonoid + mate (Thm 8.45, Prop 8.49 → C1–C3)

Prop 8.49: the mate of a machine packages *every* `Run_n` into one morphism —
the theorem that justifies `RunLimit` being a single object. Two machines are
equivalent iff their mates (behaviors) are equal, and because the carrier is
Mathlib `M p`, that equality is honest `Eq` — the CryptHOL Constructive-
Cryptography lesson ("state-hidden equations are much more concise") with the
quotient free instead of hand-built. Example 8.51: the mate of a DFA is its
accepted language — in VCVio terms, the behavior of an oracle machine is the
transcript tree it accepts, a canonical semantics for `Emulates`-style
statements. Also the clean reverse `OracleComp.toITree` bridge via finality.

**Payoff:** machine-behavior semantics for `Emulates`; `DynSystem.behavior`
(`PFunctor/Dynamical/Trajectory.lean:85`) recast as the mate.

### C4 — honest adjunction bookkeeping

Replaces the over-claimed `FreeM ⊣ Cofree` citation with the true theorems
(`U ⊣ 𝒯_₋`, Thm 8.45; the free/cofree relationship is Libkind–Spivak's module
structure), so paper 2 states the "programs run on behaviors" pairing as
something we actually proved. Resolves `corrections.md` item 1
(`Interaction/Basic/Spec.lean:83`, `REFERENCES.md:65`).

## Phase D — the UC bet (payoff is a paper, not deleted lines)

### Bicomodules + prafunctors (Thm 8.102, §8.3.5 → D1–D3)

Environments and hybrids are bicomodules between protocol categories, and
composing a hybrid functionality with a simulator is bicomodule composition. If
it lands, hybrid-world reductions become *associativity of a composition
operation* rather than manual message routing — the thing EasyUC spent ~18,000
lines on. D4 folds `IPFunctor` (session-indexed specs) in as bicomodules over
discrete comonoids. The topos `[𝒯_p, Set]` track is the long-shot: machine
behaviors are its objects, so its internal logic is a specification language
conjecturally containing Loom's `wp`/`Triple`.

**Payoff:** paper 3 (categorical UC, the ePrint 2026/899 §10 promise).

---

The pattern across all of these: Phase A items each kill a specific hand-rolled
construction on the current branch; Phase B–C items replace families of
per-instance lemmas with one universal property; Phase D is research whose
payoff is a paper, not deleted lines. `roadmap.md` labels each with its
falsifiable pays-rent test.
