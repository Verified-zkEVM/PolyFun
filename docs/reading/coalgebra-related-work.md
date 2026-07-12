# Coalgebras in neighboring provers — grounding survey (unit G0)

How CryptHOL, CertiCrypt/EasyCrypt, SSProve, and the interaction-trees
tradition handle the coinductive/coalgebraic side that PolyFun Phase B is
about to freeze APIs for. Web-sourced 2026-07-10 by four research agents;
citations were verified against author PDFs / AFP sources unless marked
[unverified]. Feeds: Phase B API design, `roadmap.md` differentiation
section, paper 2 related work.

## 1. CryptHOL (Isabelle/HOL) — the closest cousin

Sources: Lochbihler ESOP 2016; Basin–Lochbihler–Sefidgar, J. Cryptology 33
(2020) [JC20]; Lochbihler–Sefidgar–Basin–Maurer, CSF 2019 [CSF19]; AFP
entries `CryptHOL`, `Constructive_Cryptography`(-`_CM`), `Game_Based_Crypto`,
`Sigma_Commit_Crypto`. AFP theory/line references from the mirror as of
2026-07-10.

### 1.1 GPVs are our substrate, minus the polynomial language

```isabelle
codatatype ('a, 'out, 'in) gpv
  = GPV (the_gpv: "('a, 'out, 'in ⇒ ('a,'out,'in) gpv) generat spmf")
datatype ('a,'b,'c) generat = Pure 'a | IO 'b 'c
```

`generat` *is* the polynomial `A·y⁰ + Out·y^In`; `gpv` is the M-type of
`spmf ∘ generat` — a coinductive resumption monad over discrete
subprobabilities. CryptHOL never says "polynomial functor"; Isabelle's BNF
machinery does the work. Responses are **non-dependent** (`'in` fixed), so a
separate typing discipline (`ℐ` interfaces = "query ↦ set of valid
responses", a container in disguise; coinductive `WT_gpv`) is bolted on to
recover per-query response types. The CryptHOL authors say it themselves
([CSF19] §I-B, verbatim): *"we could have carried out our formalization in
other proof assistants like Coq or Lean, where constructing the codatatypes
probably would require more effort, but dependent types would simplify the
formalization of interfaces."* That sentence is simultaneously PolyFun's
value proposition (dependent directions native, no `ℐ` bolt-on) and its risk
(M-type infrastructure effort) — quote it in paper 2.

They chose gfp semantics for the *program* type itself (to include
probabilistically-terminating adversaries); the inductive fragment is
recovered as a predicate. PolyFun/VCVio's split — inductive `FreeM` programs,
coinductive M-type behaviors — is strictly finer.

### 1.2 Composition operators and their laws (the API contract to mirror)

- `exec_gpv : gpv ⇒ 's ⇒ ('a × 's) spmf` — run against a stateful oracle
  (`callee`). Defined as `partial_function (spmf)`: a **least fixpoint in
  the spmf ccpo**, not a corecursion; missing mass = divergence.
- `inline` — substitute a GPV-valued interceptor; the result is again a GPV.
  Defined as "coiteration of a least-fixpoint search operator": `inline1`
  (lfp: search for the next outer query) + `inline_aux` (primcorec), with a
  sum-type hack because *"primcorec does not support"* bind-before-corecurse
  (GPV.thy:3784 comment).
- Law set (AFP names): `exec_gpv_bind`, `inline_bind_gpv`, `inline_assoc`
  (associativity **only up to `map_gpv` state-tuple reassociation**, proven
  by a bespoke ~40-line coinduction `gpv_coinduct_bind`), `exec_gpv_inline`
  (run ∘ substitute = run against composed oracle). [JC20] §5.4 presents the
  last two as the framework's thesis: composition captured "in two simple
  equations".
- Oracle combinators: `⊕ₒ` (shared-state dispatch), `‡ₒ` (disjoint product),
  state extension, with typing/invariant decomposition lemmas along each.

PolyFun mapping: `exec_gpv` ≙ run `FreeM` against a coalgebra; `inline` ≙
handler substitution into `StateT`. Target exactly this lemma set. Two
structural wins to claim: (a) inductive `FreeM` makes substitution plain
structural recursion — the `inline1`/`inline_aux` hack disappears; (b) lens-
level state hiding makes associativity/interchange *strict*, killing the
`map_gpv` reassociation noise (which [CSF19] itself complains about — see
1.5).

### 1.3 Bisimulation: parametricity first, coinduction once per operator

`GPV_Bisim.thy:11`: "Bisimulation is a consequence of parametricity." The
user-facing rule `exec_gpv_oracle_bisim'` — exhibit a state relation `X` +
per-query `rel_spmf` coupling ⟹ run equivalence — is a one-line corollary of
the parametricity lemma for `exec_gpv`. EasyCrypt's pRHL arrives as a
*derived theorem*, not a primitive logic. Up-to-bad (`exec_gpv_oracle_bisim_bad*`)
is **not** coalgebraic bisimulation-up-to: it is a bespoke joint-run coupling
(`exec_until_bad`) whose soundness *requires* losslessness + termination
([JC20]: "essential", not technical).

Lean has no transfer engine, so plan: one hard coinduction per combinator
(the relator-parametricity lemma), then derived one-shot rules forever.
`callee_invariant_on` (invariant + WT ⟹ preserved by whole runs, with
decomposition along `⊕ₒ`) is the structure to reproduce on coalgebras.

### 1.4 Termination/analysis predicate zoo (≙ VCVio's `RunLimit` cluster)

Four tiers, each with preservation lemmas through `bind`/`inline`/`exec`:
`WT_gpv` (gfp typing) / `lossless_gpv` (lfp: finite interaction, total
sampling) / `colossless_gpv` (gfp: no silent divergence) / `plossless_gpv`
(a.s. termination via a wp-expectation transformer, `expectation_gpv`).
VCVio: `ASTerminates` ≙ `plossless`, `ImplementsAE` ≙ pgen-lossless-style
equalities under exec. Key glue: `plossless_exec_gpv`, `plossless_inline`,
`WT_gpv_inline1`, `interaction_bounded_by_inline` — *an analysis predicate
is only useful once it commutes with bind, handle, and run.*

`interaction_bound` pattern worth copying verbatim: exact `enat`-valued sup
internally ("no nice equation for bind"), **inequality-only user API**
(`interaction_bounded_by`) with an attribute-driven rule set.

`RunLimit` lesson: CryptHOL has no standalone run-limit object — the ccpo
`partial_function` discipline *is* the scheme (`lub_spmf` of finite
unrollings). The load-bearing proof infrastructure, in priority order for
PolyFun's B3: (a) fixpoint induction with admissibility automation;
(b) strong fixpoint induction; (c) **parallel fixpoint induction relating
two fixpoint towers** (`parallel_fixp_induct_2_2` — the single most-used
trick, ≥8 uses, needed for every `inline1` fact); (d) monotone-suffices
(they deliberately avoid demanding ω-continuity in user obligations).
Philosophy quote for paper 2 ([JC20] fn. 13): intermediate games must *not*
be "artificially restricted, e.g., by termination or efficiency constraints".

### 1.5 Constructive Cryptography layer = our coalgebra/behavior split, built by hand

`codatatype resource = Resource ('a ⇒ ('b × resource) spmf)` — final
coalgebra of `X ↦ (α ⇒ D(β × X))`; `converter` = same with GPV instead of
spmf. `attach` (⊳) = corecursively iterated `exec_gpv`; `comp_converter`
(⊙) = corecursively iterated `inline`; `RES(δ,s₀)` = the anamorphism
("seals" the state — HOL cannot say `∃σ. …`). Laws: `attach_compose`,
`attach_parallel2` (interchange), wiring converters `lassocr/rassocl/swap`
with a composition calculus. Their own verdict ([CSF19] §IV-C, verbatim):
the coalgebraic-view equations are *"much more concise than the
corresponding equations in CryptHOL, where the internal state is not
hidden."* I.e., the CryptHOL authors rebuilt PolyFun's
coalgebra-plus-behavior architecture manually and reported it was the
cleaner algebra. PolyFun has both layers generically; advertise the
behavior-level operators as the API, anamorphism as the bridge.

Equivalence tiers: bisimilarity ⊋ **trace equivalence** ⊋ indistinguishability
(hidden-choice counterexample). Their trace theory needed a new functor
`G(Y) = α ⇒ (D(β) × (β ⇒ Y))` — determinize into distributions-over-states —
because naive pointwise trace equality is *wrong* for probabilistic systems
(conditioning doesn't distribute over mixtures). Design input for
`PFunctor/Trace`/`Behavior` and any VCVio observational equivalence: define
unwinding on **monad-weighted frontiers**, not states, or completeness
w.r.t. distinguishers fails. (Prop 8.68/Ch 8 bicomodule machinery may give
this a home; check in R4.)

### 1.6 Honest-assessment ammunition (verified quotes)

- Line counts ([JC20] §7.1 Table 1): CryptHOL beats CertiCrypt everywhere
  and splits with EasyCrypt (switching lemma 120 vs 448; Elgamal 49 vs 68;
  hashed Elgamal 253 vs 216). "In comparison to EasyCrypt … we achieve a
  similar degree of automation."
- Conceded limitation ([JC20] §8): *"Our framework cannot yet express
  efficiency notions such as polynomial runtime … This is the flipside of
  the shallow embedding."* — exactly the gap VCVio's TM-grounded PPT machine
  layer targets; cite when motivating paper 2.
- Third-party users **avoid the GPV layer**: Butler et al.'s MPC and
  Σ-protocol formalizations stay at plain `spmf` (zero `gpv` occurrences in
  `Sigma_Commit_Crypto`, verified by grep). The coinductive layer is
  framework-author territory. Lesson: the oracle/machine layer must be
  cheap for downstream users or they route around it.
- Losslessness side-condition tax: every CC composition lemma drags a
  four-condition packet (plossless converter, lossless resource, 2× WT).
  Design VCVio's analogues as one bundled structure inferred along
  combinators, not four hypotheses per lemma.
- Their success formula (copy it): technical semantic definitions once,
  high-level derived rules forever; semantic HOL equalities beat
  relational-logic rules where available (FCF's loop fission "is a HOL
  equality in our model").

## 2. CertiCrypt / EasyCrypt — the abstract-adversary tradition

Sources read in full by the agent: Barthe–Grégoire–Zanella POPL 2009;
Zanella et al. IEEE S&P 2009 (FDH); Barthe et al. CSF 2010 (Σ-protocols);
Barbosa et al. TOPS 2023 (journal of CCS 2021); SoK S&P 2021; EasyUC CSF
2019; Firsov–Unruh CPP 2022 artifact (`dfirsov/easycrypt-rewinding`);
Firsov–Janků ePrint 2025/573 artifact (`jjanku/fsec`).

### 2.1 CertiCrypt: adversary = syntax variable in a deep embedding

pWhile deeply embedded in Coq; adversaries are procedure *variables* with
a static well-formedness analysis over syntax (read/write policies);
pRHL rules *derived as lemmas* against the semantics (foundational, like
us). Costs admitted in print: FDH ≈ 3.5k lines, OAEP ≈ 3k; "about a third
of the proof scripts are devoted to basic facts about probabilities"
(S&P 2009 §4). Validation of our core bet: making the adversary a datum
buys induction over adversary structure with no axioms — CertiCrypt did it
with first-order syntax, we do it with `FreeM` trees. What their syntax
buys that ours doesn't: certified whole-program transformations
(deadcode/hoisting) by static analysis — our continuations are opaque, so
the analogue must be equational (bind laws, bisimulation). Even their full
deep embedding *postulated* per-operator time cost ("functional time
model", CSF 2010 §II.B) — nobody observes intrinsic time; remember this
when stating VCVio's PPT claims.

### 2.2 Rewinding: the historical pain point, documented

- CertiCrypt's flagship signature paper (S&P 2009) contains **no rewinding
  at all** — both FDH proofs are single-run RO-programming. The Σ-protocol
  paper (CSF 2010) reformulated proof-of-knowledge as *special soundness*
  (extractor is handed two transcripts) specifically so the rewinding
  experiment could stay on paper: "It can be shown using a rewinding
  argument **(although we did not formalize this result in Coq)**…" (§III).
  No general forking lemma was ever mechanized in CertiCrypt.
- EasyCrypt needed a four-paper arc: **(1)** Firsov–Unruh CPP 2022 —
  probabilistic *reflection* via a classical-choice operator (the
  denotation of an abstract module is conjured with `some_real`, since
  abstract procedures have no first-class semantics), plus rewindability
  as a **per-adversary axiom schema** (`RewProp`, verified verbatim from
  the artifact): the adversary must itself export `getState/setState`
  procedures serializing its whole global state injectively into an
  abstract `sbits` type, with pairing axioms. **(2)** Firsov–Unruh CSF
  2023 — ZK/PoK on top. **(3)** Barbosa et al. CRYPTO 2023 (Dilithium) —
  Bellare–Neven forking, requiring an *unmerged expected-cost fork* of
  EasyCrypt. **(4)** Firsov–Janků ePrint 2025/573 (CSF 2026) — general
  forking + Schnorr, still needing forgetful-oracle scaffolding, a
  `Stopping` theory, and a stack of serialization-injection axioms; its
  abstract still concedes "rewinding support is limited in existing
  verification frameworks."
- In our substrate every ingredient is definitional: reflection =
  `evalDist` of the tree; `RewProp` holds by `rfl` (state is a value;
  nothing needs serializing); reprogramming = a different handler on the
  same tree; query bounds = structural. **The plumbing vanishes; the
  analysis (Jensen/averaging, the acc²/q bound) remains** and must be
  proved over `evalDist` in VCVio — claim exactly that much in papers.

### 2.3 Module-system expressiveness limits (all with printed quotes)

- "there's no way to do a structural induction over modules in EASYCRYPT"
  — EasyUC §VI (they proved only an *instance* of UC composition).
- Modules can't be value-parameterized (EasyUC resorted to axioms fixing
  globals, §V-D); module equality inexpressible; `glob M` opaque.
- Unbounded abstract interaction breaks termination-sensitive lemmas
  (EasyUC's functionality/adversary ping-pong problem, §VI) — exactly what
  a coinductive layer handles semantically.
- Pre-2021, PPT of *constructed* adversaries was extra-logical ("EASYCRYPT
  doesn't help us in this analysis", EasyUC §V-D); the module system had
  "no complete formal semantics" until TOPS 2023.
- EasyUC scale datum: toy SMC-from-KE = 9 months, 18,000 lines.

The one-sentence ledger (use in paper 2): *the abstract-module tradition
made quantification cheap and structure expensive; the syntax-tree
approach inverts that — and rewinding, forking, adversary-dependent
hybrids, and UC-style composition all live on the structure side.*
The honest converse: EasyCrypt's SMT-backed pRHL + `eqobs` automation and
a decade of scheme libraries are what keep their proofs short; our
bisimulation/decoration lemma base must reach comparable ergonomics, and
"A cannot depend on X" arguments rest on construction (no ambient heap,
no internal parametricity in Lean), not on a syntactic checker.

### 2.4 Cost and UC (CCS 2021 / TOPS 2023) — designs to copy

- Their cost is a *tuple*: intrinsic cost (oracle calls priced 0) + per-
  oracle call counts. A free-monad substrate exhibits this natively:
  **query counts are theorem-grade structural facts; intrinsic time is a
  postulated decoration** — mirror the split and label it honestly.
- Their UC execution model — "control returns to the environment" along a
  procedure-call tree, machines statically fixed — is a paraphrase of
  interaction through a polynomial node structure; we can additionally
  model what they excluded by fiat (nonterminating interaction, free
  scheduling via `Interaction/Concurrent` frontiers).
- Copy the ∀∃ discipline with cost-indexed simulator/environment classes
  (their Def 6.1) and absorbing cost bookkeeping in composition — the
  "unrestricted ∃S too weak / unrestricted ∀Z too strong" trap is
  substrate-independent.
- Their price tags: 8 kLoC of tool changes; cost annotations at ratios up
  to ~1:3 of development; worst-case cost only.

## 3. SSProve and the interaction-trees lineage

Sources verified by the agent: SSProve repo source (`pkg_core_definition.v`,
`pkg_composition.v`, DOC.md) + CSF 2021 / TOPLAS 2023; ITrees POPL 2020 PDF
+ DeepSpec repo; gpaco CPP 2020; Foster–Hur–Woodcock CONCUR 2021 (+ TOSEM
2025); CTrees POPL 2023 PDF; Ticl/ICTrees OOPSLA2 2025; gitrees POPL 2024;
HITrees arXiv 2510.14558 (Lean!); Nominal-SSProve CSF 2025. Also verified
against PolyFun source (see correction below).

### 3.0 Correction to our own framing

PolyFun's `ITree.Shape` **has** a Tau (`step`, arity `PUnit`, guarding
`iter`). The honest differentiator is: **strong bisimulation is
definitional equality** (`Bisim = (·=·)` via the M-type universal property,
`ITree/Bisim/Defs.lean`), so there is no strong-bisim setoid, no `Proper`
instances, no `setoid_rewrite`; τ-handling is quarantined inside the
inductive `TauSteps` layer of `WeakBisim`. Never write "no Tau nodes".

### 3.1 SSProve: the package algebra, verified from source

`raw_code` is an **inductive** free monad (ret / opr / getr / putr /
sampler); validity `valid_code L I c` types imports + touched locations;
packages = interface-typed finite maps of procedures. Sequential
composition `link` *is* a Plotkin–Pretnar handler inlining; laws (strict
*equalities* of finite maps, which is what makes game-hops rewrites):
`link_assoc`, `par_commut` (needs `fseparate`), `par_assoc`, `link_id`/
`id_link`, and `interchange : (p₁∘p₃) ‖ (p₂∘p₄) = (p₁‖p₂) ∘ (p₃‖p₄)`.
Adversary = package exporting one `RUN : unit → bool`; reduction is the
rewrite `Advantage_link : Adv G₀ G₁ (A ∘ P) = Adv (P∘G₀) (P∘G₁) A` +
`Advantage_triangle`. Hard ceiling, structurally verified: **everything
terminates** — no Tau, no iteration, bounded-loop rules only; unbounded/
reactive protocols and UC are out of scope. Nominal-SSProve (CSF 2025)
calls the heap-disjointness side conditions "never satisfactorily
addressed" and replaces them with nominal sets — an argument for making
separation *intrinsic* (our ownership/lens discipline) rather than
side-conditional. PolyFun should mirror the law *names* (`link_assoc`,
`interchange`, `Advantage_link`) over `Spec`/`FreeM` with
`Interaction/Basic/Ownership` supplying separation.

### 3.2 ITrees in Rocq: what the pain actually is

`itree E R` coinductive, negative style (positive "breaks subject
reduction"); `eutt` is mixed inductive–coinductive (finite Tau-stripping
inductively, alignment coinductively) — same skeleton as PolyFun's
`TauSteps` + `Match`. Printed pain points: Coq coinduction "notoriously
limited"; transitivity/bind-congruence for eutt "quite challenging",
needing eqit skip-flags + euttG; anonymous functions "thwart the
setoid_rewrite tactic"; syntactic cofix guardedness "inherently
non-compositional" (hence first-class `iter`/`mrec`). gpaco (CPP 2020)
exists because nested paco "forgets all available accumulated knowledge".
Monad laws hold only up to strong-bisim setoid `≅`. The completeness bar
to adopt: the four Bloom–Ésik `iter` laws (fixed point, parameter,
composition, codiagonal), `interp` a monad morphism, `mrec` unfolding law
(PolyFun `ITree/Rec` `mutualRec` should match it). Rhetorical gift:
POPL 2020 §9 judged Lean "seemingly inadequate to the task" for lacking
coinductive types — Mathlib's `PFunctor.M` + `Bisim = Eq` is the rebuttal.
§8.3 also concedes the container presentation (Hancock–Setzer/McBride) is
the MLTT-native one.

### 3.3 Isabelle ITrees, CTrees, and the 2023–25 frontier

- **Foster–Hur–Woodcock (CONCUR 2021; not AFP** — no such entry exists,
  contrary to a guess in our prompt): `Vis` carries a *partial function*
  from events (deadlock/external choice in the type; per-event
  deterministic), corec-with-friends for bind, weak bisim as
  coinductive-inductive over `τⁿ` stabilization, `div` unique divergent
  tree. Their one-shot-coinduction + automation style works *because*
  strong bisim is equality-like — evidence our non-paco approach scales.
  Useful vocabulary for B3: `stable`/`stabilises`/`τⁿ` normal forms.
- **CTrees (POPL 2023)**: for internal nondeterminism, two branch kinds
  (`brS` stepping / `brD` delayed), LTS derived, `sbisim`/`wbisim` via
  Pous's companion library (not paco) — and they still pay an `equ ≠ eq`
  tax. Their "enhanced" version drifts to container-indexed branching
  (their footnote concedes our representation). **ICTrees/Ticl (OOPSLA2
  2025)** retreat to *one* branching kind — lesson: if `Concurrent` ever
  needs ITree-level nondeterminism, add one branch shape to the one-step
  polynomial, derive the LTS, and port the *tower/companion* principle,
  not gpaco.
- **Higher-order effects** delimit our claim: gitrees (POPL 2024,
  guarded/Iris) and **HITrees (arXiv 2510.14558 — in Lean, must-cite)**
  handle effects that take/return computations; polynomial signatures
  with dependent arities cover *indexed* but not *higher-order* effects.
  Say so explicitly.

### 3.4 The 2×2 that positions us

No system in the itree lineage has SSProve's typed package algebra;
SSProve has no coinduction. PolyFun/VCVio occupies the empty cell:
SSP-style strict package laws over the inductive `FreeM` layer, plus
M-type weak bisimulation for unbounded/reactive interaction, with
separation intrinsic (ownership/lenses) rather than side-conditional —
and, unlike every listed system, one polynomial substrate under both.

## 4. Poly formalization landscape and novelty

Sources verified 2026-07-10: github.com/sinhp/Poly; Mathlib4 docs; Ahman's
Directed-Containers Agda repo; arXiv/LIPIcs/EPTCS as cited; 1lab.

### 4.1 Who has what

- **sinhp/Poly (Lean 4; Hazratpour with Awodey, Riehl, Nawrocki, Carneiro
  as active committers).** *Categorical* polynomial functors over an
  arbitrary category with pullbacks (`UvPoly` wraps `p : E ⟶ B`;
  Gambino–Kock/LCCC style, aimed at HoTTLean natural models). Has:
  LCCC + Beck–Chevalley + a distributivity file, polynomial composition
  with its classifying property (still carrying a `sorry` at fetch time),
  monoidal structure on `UvPoly.Total`. Homs are *pullback squares* — only
  cartesian morphisms; no general lenses, **no vertical–cartesian
  factorization, no ◁-comonoid theory, no dynamical systems, no charts**.
  Complementary, not competing: different Hom, different setting.
- **Mathlib.** `PFunctor` (+ `comp`, W, M), MvPFunctor, QPF
  (Avigad–Carneiro–Hudon ITP 2019). Verified: **no morphism type between
  PFunctors at all** — no category, no monoidal structure, no lenses. The
  entire Poly-as-category layer is missing upstream; PolyFun is building
  on virgin ground from Mathlib's perspective.
- **Ahman's Directed-Containers (Agda; FoSSaCS'12/LMCS'14, MSFP'16).**
  Mechanizes directed containers ≅ comonad structures on container
  functors — the container-side content of "◁-comonoids are categories",
  predating the categorical phrasing. **The comonoid ↔ small-category
  equivalence itself (Ahman–Uustalu 2016 / book Thm 7.28) has never been
  mechanized in any assistant.** Bicomodules: no mechanization anywhere.
- **Aberlé, arXiv 2604.01303 (Agda, submitted ACT 2026)** — closest in
  spirit to PolyFun: concrete containers, lenses, free monad + Kleisli,
  wiring-diagram composition, Mealy-machine semantics, dependent free
  monad for Hoare-style verification. But: cofree comonoid, ◁ coherence,
  comonoids-as-categories, ⊗-closure eval/curry, factorization — all
  absent (the cofree connection is Appendix-B prose only). Cite strongly.
- **Others.** 1lab `Cat.Instances.Poly` (Cubical Agda: category of
  dependent lenses, no monoidal structure, no charts); Finster–Lucas–
  Mimram–Seiller MFPS 2021 (Agda, finitary polynomials over groupoids,
  bicategorical composition); De Pascalis–Uustalu–Veltri 2509.25879
  (Cubical Agda, monoids in indexed-container composition = monads);
  Damato–Altenkirch–Ljungström ITP 2025 (containers preserve W/M).
  PolyTT/CatColab are implementations, not mechanized theory. David Jaz
  Myers' *Categorical Systems Theory* draft = the yardstick for what a
  full systems doctrine includes (unmechanized).
- **Category-theoretic crypto.** Broadbent–Karvonen (FoSSaCS'22/LMCS'23)
  unmechanized; SSProve = package algebra, not category theory; CatCrypt
  (Spitters, ePrint 2026/604) is Rust→Lean SSP-tradition, closed-source,
  no polynomial functors. **No other group connects Poly to protocol or
  crypto semantics** — the VCVio/PolyFun line is alone in that position.

### 4.2 Novelty verdict (condensed from the agent's table)

First-mechanization-anywhere candidates (no prior art found in any proof
assistant): **⊗-closure with eval/curry (A1)**; **vertical–cartesian
factorization on the full lens category (A3)**; **◁-comonoids = small
categories (B1/Thm 7.28)**; **retrofunctors ↔ vwb lenses (B5)**; **cofree
comonoid with universal property (C2/C3)**; **FreeM ⊣ Cofree / pattern-
runs-on-matter module structure (C4)**; **bicomodules/prafunctors (D1–D4)**;
**lens/chart interplay with coherence** (already shipped in PolyFun).
First-in-Lean-4 but with cross-assistant prior art to cite: the category
Poly itself (1lab), ◁ with coherence (sinhp partial, Finster et al.
bicategorical), behavior-uniqueness dynamics (generic coalgebra
literature + Aberlé's Mealy machines).

Citation obligations for papers 2–3: sinhp/Poly, danelahman/
Directed-Containers, Aberlé 2604.01303, 1lab, Finster et al. MFPS 2021,
Mathlib QPF (ITP 2019), Libkind–Spivak ACT 2024 (EPTCS 429, the
pattern-runs-on-matter module structure — the honest form of the
`FreeM ⊣ Cofree` slogan).

### 4.3 Housekeeping found

The book is published: Niu–Spivak, *Polynomial Functors: A Mathematical
Theory of Interaction*, **Cambridge University Press, LMS Lecture Note
Series 498, 2025** (DOI 10.1017/9781009576734). PolyFun's `REFERENCES.md` /
`CLAUDE.md` say "MIT Press 2024" — fix (tracked in `corrections.md`).

## 5. Synthesis: Phase B design directives

Consolidated from all four sections; these are the commitments the survey
buys, in rough priority order.

1. **Law-set contract for run/handle** (from CryptHOL §1.2): PolyFun/VCVio
   must ship the analogues of `exec_gpv_simps`, `exec_gpv_bind`,
   `inline_bind_gpv`, `inline_assoc` (strict, state hidden by lenses),
   `exec_gpv_inline`, with dispatch/product combinators and decomposition
   lemmas. This list *is* the API; everything else is implementation.
2. **One hard coinduction per combinator.** No transfer engine in Lean, so
   prove the relator-parametricity lemma once per operator, then derive
   `exec_gpv_oracle_bisim`-shaped one-shot rules (state relation +
   per-step coupling ⟹ run equivalence) as the only user-facing surface.
3. **Bundle the analysis predicates.** WT/lossless/bounds/termination as
   one structure carried by instances along every combinator (CryptHOL's
   four-hypothesis packet and CC's `lossless_attach` show the tax of not
   doing this). A predicate earns its place only with preservation lemmas
   through bind, handle, and run.
4. **Run-limit infrastructure (B3) = the fixpoint-induction trio**:
   admissibility automation, strong induction, and **parallel fixpoint
   induction relating two truncation towers** (CryptHOL's most-used trick)
   — build parallel first. Keep `interaction_bound`'s pattern: exact sup
   internal, inequality-only user API.
5. **Advertise behavior-level operators** (state hidden) as the primary
   algebra, anamorphism (`corec`) as the bridge — [CSF19] rebuilt exactly
   this by hand and called it the cleaner algebra. Ship the wiring-lens
   calculus (assoc/swap/id + composition) as first-class.
6. **Observational equivalence on monad-weighted frontiers**, not states
   (CC's determinization functor) — pointwise trace equality is *wrong*
   probabilistically. Design `Dynamical/Behavior` + `Concurrent`
   observation APIs to anticipate this; check Ch 8 bicomodules for the
   generic home in R4.
7. **Package layer**: SSProve's law names (`link_assoc`, `par_commut`,
   `interchange`, `Advantage_link`, `Advantage_triangle`) as strict
   equalities over `Spec`/`FreeM`, with separation intrinsic via
   `Ownership`/lenses (Nominal-SSProve's critique of side-conditional
   disjointness).
8. **ITree-layer completeness bar**: Bloom–Ésik's four iter laws, `interp`
   monad morphism, `mrec` unfolding law. Up-to closures in order:
   up-to-bind, up-to-strong-Eq (free for us since strong = `Eq`); if
   nested coinduction appears, port Pous's tower/companion, not gpaco.
9. **PPT honesty split** (CCS 2021): query counts are theorem-grade
   structural facts; intrinsic time is a labeled model assumption. Never
   blur the two in papers.
10. **Adoption warning** (CryptHOL §1.6): third-party users routed around
    the GPV layer entirely. The coalgebra/machine layer must be cheap at
    the point of use — worked examples and `PolyFunTest/` smoke tests are
    not optional polish; they are the adoption mechanism.
