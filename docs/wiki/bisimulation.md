# Bisimulation And Behavioural Equivalence

This page is the agent-facing glossary for the several bisimulation and
behavioural-equivalence notions in PolyFun. They span three layers (interaction
trees, dynamical systems, UC open processes) and are easy to confuse because the
words "bisimulation", "weak", and "observation" are reused with different
technical meanings. The source files are the final authority; this page situates
them relative to one another.

## The generic framework: `Control.LTS` + `Control.WeakBisim` / `StrongBisim`

`PolyFun/Control/Bisimulation.lean` factors the common construction out of the
per-layer relations. A `Control.LTS Obs` is a labeled transition system: a state
space, a family of `Move`s out of each state, a `next` successor per move, and a
`label` that is either **silent** (`none`, a τ-move) or a **visible** observation
(`some o`). On two systems sharing an observation alphabet it defines two
bisimulations:

- **`StrongBisim`** (`IsStrongBisim`): every move — silent or visible — is
  matched *immediately* by an equally-labeled move preserving the relation.
- **`WeakBisim`** (`IsWeakBisim`): silent moves may be matched by *any* move or
  **stuttered** (the other side stays put); visible moves are matched
  immediately by an equally-labeled visible move.

Both come with `refl`/`symm`/`trans` proved **once**, and `StrongBisim.toWeakBisim`
records the inclusion `StrongBisim ⊆ WeakBisim`. Two properties are worth
knowing:

- **`trans` is constructive / axiom-free.** Silence is a decidable `Option`
  label, so the transitivity stutter argument classifies the middle move by
  reading its label — no `Classical.em`. (`#print axioms Control.WeakBisim.trans`
  is `[]`.)
- **`WeakBisim` matches visible moves immediately** — it does *not* absorb silent
  steps *around* a visible action. This is the "delay" flavour, not full weak
  bisimulation; see the spectrum below.

## The spectrum

For a fixed transition system, the notions are ordered strong ⊂ delay ⊂ weak:

| Flavour | Silent steps | Visible steps | In PolyFun |
|---|---|---|---|
| **strong** | matched immediately | matched immediately | `ITree.Bisim` (`= Eq`); `DynSystem.ObsEq` / `IsSimulation`; `Control.StrongBisim` |
| **delay** | absorbed (stutter) | matched **immediately** | `Interaction.UC.OpenProcessIso` `=` `Control.WeakBisim` |
| **weak** | absorbed | matched **up to** silent steps | `ITree.WeakBisim` (`eutt` / `≈`) |

The three are genuinely different equivalences, not one notion written three
times. In particular `eutt` relates `pure r ≈ step (pure r)` (a silent step
before an observation), which is **not** an `OpenProcessIso`/`Control.WeakBisim`
relation. So `ITree.WeakBisim` is *not* an instance of `Control.WeakBisim`; a
fully-weak generic notion (visible-up-to-silent, via a τ*-closure) is the natural
extension and is future work.

## Per-layer notions

### Interaction trees (`PolyFun/ITree/Bisim/`)
- `ITree.Bisim t s := t = s` — **strong** bisimulation *is definitional
  equality*, because `ITree F = M (Poly F)` is a terminal coalgebra. This is the
  setoid/paco-free payoff the project advertises.
- `ITree.WeakBisim` (`≈`, Coq `eutt`) — **weak** bisimulation, a Tarski greatest
  fixed point of "strip finitely many τ-`step` nodes (`TauSteps`) then match
  observable heads (`Match`)". Equivalence + `Setoid` + continuation
  bind-congruence in `Bisim/Equiv.lean`, `Bisim/Bind.lean`.

### Dynamical systems (`PolyFun/PFunctor/Dynamical/`)
- `DynSystem.behavior : S → M p` (`Trajectory.lean`) — the unique map into the
  terminal `p`-coalgebra; `DynSystem.ObsEq s₁ s₂ := behavior s₁ = behavior s₂`
  is behavioural equivalence as **honest `Eq`** of behaviour trees.
- `DynSystem.IsSimulation` / `implements_of_isSimulation` (`Refinement.lean`) —
  a step-synchronized simulation forces equal behaviour trees, via
  `M.corec_eq_corec`.
- `DynSystem.ForwardSimulation` / `Bisimulation` (`Refinement.lean`) — the lax,
  step-relation-parameterized simulations with run-transport; instantiated by
  `Concurrent.Bisimulation` (a *strong* relational bisimulation over process
  transcripts).
- **Framework connection** (`Dynamical/Bisimulation.lean`): `DynSystem.toLTS`
  exhibits a `p`-system as a `Control.LTS`, and
  `DynSystem.obsEq_of_isStrongBisim` proves a generic `Control.StrongBisim` on
  the induced systems implies `ObsEq` — "bisimulation ⟹ behavioural
  equivalence", landing the generic framework on the M-finality equality.

### UC open processes (`PolyFun/Interaction/UC/`)
- `OpenProcessIso` (`OpenProcess.lean`) — the silent-step-absorbing **delay**
  bisimulation used to prove the concrete `openTheory` monoidal/compact-closed
  laws up to bisimilarity. `OpenProcessBisim.lean` proves
  `openProcessIso_iff_weakBisim` (it *is* `Control.WeakBisim` at the process
  LTS) and re-derives its `refl`/`symm`/`trans` from the generic lemmas.
- `Observation.bisim` (`BisimObservation.lean`) — `OpenProcessIso` packaged as
  an `Emulates` `Observation`, so UC emulation can be judged **up to weak
  (delay) bisimulation** rather than syntactic equality. With
  `Emulates.plug_compose_of_commObs` / `plug_compose_bisim`, UC `plug`-
  composition applies to the concrete process model (which is not
  `HasPlugWireFactor` on the nose).

## See also

- [`itree.md`](itree.md), [`pfunctor.md`](pfunctor.md),
  [`interaction.md`](interaction.md) for the surrounding layers.
- `docs/reading/roadmap.md` long-term follow-on #4 (the sim/bisim glossary this
  page discharges) and the delay-vs-weak finding.
