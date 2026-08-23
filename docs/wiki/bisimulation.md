# Bisimulation and behavioural equivalence

PolyFun has several related notions whose names are easy to conflate. This page
records their precise boundaries.

## Generic labelled transition systems

`PolyFun/Control/Bisimulation.lean` defines `Control.LTS Obs`. A direct
transition has an `Option Obs` label: `none` is silent (`τ`), while `some o` is
visible. The derived transitions are:

- `SilentSteps`: zero or more silent transitions;
- `DelayStep none`: `τ*`;
- `DelayStep (some o)`: `τ*` followed by one `o`-transition;
- `WeakStep none`: `τ*`;
- `WeakStep (some o)`: `τ*`, one `o`-transition, then `τ*`.

This gives the standard spectrum:

| Flavour | Match for a silent transition | Match for a visible transition |
|---|---|---|
| strong | one silent transition | one equally labelled transition |
| delay | `τ*` | `τ*` then one equally labelled transition |
| weak | `τ*` | `τ*`, one equally labelled transition, `τ*` |

The API deliberately separates three levels:

- `Is{Strong,Delay,Weak}Simulation` and `Is…Bisimulation` concern a supplied
  relation and impose no totality condition;
- `{Strong,Delay,Weak}Bisimilar L₁ L₂ s₁ s₂` concern a particular pair of
  states and have reflexive, symmetric, and transitive laws;
- `{Strong,Delay,Weak}BisimulationEquivalent L₁ L₂` require a bisimulation relation
  that is total on both state spaces.

Closure lemmas lift simulations across silent/delay/weak paths, and the
inclusions `strong ⊆ delay ⊆ weak` are explicit. State and move universes are
independent on the two sides.

### Relation to cslib

The *theory* of these notions is cslib's, not PolyFun's. `Control.LTS` is
move-indexed — a state exposes a type of moves, each with a target and a label —
which is the polynomial-coalgebra presentation and is what lets `DynSystem` and
`ITree` adapt into this layer. cslib's `Cslib.LTS` is relation-indexed. `Step`
projects one onto the other:

```lean
instance : Cslib.HasTau (Option Obs) := ⟨none⟩
def Control.LTS.toLts (L : LTS Obs) : Cslib.LTS L.State (Option Obs) := ⟨L.Step⟩
```

Two step-level correspondences are definitional (`toLts_tr`, `τSTr_toLts`): a
silent closure *is* cslib's `τSTr`. `sTr_toLts_iff` identifies `WeakStep` with
cslib's saturated transition `STr`, and the relation-level correspondences
follow:

| PolyFun | cslib |
|---|---|
| `IsStrongSimulation` | `IsSimulation` on `toLts` |
| `IsStrongBisimulation` | `IsBisimulation` on `toLts` |
| `StrongBisimilar` | `Bisimilarity` on `toLts` |
| `IsWeakSimulation` | `IsSimulation` into `toLts.saturate` |
| `IsWeakBisimulation` | `IsSWBisimulation`, hence `IsWeakBisimulation` |
| `WeakBisimilar` | `WeakBisimilarity` |
| `LTS.WeakTrace s obs t` | `MTr` of `toLts.saturate` at `obs.map some` |

The weak entry is the substantive one. PolyFun's weak bisimulation issues a
*single* transition as the challenge and answers with a weak one — which is
exactly cslib's `IsSWBisimulation`, not its `IsWeakBisimulation` (bisimulation
of the saturated systems). That the two agree is Sangiorgi's Lemma 4.2.10,
proved in cslib and transported by `isWeakBisimulation_iff`. PolyFun never
proved it.

`WeakTrace` records only the *visible* observations, so it is a `List Obs` where
a cslib trace is a `List Label`; tagging each observation with `some` recovers
the cslib trace of the saturated system.

**The delay spectrum has no cslib counterpart** and is developed in PolyFun. It
is load-bearing — `OpenProcessActivationEquiv` is delay bisimulation, not weak —
so it is the clearest upstream contribution candidate. See
[`../reading/upstream-alignment.md`](../reading/upstream-alignment.md).

## Dynamical systems

`DynSystem.behavior : S → M p` is the unique map into the terminal
`p`-coalgebra. `DynSystem.ObsEq` is equality of those behaviour trees.
`DynSystem.IsSimulation` is the synchronized, polynomial-specific relation:
related states expose the same position and remain related after every
direction.

`Dynamical/Bisimulation.lean` supplies an adapter:

- `DynSystem.toLTS` records the current polynomial position and direction as
  visible observations;
- `isSimulation_of_isStrongSimulation` turns a generic strong LTS simulation
  into the existing `DynSystem.IsSimulation`;
- `isStrongSimulation_of_isSimulation` gives the converse, and
  `isStrongSimulation_toLTS_iff_isSimulation` packages the exact
  correspondence;
- `obsEq_of_isStrongSimulation` then reuses
  `behavior_eq_of_isSimulation` to obtain equality of behavior trees.

The adapter contains no second coinduction proof; terminal-coalgebra finality
remains the single behavioural-equality principle.

## Interaction trees

- `ITree.Bisim` is strong/structural bisimulation and coincides with `Eq` by the
  M-type universal property.
- `ITree.WeakBisimRel RR` is the relational `euttR`-style relation. The trees
  share an event signature but may return types in independent universes;
  pure leaves are compared by `RR`, while finite `TauSteps` around observable
  heads are ignored.
- `ITree.WeakBisim` is definitionally `WeakBisimRel Eq`. It supplies the
  same-type equivalence and `Setoid` used by the existing simulation theory.
- `bind_weakBisimRel` and `map_weakBisimRel` are the two-sided congruence laws:
  they relate different source return types and different continuation return
  types without collapsing their universes.

`ITree.toLTS F α` is the explicit adapter to the generic LTS layer. Its states
are `Option (ITree F α)` so a visible return can enter terminal state `none`;
its labels record either a dependent event/reply pair or a returned value.
`weakBisim_isLTSWeakBisimulation` proves that `ITree.WeakBisim`, lifted to
optional states, is a generic weak bisimulation, and
`traces_eq_of_weakBisim` derives equality of finite visible trace sets.

## UC open processes

`OpenProcess.activationLTS` labels a complete silent path by `none` and
every activated path by the single observation `some ()`.
`OpenProcessActivationEquiv` is exactly whole-system delay bisimulation of
these generic labelled transition systems. The structural `openTheory` laws
prove the stronger delay notion (not merely weak bisimulation): their matches
are immediate activation-preserving steps or genuine silent stutters.

This observation is deliberately coarse. It does not retain packet/action
identity or `stepSampler` effects, and is therefore **not** exported as a UC
security `Observation`.

The generic theorems `Emulates.plug_right` and `Emulates.plug_compose` require
the exact class `Observation.RespectsPlugComm`. A concrete security observation
can apply them once it proves plug commutation while retaining every event and
effect relevant to the security statement. The structural theorem
`openTheory_plug_comm_activation_equiv` does not supply that proof: it remains
a scheduler-coherence lemma, not an indistinguishability definition.

## Naming rule

Use “simulation” for a directional, relation-local preservation theorem;
“bisimulation” when both directions are present; “bisimilar” for a state pair;
and “bisimulation equivalent” only for a total whole-system witness. Always say
strong, delay, or weak when silent transitions are possible.
