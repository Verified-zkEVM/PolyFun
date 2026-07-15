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

The generic LTS weak closure and `ITree.WeakBisim` describe the same standard
shape at different representation layers; no adapter is claimed here until it
preserves dependent event labels and continuations explicitly.

## UC open processes

`OpenProcess.activationLTS` labels a complete silent transcript by `none` and
every activated transcript by the single observation `some ()`.
`OpenProcessActivationEquiv` is exactly whole-system delay bisimulation of
these generic labelled transition systems. The structural `openTheory` laws
prove the stronger delay notion (not merely weak bisimulation): their matches
are immediate activation-preserving steps or genuine silent stutters.

This observation is deliberately coarse. It does not retain packet/action
identity or `stepSampler` effects, and is therefore **not** exported as a UC
security `Observation`.

The generic theorems `Emulates.plug_right_of_observes_plug_comm` and
`plug_compose_of_observes_plug_comm` are still useful: a concrete security observation can
apply them once it proves plug commutation while retaining the events and
effects relevant to the security statement.
`openTheory_plug_comm_activation_equiv` remains
a structural coherence lemma, not an indistinguishability definition.

## Naming rule

Use “simulation” for a directional, relation-local preservation theorem;
“bisimulation” when both directions are present; “bisimilar” for a state pair;
and “bisimulation equivalent” only for a total whole-system witness. Always say
strong, delay, or weak when silent transitions are possible.
