/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Decoration
import PolyFun.Interaction.Multiparty.Core
import PolyFun.PFunctor.Dynamical.Combinators
import PolyFun.PFunctor.Dynamical.Safety
import PolyFun.PFunctor.Dynamical.Trajectory
import Mathlib.Data.PFunctor.Univariate.M
import Batteries.Tactic.Lint

/-!
# Dynamic concurrent processes

This file introduces the semantic center of the concurrent `Interaction`
layer.

The structural syntax in `Concurrent.Spec` is a useful source language, but it
is not the only natural presentation of concurrency. Many systems are better
viewed as a **residual process** which, at any moment, exposes one finite
sequential interaction episode; completing that episode yields the next
residual process.

That is the viewpoint formalized here.

The file is organized in two levels:

* `StepOver Γ P` and `ProcessOver Γ` are the generic forms, parameterized by a
  realized node context `Γ`;
* `Step Party P` and `Process Party` are the closed-world specializations whose
  node metadata is exactly `NodeProfile Party`, the bundled
  `NodeAuthority + NodeView` view of node-local semantic data.

So the intended reading is:

* a **step** is one finite local protocol episode,
* a **process** is an unbounded sequence of such steps obtained by
  continuation,
* and controller / observation metadata lives in a node context rather than
  being built into the process infrastructure itself.

This design stays continuation-first, but is more general than the structural
tree frontend: cyclic or unbounded behavior is represented by the residual
state type, while each individual step remains a finite `Interaction.Spec`.
-/

universe u v w w₂ w₃

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace Concurrent

/--
`NodeAuthority Party X` records the controller-attribution part of node-local
semantic data: which parties are credited as controllers of each move
`x : X`.

This is one of the two orthogonal layers of `NodeProfile`. It is stored
separately so that downstream reasoning that depends only on
controller attribution (corruption policies, scheduler accountability,
party-side responsibility arguments) can take a `NodeAuthority` parameter
without committing to any particular observation structure.
-/
structure NodeAuthority (Party : Type u) (X : Type w) where
  /-- `controllers x` is the ordered list of parties credited as controllers of
  the move `x : X`. -/
  controllers : X → List Party := fun _ => []

/--
`NodeView Party X` records the view-attribution part of node-local
semantic data: what each party `me : Party` locally observes of the
chosen move `x : X`, expressed as a `Multiparty.ViewMode X`.

This is the second of the two orthogonal layers of `NodeProfile`. It
is stored separately so that downstream reasoning that depends only on
local views (information-flow arguments, projection / trace semantics,
view-equivalence proofs) can take a `NodeView` parameter without
committing to any particular controller attribution.

The name avoids confusion with `Multiparty.Observation X`, which is the
unrelated **per-move information-lattice kernel** living in
`Multiparty/Observation.lean`. `NodeView` is the per-party operational
view assignment at one node; `Observation` is one quotient morphism
`X → Obs` packaged with its codomain.
-/
structure NodeView (Party : Type u) (X : Type w) where
  /-- `views me` is the local view that party `me` has of the chosen move,
  expressed as a `Multiparty.ViewMode X`. -/
  views : Party → Multiparty.ViewMode X

/--
`NodeProfile Party X` records the local semantic data attached to one
sequential interaction node whose move space is `X`.

It bundles two orthogonal layers:

* `NodeAuthority Party X` — `controllers x` is the controller-path contribution
  associated to choosing the move `x : X`;
* `NodeView Party X` — `views me` assigns to party `me` its local view
  of the chosen move.

The two layers are intentionally stored as separate factor structures.
Many natural systems align them so that the first controller in
`controllers x` has local view `.active`, but this file does not force that
relationship definitionally; any desired coherence law can be imposed later
as a separate well-formedness predicate.

Because `NodeProfile` `extends` both factors, the dot-notation accessors
`node.controllers`, `node.views` and the structure-literal constructor
`{ controllers := ..., views := ... }` work exactly as if the fields were
declared inline. The factor projections `node.toNodeAuthority`,
`node.toNodeView` are auto-generated and let downstream code restrict
attention to a single layer.
-/
structure NodeProfile (Party : Type u) (X : Type w)
    extends NodeAuthority Party X, NodeView Party X

/--
The closed-world node context used by the current concurrent semantics.

At a node with move space `X`, the context value is exactly the
`NodeProfile Party X` describing:

* which parties are recorded as controllers of the chosen move, and
* what each party locally observes of that move.

This is the context whose specialization recovers the existing closed-world
`Step` / `Process` APIs.
-/
abbrev StepContext (Party : Type u) := fun X => NodeProfile Party X

/--
`StepOver Γ P` is one finite sequential interaction episode whose nodes are
decorated by realized context `Γ`, and whose completion produces the next
residual process state `P`.

Fields:

* `spec` is the shape of the sequential interaction episode;
* `semantics` decorates that sequential tree by node-local context `Γ`;
* `next` maps a complete transcript of that episode to the next residual
  process state.

The important point is that a `StepOver` is **not** restricted to a single
atomic event. One concurrent step may itself be a short sequential protocol:
for example, a scheduler choice followed by a payload choice, or a small
request/response exchange treated as one logical concurrent transition.

So `StepOver` is the right object when the concurrency layer should expose
finite sequential structure inside each global step, rather than flattening
everything into atomic transitions.

## Polynomial reading

`StepOver Γ P` is the application to `P` of the polynomial functor
`StepOver.toPFunctor Γ` whose positions are `Γ`-decorated specs and whose
directions over a position are transcripts of its underlying spec. The
`Equiv` `StepOver.equivObj` exhibits this on the nose by regrouping the
`(spec, semantics, next)` fields. The position type is itself equivalent to
`Interaction.Spec.DecoratedSpec Γ` via `Interaction.Spec.decoratedSpecEquiv`,
identifying `StepOver` as a polynomial substrate built directly on top of
`Γ.toPFunctor`. The structure form is preserved as the working API because
its named fields support clean `{ spec := ..., semantics := ..., next := ... }`
construction at every call site, and projections such as `(mapContext f s).spec`
are definitionally equal to `s.spec`.
-/
structure StepOver (Γ : Interaction.Spec.Node.Context.{w, w₂}) (P : Type v) where
  /-- The shape of the finite sequential interaction episode of this step. -/
  spec : Interaction.Spec.{w}
  /-- The decoration of `spec` by node-local context `Γ`. -/
  semantics : PFunctor.FreeM.Displayed.Decoration Γ spec
  /-- Maps a complete transcript of `spec` to the next residual process state. -/
  next : PFunctor.FreeM.Path spec → P

namespace StepOver

/--
Map the node-local context carried by a step along a realized context morphism.

This changes only the metadata decorating the step protocol. The underlying
sequential interaction tree and the continuation `next` are left unchanged.
-/
def mapContext
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {P : Type v}
    (f : Interaction.Spec.Node.ContextHom Γ Δ)
    (step : StepOver Γ P) : StepOver Δ P where
  spec := step.spec
  semantics := PFunctor.FreeM.Displayed.Decoration.map f step.spec step.semantics
  next := step.next

end StepOver

/-- `StepOver Γ` is functorial in the continuation type: `map f` post-composes `f` after
the `next` continuation, preserving the interaction protocol and its decoration. -/
instance {Γ : Interaction.Spec.Node.Context.{w, w₂}} : Functor (StepOver.{v, w, w₂} Γ) where
  map f s := { spec := s.spec, semantics := s.semantics, next := f ∘ s.next }

instance {Γ : Interaction.Spec.Node.Context.{w, w₂}} :
    LawfulFunctor (StepOver.{v, w, w₂} Γ) where
  id_map _ := rfl
  comp_map _ _ _ := rfl
  map_const := rfl

namespace StepOver

/-! ### Polynomial bridge

`StepOver Γ P` is the application to `P` of the polynomial functor
`StepOver.toPFunctor Γ` whose positions are `Γ`-decorated specs and whose
direction family at each position is the type of complete transcripts of
the underlying spec. The `Equiv` `StepOver.equivObj` regroups the
`(spec, semantics, next)` fields into the polynomial form
`(position, continuation)`; both roundtrips are definitionally `rfl`.

The position type `Σ spec, Decoration Γ spec` is itself equivalent to
`Interaction.Spec.DecoratedSpec Γ` via `Interaction.Spec.decoratedSpecEquiv`,
which is the free monad on `Γ.toPFunctor` at the unit payload. This bridge
identifies `StepOver` as a polynomial substrate sitting directly on top of
`Γ.toPFunctor` while preserving the structure form's ergonomic call sites
and definitional projection equalities. -/

/-- The polynomial functor whose application to `P` is `StepOver Γ P`.

A position is a `Γ`-decorated spec — a pair of an interaction shape
`spec : Spec` and a `Decoration Γ spec` of per-node `Γ`-metadata on it.
A direction over such a position is a complete transcript of `spec`.

Up to `Interaction.Spec.decoratedSpecEquiv`, positions are exactly
`Interaction.Spec.DecoratedSpec Γ`, the free term of `Γ.toPFunctor` at the
unit payload. -/
@[reducible]
def toPFunctor (Γ : Interaction.Spec.Node.Context.{w, w₂}) :
    PFunctor.{max (w+1) w₂, w} where
  A := Σ spec : Interaction.Spec.{w}, PFunctor.FreeM.Displayed.Decoration Γ spec
  B := fun p => PFunctor.FreeM.Path p.1

/-- `StepOver Γ P` is exactly `(StepOver.toPFunctor Γ).Obj P`, exhibiting
the step-over structure as a polynomial application.

The forward direction regroups the `(spec, semantics, next)` fields into
the polynomial form `(position, continuation)`, and the inverse unpacks
them again. Both roundtrips are definitionally `rfl`. -/
@[simps]
def equivObj {Γ : Interaction.Spec.Node.Context.{w, w₂}} {P : Type v} :
    StepOver.{v, w, w₂} Γ P ≃ (StepOver.toPFunctor Γ).Obj P where
  toFun s := ⟨⟨s.spec, s.semantics⟩, s.next⟩
  invFun := fun ⟨⟨spec, semantics⟩, next⟩ => ⟨spec, semantics, next⟩
  left_inv _ := rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

/-- The position type of `StepOver.toPFunctor Γ` is the same data as a
`Γ`-decorated spec, via `Interaction.Spec.decoratedSpecEquiv`. This is the
bridge that identifies the `StepOver` polynomial as a substrate built on
top of `Γ.toPFunctor`. -/
def equivPositions (Γ : Interaction.Spec.Node.Context.{w, w₂}) :
    (StepOver.toPFunctor Γ).A ≃ Interaction.Spec.DecoratedSpec Γ :=
  Interaction.Spec.decoratedSpecEquiv.symm

end StepOver

/--
`ProcessOver P Γ` is a continuation-based concurrent process with residual
state space `P`, whose current step episodes are decorated by realized context
`Γ`: a dynamical system over the step polynomial `StepOver.toPFunctor Γ`.

From any residual process state `p : P`, the process exposes exactly one
step protocol `step p : StepOver Γ P`. Running that step to completion
produces the next residual state.

So `ProcessOver` should be read as:

> a system whose behavior unfolds as a sequence of finite step protocols.

This is the generic semantic center for the concurrent layer. Structural
trees, flat machines, and future frontends can all compile into `ProcessOver`
by choosing an appropriate node-local context `Γ`.

Being a `PFunctor.DynSystem`, the whole dynamical-system toolkit applies to
processes directly: the coalgebra structure map (`DynSystem.out`, with its
coalgebra packaging `DynSystem.coalg`), terminal-coalgebra behavior and
observational equivalence (`DynSystem.behavior`, `DynSystem.ObsEq`), finite
and infinite orbits (`DynSystem.Prefix`, `DynSystem.Run`), and transition
metadata (`DynSystem.EventMap`, `DynSystem.SafetySpec`, …). The `StepOver`-shaped
views of the coalgebra structure map are `ProcessOver.step` and
`ProcessOver.ofStep`.
-/
abbrev ProcessOver (P : Type v) (Γ : Interaction.Spec.Node.Context.{w, w₂}) :=
  PFunctor.DynSystem P (StepOver.toPFunctor Γ)

namespace ProcessOver

/-- The type of residual process states: the process's state-space parameter,
exposed under its dynamical name for dot notation at use sites. -/
-- The process argument exists only to support dot notation; the state space is
-- fully determined by the parameter `P`.
@[nolint unusedArguments]
abbrev Proc {P : Type v} {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (_process : ProcessOver.{v, w, w₂} P Γ) : Type v :=
  P

/-- The step protocol exposed at each residual state, whose completion yields
the next state: the `StepOver`-shaped view of the coalgebra structure map.

Reducible so that it unfolds during unification and instance search. -/
@[reducible]
def step {P : Type v} {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} P Γ) (p : process.Proc) :
    StepOver Γ process.Proc :=
  ⟨(process.expose p).1, (process.expose p).2, process.update p⟩

/-- Build a process from a state space and a step-protocol assignment. This is
the `StepOver`-shaped constructor inverse to `ProcessOver.step`; both round
trips hold definitionally (`step_ofStep`, `ofStep_step`).

Reducible so that it unfolds during unification and instance search. -/
@[reducible]
def ofStep {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (Proc : Type v) (step : Proc → StepOver Γ Proc) : ProcessOver.{v, w, w₂} Proc Γ :=
  PFunctor.DynSystem.mk'
    (fun p => ⟨(step p).spec, (step p).semantics⟩)
    (fun p => (step p).next)

@[simp] theorem step_ofStep
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (Proc : Type v) (f : Proc → StepOver Γ Proc) :
    (ofStep Proc f).step = f := rfl

@[simp] theorem ofStep_step
    {P : Type v} {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} P Γ) :
    ofStep process.Proc process.step = process := rfl

/-- Processes with pointwise-equal step assignments on the same state space are
equal. -/
theorem ofStep_congr
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Proc : Type v} {f g : Proc → StepOver Γ Proc}
    (h : ∀ p, f p = g p) : ofStep Proc f = ofStep Proc g :=
  congrArg _ (funext h)

/--
Map the node-local context carried by a process along a realized context
morphism.

This changes only the metadata exposed at each step. The residual state space
and transition structure are preserved.
-/
def mapContext
    {P : Type v}
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (f : Interaction.Spec.Node.ContextHom Γ Δ)
    (process : ProcessOver P Γ) : ProcessOver P Δ :=
  ofStep process.Proc fun p => (process.step p).mapContext f

/--
Binary-choice interleaving of two processes with different node contexts.

Given processes `p₁` over `Γ₁` and `p₂` over `Γ₂`, context morphisms mapping
each into a common target context `Δ`, and a scheduler decoration in `Δ` for
the `ULift Bool` choice node, produce a single `ProcessOver Δ` whose state
space is `p₁.Proc × p₂.Proc`.

At each step, a scheduler node chooses left (`true`) or right (`false`), then
the selected subprocess's step protocol runs with its decoration mapped into
`Δ`. Only the selected component of the product state advances.
-/
def interleave
    {P₁ P₂ : Type v}
    {Γ₁ : Interaction.Spec.Node.Context.{w, w₂}}
    {Γ₂ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁)
    (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂ Δ)
    (schedulerCtx : Δ (ULift.{w} Bool)) : ProcessOver.{v, w, w₂} (P₁ × P₂) Δ :=
  ofStep (p₁.Proc × p₂.Proc) fun (s₁, s₂) =>
    let step₁ := p₁.step s₁
    let step₂ := p₂.step s₂
    { spec := .node (ULift.{w} Bool) fun
        | ⟨true⟩ => step₁.spec
        | ⟨false⟩ => step₂.spec
      semantics :=
        ⟨schedulerCtx, fun
          | ⟨true⟩ => PFunctor.FreeM.Displayed.Decoration.map f₁ step₁.spec step₁.semantics
          | ⟨false⟩ => PFunctor.FreeM.Displayed.Decoration.map f₂ step₂.spec step₂.semantics⟩
      next := fun
        | ⟨⟨true⟩, tr⟩ => (step₁.next tr, s₂)
        | ⟨⟨false⟩, tr⟩ => (s₁, step₂.next tr) }

/-- Post-composing `mapContext g` distributes over `interleave`: the result is
the same interleaving with each injection pre-composed by `g`. -/
theorem mapContext_interleave
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Δ Δ' : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂ Δ)
    (sched : Δ (ULift.{w} Bool))
    (g : Interaction.Spec.Node.ContextHom Δ Δ') :
    (p₁.interleave p₂ f₁ f₂ sched).mapContext g =
      p₁.interleave p₂
        (Interaction.Spec.Node.ContextHom.comp g f₁)
        (Interaction.Spec.Node.ContextHom.comp g f₂)
        (g _ sched) := by
  simp only [mapContext, interleave, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  simp only [PFunctor.FreeM.liftBind_eq]
  rw [PFunctor.FreeM.Displayed.Decoration.map_lift_bind]
  dsimp only
  congr 1; funext ⟨b⟩
  cases b <;> dsimp
  · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        g f₂ _ _
  · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        g f₁ _ _

/-- Pre-composing both operands with `mapContext` distributes into the
`interleave` injections via `ContextHom.comp`. -/
theorem interleave_mapContext
    {P₁ P₂ : Type v}
    {Γ₁ Γ₁' Γ₂ Γ₂' Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₁ : Interaction.Spec.Node.ContextHom Γ₁ Γ₁')
    (g₂ : Interaction.Spec.Node.ContextHom Γ₂ Γ₂')
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁' Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂' Δ)
    (sched : Δ (ULift.{w} Bool)) :
    (p₁.mapContext g₁).interleave (p₂.mapContext g₂) f₁ f₂ sched =
      p₁.interleave p₂
        (Interaction.Spec.Node.ContextHom.comp f₁ g₁)
        (Interaction.Spec.Node.ContextHom.comp f₂ g₂)
        sched := by
  simp only [mapContext, interleave, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b <;> dsimp
    · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        f₂ g₂ _ _
    · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        f₁ g₁ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

/-- Specialization of `interleave_mapContext` when only the left operand
is pre-composed with `mapContext`. -/
theorem interleave_mapContext_left
    {P₁ P₂ : Type v}
    {Γ₁ Γ₁' Γ₂ Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₁ : Interaction.Spec.Node.ContextHom Γ₁ Γ₁')
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁' Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂ Δ)
    (sched : Δ (ULift.{w} Bool)) :
    (p₁.mapContext g₁).interleave p₂ f₁ f₂ sched =
      p₁.interleave p₂
        (Interaction.Spec.Node.ContextHom.comp f₁ g₁)
        f₂
        sched := by
  simp only [mapContext, interleave, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b <;> dsimp
    exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        f₁ g₁ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

/-- Specialization of `interleave_mapContext` when only the right operand
is pre-composed with `mapContext`. -/
theorem interleave_mapContext_right
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Γ₂' Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₂ : Interaction.Spec.Node.ContextHom Γ₂ Γ₂')
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂' Δ)
    (sched : Δ (ULift.{w} Bool)) :
    p₁.interleave (p₂.mapContext g₂) f₁ f₂ sched =
      p₁.interleave p₂
        f₁
        (Interaction.Spec.Node.ContextHom.comp f₂ g₂)
        sched := by
  simp only [mapContext, interleave, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b <;> dsimp
    exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.Spec.basePFunctor) (α := PUnit.{w+1})
        f₂ g₂ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

/--
The wiring lens implementing scheduler-tagged interleaving: at a pair of
decorated step specs, the position is one `ULift Bool` scheduler node whose
branches are the two specs with decorations mapped into the common context,
and a transcript of that node projects back to the chosen side's transcript.

`interleave` is the `wrap` of `choiceProd` along this lens
(`interleave_eq_wrap_choiceProd`).
-/
def interleaveLens
    {Γ₁ : Interaction.Spec.Node.Context.{w, w₂}}
    {Γ₂ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂ Δ)
    (schedulerCtx : Δ (ULift.{w} Bool)) :
    PFunctor.Lens
      (PFunctor.prod (StepOver.toPFunctor Γ₁) (StepOver.toPFunctor Γ₂))
      (StepOver.toPFunctor Δ) where
  toFunA := fun (a₁, a₂) =>
    ⟨.node (ULift.{w} Bool) fun
        | ⟨true⟩ => a₁.1
        | ⟨false⟩ => a₂.1,
      ⟨schedulerCtx, fun
        | ⟨true⟩ => PFunctor.FreeM.Displayed.Decoration.map f₁ a₁.1 a₁.2
        | ⟨false⟩ => PFunctor.FreeM.Displayed.Decoration.map f₂ a₂.1 a₂.2⟩⟩
  toFunB := fun (_, _) => fun
    | ⟨⟨true⟩, tr⟩ => .inl tr
    | ⟨⟨false⟩, tr⟩ => .inr tr

/-- `interleave` factors through the dynamical-system layer: it is the
asynchronous choice `choiceProd` of the two processes, wrapped along the
scheduler wiring lens `interleaveLens`. -/
theorem interleave_eq_wrap_choiceProd
    {P₁ P₂ : Type v}
    {Γ₁ : Interaction.Spec.Node.Context.{w, w₂}}
    {Γ₂ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁)
    (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.Spec.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.Spec.Node.ContextHom Γ₂ Δ)
    (schedulerCtx : Δ (ULift.{w} Bool)) :
    p₁.interleave p₂ f₁ f₂ schedulerCtx
      = PFunctor.DynSystem.wrap (interleaveLens f₁ f₂ schedulerCtx)
          (PFunctor.DynSystem.choiceProd p₁ p₂) := by
  refine Eq.trans (ofStep_congr fun (s₁, s₂) => ?_)
    (ofStep_step (PFunctor.DynSystem.wrap (interleaveLens f₁ f₂ schedulerCtx)
      (PFunctor.DynSystem.choiceProd p₁ p₂)))
  change _ = StepOver.mk _ _ _
  refine congrArg (StepOver.mk _ _) ?_
  funext tr
  obtain ⟨⟨b⟩, tail⟩ := tr
  cases b <;> rfl

/--
A stable external label for each complete step transcript of a process: the
dynamical-system `EventMap` at the step polynomial, where a transition is a
complete step transcript.

The point of an `EventMap` is to attach one comparison-friendly label to a
whole step, independently of how much internal sequential structure that step
contains.
-/
abbrev EventMap {P : Type v} {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} P Γ) (Event : Type w₃) :=
  PFunctor.DynSystem.EventMap process Event

/--
A stable ticket for each complete step transcript of a process: the
dynamical-system `Tickets` at the step polynomial.

Tickets are the intended handles for fairness and liveness: instead of talking
about unstable frontier events whose types change from state to state, later
semantic layers can talk about these stable identifiers.
-/
abbrev Tickets {P : Type v} {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} P Γ) (Ticket : Type w₃) :=
  PFunctor.DynSystem.Tickets process Ticket

/--
`TranscriptRel left right` relates concrete process steps: each argument
contains the source process state together with the complete transcript chosen
at that state. It specializes dynamical-system `StepRel` to the step
polynomial; including the source states lets relations inspect the contexts in
which dependent transcripts are available.

This is the generic step-matching interface consumed by refinement. No
controller or observation structure is assumed here; those
become special cases once the surrounding contexts are projected into
`StepContext`.
-/
abbrev TranscriptRel
    {P₁ P₂ : Type v}
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (left : ProcessOver P₁ Γ) (right : ProcessOver P₂ Δ) :=
  PFunctor.DynSystem.StepRel left right

namespace TranscriptRel

/-- The permissive step relation that accepts every pair of concrete process
steps. -/
abbrev top
    {P₁ P₂ : Type v}
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver P₁ Γ} {right : ProcessOver P₂ Δ} :
    TranscriptRel left right :=
  PFunctor.DynSystem.StepRel.top

/-- Reverse a step-matching relation by flipping its two transcript
arguments. -/
abbrev reverse
    {P₁ P₂ : Type v}
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver P₁ Γ} {right : ProcessOver P₂ Δ}
    (rel : TranscriptRel left right) :
    TranscriptRel right left :=
  PFunctor.DynSystem.StepRel.reverse rel

/-- Conjunction of step-matching relations. -/
abbrev inter
    {P₁ P₂ : Type v}
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver P₁ Γ} {right : ProcessOver P₂ Δ}
    (first second : TranscriptRel left right) :
    TranscriptRel left right :=
  PFunctor.DynSystem.StepRel.inter first second

end TranscriptRel

/--
`ProcessOver.Labeled` is a process equipped with a stable external event label
for each complete step transcript: the dynamical-system `Labeled` bundle at the
step polynomial. The underlying process is `Labeled.toProcess`.
-/
-- The process state/message universes and the event-label universe are independent.
@[nolint checkUnivs]
abbrev Labeled (Γ : Interaction.Spec.Node.Context.{w, w₂}) :=
  PFunctor.DynSystem.Labeled.{v} (StepOver.toPFunctor Γ)

/-- The underlying process of a labeled process. -/
abbrev Labeled.toProcess {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (labeled : Labeled Γ) : ProcessOver labeled.State Γ :=
  labeled.toMachine.behavior

/--
`ProcessOver.Ticketed` is a process equipped with a stable ticket for each
complete step transcript: the dynamical-system `Ticketed` bundle at the step
polynomial. The underlying process is `Ticketed.toProcess`.

These tickets are the obligation identifiers used by the fairness and liveness
layers.
-/
-- The process state/message universes and the ticket universe are independent.
@[nolint checkUnivs]
abbrev Ticketed (Γ : Interaction.Spec.Node.Context.{w, w₂}) :=
  PFunctor.DynSystem.Ticketed.{v} (StepOver.toPFunctor Γ)

/-- The underlying process of a ticketed process. -/
abbrev Ticketed.toProcess {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : Ticketed Γ) : ProcessOver ticketed.State Γ :=
  ticketed.toMachine.behavior

/--
`ProcessOver.SafetySpec Γ` is a process-level safety-verification problem:
dynamics, initial states, ambient assumptions, and a safety predicate. The
underlying process is `SafetySpec.toProcess`.
-/
abbrev SafetySpec (Γ : Interaction.Spec.Node.Context.{w, w₂}) :=
  PFunctor.DynSystem.SafetySpec.{v} (StepOver.toPFunctor Γ)

/-- The underlying process of a verification-oriented system. -/
abbrev SafetySpec.toProcess {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : SafetySpec Γ) : ProcessOver system.State Γ :=
  system.toMachine.behavior

/-- The residual state space of a system's underlying process. -/
abbrev SafetySpec.Proc {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : SafetySpec Γ) : Type _ :=
  system.toProcess.Proc

/-- The step protocol of a system's underlying process. -/
abbrev SafetySpec.step {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : SafetySpec Γ) (p : system.Proc) : StepOver Γ system.Proc :=
  system.toProcess.step p

/-! ### Polynomial-coalgebra behavior

`StepOver.toPFunctor Γ` (from S3) exhibits one episode of `Γ`-decorated
interaction as a polynomial functor. Its terminal coalgebra is the M-type
`PFunctor.M (StepOver.toPFunctor Γ)`: the type of all possibly-infinite
trees of step protocols.

Since a `ProcessOver Γ` is a dynamical system over this polynomial, the
terminal-coalgebra semantics comes directly from the dynamical-system layer:
`process.behavior : process.Proc → Behavior Γ` is `PFunctor.DynSystem.behavior`,
its defining equation is `DynSystem.dest_behavior`, the "bisimulation by
uniqueness" principle is `DynSystem.behavior_unique`, and equality of behavior
trees is the canonical observational equivalence `DynSystem.ObsEq`. A
same-interface `DynSystem.IsSimulation` implies this equality; mutual safety
refinement instead expresses two-way existential trace matching and is not a
coalgebraic bisimulation. -/

/-- The terminal coalgebra of `StepOver.toPFunctor Γ`: the type of
possibly-infinite trees of `Γ`-decorated step protocols. Each such tree
records one complete observable behavior of a `ProcessOver Γ` from a
chosen seed state, the target of `PFunctor.DynSystem.behavior`. -/
abbrev Behavior (Γ : Interaction.Spec.Node.Context.{w, w₂}) :
    Type (max (w + 1) w₂) :=
  PFunctor.M (StepOver.toPFunctor Γ)

end ProcessOver

/--
The closed-world specialization of `StepOver`.

Here the node context is fixed to `StepContext Party`, so every node carries
the usual controller-path and local-view data for that party universe.
-/
abbrev Step (Party : Type u) (P : Type v) :=
  StepOver (StepContext Party) P

namespace Step

/-- Recursively walk a transcript alongside its decoration, concatenating the
controller list recorded at each visited node into the accumulated path.

Auxiliary for `Step.controllerPath`. -/
private def controllerPathAux {Party : Type u} :
    {spec : Interaction.Spec.{w}} →
    PFunctor.FreeM.Displayed.Decoration (StepContext Party) spec →
    PFunctor.FreeM.Path spec →
    List Party
  | .done, _, _ => []
  | .node _ _, ⟨node, restSemantics⟩, ⟨x, tail⟩ =>
      node.controllers x ++ controllerPathAux (restSemantics x) tail

/--
`controllerPath step tr` is the controller sequence exposed by the concrete
step transcript `tr`.

Every visited node contributes the controller list recorded for the chosen
move at that node. These per-node contributions are concatenated along the
whole step transcript.

So if a step internally consists of, say, "the scheduler chooses a branch,
then Alice chooses a payload", the controller path records both pieces in
order.
-/
def controllerPath {Party : Type u} {P : Type v} (step : Step Party P) :
    PFunctor.FreeM.Path step.spec → List Party :=
  fun tr => controllerPathAux step.semantics tr

/--
`currentController? step tr` is the head of the controller path exposed by the
concrete transcript `tr`, if such a controller exists.

This is the most immediate "who controlled this step?" projection. It is only
the first controller because one step may internally contain several
controlled subchoices.
-/
def currentController? {Party : Type u} {P : Type v} (step : Step Party P)
    (tr : PFunctor.FreeM.Path step.spec) : Option Party :=
  step.controllerPath tr |>.head?
end Step

namespace StepOver

/--
Closed-world controller-path projection for a `StepOver` specialized to
`StepContext Party`.

This bridge keeps the old dot-notation ergonomics after the `StepOver`
cutover: downstream closed-world code can still write
`(process.step p).controllerPath tr`.
-/
abbrev controllerPath {Party : Type u} {P : Type v}
    (step : StepOver (StepContext Party) P) :
    PFunctor.FreeM.Path step.spec → List Party :=
  Step.controllerPath step

/--
Closed-world current-controller projection for a `StepOver` specialized to
`StepContext Party`.
-/
abbrev currentController? {Party : Type u} {P : Type v}
    (step : StepOver (StepContext Party) P)
    (tr : PFunctor.FreeM.Path step.spec) : Option Party :=
  Step.currentController? step tr

end StepOver

/--
The closed-world specialization of `ProcessOver`, with residual state space
`P`.

This is the process type consumed by the current execution, run, observation,
refinement, fairness, and liveness layers.
-/
-- The `Party` universe and the process's state/message universes are independent.
@[nolint checkUnivs]
abbrev Process (P : Type v) (Party : Type u) :=
  ProcessOver P (StepContext Party)

namespace Process

/--
A stable external label for each complete closed-world process step.
-/
abbrev EventMap {P : Type v} {Party : Type u}
    (process : Process P Party) (Event : Type w₂) :=
  ProcessOver.EventMap process Event

/--
A stable ticket for each complete closed-world process step.
-/
abbrev Tickets {P : Type v} {Party : Type u}
    (process : Process P Party) (Ticket : Type w₂) :=
  ProcessOver.Tickets process Ticket

/--
The closed-world specialization of `ProcessOver.TranscriptRel`.
-/
abbrev TranscriptRel {P₁ P₂ : Type v} {Party : Type u}
    (left : Process P₁ Party) (right : Process P₂ Party) :=
  ProcessOver.TranscriptRel left right

/--
`Process.Labeled` is a closed-world process together with a stable event label
for each complete step transcript.
-/
-- The `Party` universe and the event/process universes are independent.
@[nolint checkUnivs]
abbrev Labeled (Party : Type u) :=
  ProcessOver.Labeled (StepContext Party)

/--
`Process.Ticketed` is a closed-world process together with a stable ticket for
each complete step transcript.

These tickets are the obligation identifiers used later by the fairness and
liveness layers.
-/
-- The `Party` universe and the ticket/process universes are independent.
@[nolint checkUnivs]
abbrev Ticketed (Party : Type u) :=
  ProcessOver.Ticketed (StepContext Party)

/--
`Process.SafetySpec` is a closed-world process-level safety-verification
problem.

Its parent field `toProcess` is the dynamic semantics; the remaining fields are
verification metadata on top of that semantics:

* `init` marks initial residual states;
* `assumptions` records ambient assumptions on runs;
* `safe` is the state predicate to be established.

This keeps the semantic object and the proof obligations separate while still
bundling them in one place for refinement and liveness statements.
-/
-- The `Party` universe and the process's state/message universes are independent.
@[nolint checkUnivs]
abbrev SafetySpec (Party : Type u) :=
  ProcessOver.SafetySpec (StepContext Party)

end Process
end Concurrent
end Interaction
