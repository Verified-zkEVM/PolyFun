/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenTheory

/-!
# Sub-theories: which open systems a model allows

An `OpenTheory` says how open systems may be combined. It does not say which
open systems one is *allowed* to build. Every UC-style development needs that
second notion: a corruption model is a restriction on the machines a real
protocol may use, and an efficiency requirement is a restriction on the
machines anyone may use at all.

`SubTheory T` is that notion. It is a boundary-indexed membership predicate
on `T.Obj` together with proofs that membership survives the theory's
operations. Nothing here mentions corruption, probability, or cost: those are
instantiations, and the point of the abstraction is that they are the *same*
instantiation mechanism.

## Main definitions

* `SubTheory T` bundles `mem` with closure under `map`, `par`, and `wire`.
* `SubTheory.IsPlugClosed D` adds closure under `plug`. It is a separate class
  rather than a field because a theory with strict plug/wire factorization
  gets it for free (`isPlugClosed_of_hasPlugWireFactor`), while the concrete
  process model — which has no such factorization — must earn it.
* `SubTheory.IsStructural D` says `D` contains the structural generators, the
  unit and the identity wires.
* `SubTheory.top`, `SubTheory.inf`, and the order `≤`. `top` allows
  everything, so every statement relativized to `top` is the unrelativized
  statement. `inf` is how independent restrictions — a corruption model and an
  efficiency class — combine into one allowed-systems predicate.
* `SubTheory.generated G` is the smallest sub-theory containing the generators
  `G`, and `SubTheory.generated_le` is its induction principle.

## Why the closure fields are the interesting part

Read `mem` as "is implementable within some fixed resource discipline". Then
`mem_par` and `mem_wire` say that a network of implementable systems is itself
implementable — the property that composable-security frameworks normally
assume outright about their machine model, because it is stated globally over
networks and there is no finite obligation to discharge. Here the network is
built from four operations, so the assumption *is* four closure fields. That
is the whole reason to make the allowed class a first-class object rather than
a side condition.

`generated` and `generated_le` are the other half of the same idea. A protocol
class defined by its generators is a `generated` sub-theory, so proving every
member of it implementable reduces to proving the generators implementable and
supplying the closure fields once.

## Design notes

`mem` is a `Prop`, not data. A resource-bounded instantiation carries its
witness *inside* the proposition (`∃ a bound in the class, …`), exactly as
`StepClass.Hom` does one level down in `PolyFun/Realizability/`; making
membership proof-relevant would make `EmulatesWithin` proof-relevant too,
which is wrong.

`SubTheory` is deliberately the `OpenTheory`-level sibling of
`PFunctor.StepClass`: a bundled predicate plus its closure proofs, passed
explicitly rather than synthesized, with the optional structure split into
mixins and an order along which results transport. The two are meant to meet
at an instantiation of `mem` in terms of realizability, not to share code.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/--
`SubTheory T` picks out, at every boundary, which open systems of `T` are
allowed, subject to those systems being closed under the theory's composition
operations.

This is the formal counterpart of the nested sub-categories a UC development
fixes before stating any security property: one parameter naming the class of
systems a real protocol may be assembled from.

Closure under `plug` is *not* a field; see `SubTheory.IsPlugClosed`.
-/
structure SubTheory (T : OpenTheory.{u}) where
  /-- Which open systems at boundary `Δ` the sub-theory allows. -/
  mem : ∀ {Δ : PortBoundary}, T.Obj Δ → Prop
  /-- Allowed systems remain allowed under boundary adaptation. Adaptation
  changes only how a system presents its boundary, so no restriction worth
  the name can be broken by it. -/
  mem_map : ∀ {Δ₁ Δ₂ : PortBoundary} {W : T.Obj Δ₁} (φ : PortBoundary.Hom Δ₁ Δ₂),
    mem W → mem (T.map φ W)
  /-- Allowed systems are closed under parallel composition. -/
  mem_par : ∀ {Δ₁ Δ₂ : PortBoundary} {W₁ : T.Obj Δ₁} {W₂ : T.Obj Δ₂},
    mem W₁ → mem W₂ → mem (T.par W₁ W₂)
  /-- Allowed systems are closed under wiring one shared boundary. -/
  mem_wire : ∀ {Δ₁ Γ Δ₂ : PortBoundary} {W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
      {W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)},
    mem W₁ → mem W₂ → mem (T.wire W₁ W₂)

namespace SubTheory

/-- Allowed systems remain allowed under transport along a boundary
equivalence. -/
theorem mem_mapEquiv {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂) {W : T.Obj Δ₁} (hW : D.mem W) :
    D.mem (T.mapEquiv e W) :=
  D.mem_map e.toHom hW

/-! ### Closure under total closure -/

/--
`D.IsPlugClosed` states that plugging an allowed system against an allowed
context yields an allowed closed system.

This is a mixin rather than a `SubTheory` field for the same reason
`Observation.RespectsPlugComm` is split out of
`Observation.RespectsFactorization`: a theory whose `plug` factors through
`wire` gets it for free (`isPlugClosed_of_hasPlugWireFactor`), whereas the
process-backed `openTheory` — which instantiates only `OpenTheory.IsLawful`
— has to prove it directly. Splitting lets each model declare exactly the
strength it can honestly satisfy.
-/
class IsPlugClosed {T : OpenTheory.{u}} (D : SubTheory T) : Prop where
  /-- Closing an allowed system against an allowed context stays allowed. -/
  mem_plug : ∀ {Δ : PortBoundary} {W : T.Obj Δ} {K : T.Obj (PortBoundary.swap Δ)},
    D.mem W → D.mem K → D.mem (T.plug W K)

/-- In a theory with strict plug/wire factorization, `plug` is a composite of
`map` and `wire`, so every sub-theory is automatically plug-closed. This is
what keeps the free syntax models on the full relativized suite. -/
instance isPlugClosed_of_hasPlugWireFactor [OpenTheory.HasPlugWireFactor T]
    (D : SubTheory T) : D.IsPlugClosed where
  mem_plug hW hK := by
    rw [OpenTheory.plug_eq_wire]
    exact D.mem_map _ (D.mem_wire (D.mem_map _ hW) (D.mem_map _ hK))

/-- `close` is `plug` under the contextual-equivalence reading, so it inherits
closure verbatim. -/
theorem mem_close {D : SubTheory T} [D.IsPlugClosed] {Δ : PortBoundary}
    {W : T.Obj Δ} {K : T.Plug Δ} (hW : D.mem W) (hK : D.mem K) :
    D.mem (T.close W K) :=
  IsPlugClosed.mem_plug hW hK

/-! ### Containing the structural generators -/

/--
`D.IsStructural` states that `D` contains the two pieces of structure a
compact-closed theory supplies on its own: the unit and the identity wire at
every boundary.

These are the wires of a string diagram rather than machines in it, so any
class of systems meant to be closed under rewiring must contain them. It is a
class, and separate from `SubTheory`, because a theory need not have the
structure at all: `openTheory` has neither `OpenTheory.HasUnit` nor
`OpenTheory.HasIdWire` registered.
-/
class IsStructural {T : OpenTheory.{u}} [OpenTheory.HasUnit T] [OpenTheory.HasIdWire T]
    (D : SubTheory T) : Prop where
  /-- The monoidal unit is allowed. -/
  mem_unit : D.mem (OpenTheory.HasUnit.unit (T := T))
  /-- Every identity wire is allowed. -/
  mem_idWire : ∀ Γ : PortBoundary, D.mem (OpenTheory.HasIdWire.idWire (T := T) Γ)

/-! ### Order, top, and meet -/

/--
`D₁ ≤ D₂` says every system `D₁` allows is also allowed by `D₂`.

Relativized security statements are *antitone* in this order: allowing fewer
contexts is a weaker demand on the protocol. See `EmulatesWithin.mono`.
-/
@[expose]
def le (D₁ D₂ : SubTheory T) : Prop :=
  ∀ {Δ : PortBoundary} (W : T.Obj Δ), D₁.mem W → D₂.mem W

instance : LE (SubTheory T) := ⟨SubTheory.le⟩

/-- Build an inclusion of sub-theories from pointwise membership transfer. -/
theorem le_of_mem {D₁ D₂ : SubTheory T}
    (h : ∀ {Δ : PortBoundary} (W : T.Obj Δ), D₁.mem W → D₂.mem W) : D₁ ≤ D₂ := h

theorem le_refl (D : SubTheory T) : D ≤ D := fun _ hW => hW

theorem le_trans {D₁ D₂ D₃ : SubTheory T} (h₁₂ : D₁ ≤ D₂) (h₂₃ : D₂ ≤ D₃) : D₁ ≤ D₃ :=
  fun W hW => h₂₃ W (h₁₂ W hW)

/-- Transfer membership upward along the order. -/
theorem mem_of_le {D₁ D₂ : SubTheory T} (h : D₁ ≤ D₂) {Δ : PortBoundary} {W : T.Obj Δ}
    (hW : D₁.mem W) : D₂.mem W :=
  h W hW

/--
The sub-theory allowing everything.

Relativizing to `top` is a no-op: `EmulatesWithin.emulatesWithin_top_iff`
shows the relativized emulation judgment collapses to `Emulates`. This is what
makes the whole layer a conservative extension.
-/
@[expose]
def top (T : OpenTheory.{u}) : SubTheory T where
  mem := fun _ => True
  mem_map _ _ := trivial
  mem_par _ _ := trivial
  mem_wire _ _ := trivial

instance isPlugClosed_top (T : OpenTheory.{u}) : (top T).IsPlugClosed where
  mem_plug _ _ := trivial

instance isStructural_top (T : OpenTheory.{u}) [OpenTheory.HasUnit T] [OpenTheory.HasIdWire T] :
    (top T).IsStructural where
  mem_unit := trivial
  mem_idWire _ := trivial

theorem le_top (D : SubTheory T) : D ≤ top T := fun _ _ => trivial

@[simp]
theorem top_mem {Δ : PortBoundary} (W : T.Obj Δ) : (top T).mem W := trivial

/--
The intersection of two sub-theories.

This is how independent restrictions combine. A corruption model and a
resource bound are two unrelated reasons to disallow a system; their meet is
the class of systems allowed for both reasons, and it is a sub-theory because
each closure field holds componentwise.
-/
@[expose]
def inf (D₁ D₂ : SubTheory T) : SubTheory T where
  mem W := D₁.mem W ∧ D₂.mem W
  mem_map φ h := ⟨D₁.mem_map φ h.1, D₂.mem_map φ h.2⟩
  mem_par h₁ h₂ := ⟨D₁.mem_par h₁.1 h₂.1, D₂.mem_par h₁.2 h₂.2⟩
  mem_wire h₁ h₂ := ⟨D₁.mem_wire h₁.1 h₂.1, D₂.mem_wire h₁.2 h₂.2⟩

instance isPlugClosed_inf (D₁ D₂ : SubTheory T) [D₁.IsPlugClosed] [D₂.IsPlugClosed] :
    (inf D₁ D₂).IsPlugClosed where
  mem_plug h₁ h₂ := ⟨IsPlugClosed.mem_plug h₁.1 h₂.1, IsPlugClosed.mem_plug h₁.2 h₂.2⟩

instance isStructural_inf [OpenTheory.HasUnit T] [OpenTheory.HasIdWire T]
    (D₁ D₂ : SubTheory T) [D₁.IsStructural] [D₂.IsStructural] : (inf D₁ D₂).IsStructural where
  mem_unit := ⟨IsStructural.mem_unit, IsStructural.mem_unit⟩
  mem_idWire Γ := ⟨IsStructural.mem_idWire Γ, IsStructural.mem_idWire Γ⟩

@[simp]
theorem inf_mem {D₁ D₂ : SubTheory T} {Δ : PortBoundary} {W : T.Obj Δ} :
    (inf D₁ D₂).mem W ↔ D₁.mem W ∧ D₂.mem W :=
  Iff.rfl

theorem inf_le_left (D₁ D₂ : SubTheory T) : inf D₁ D₂ ≤ D₁ := fun _ h => h.1

theorem inf_le_right (D₁ D₂ : SubTheory T) : inf D₁ D₂ ≤ D₂ := fun _ h => h.2

theorem le_inf {D D₁ D₂ : SubTheory T} (h₁ : D ≤ D₁) (h₂ : D ≤ D₂) : D ≤ inf D₁ D₂ :=
  fun W hW => ⟨h₁ W hW, h₂ W hW⟩

/-! ### The sub-theory generated by a set of generators -/

/--
`Generated T G W` says `W` can be assembled from generators satisfying `G`
using only the operations of `T`.

This is the inductive counterpart of "the smallest sub-theory containing `G`",
and it is the shape a protocol class actually takes in practice: one names the
allowed building blocks and takes everything wired together from them.

The `plug` constructor is included, so `SubTheory.generated G` is plug-closed
unconditionally — no factorization law is needed to build a closed system, only
to take one apart.
-/
inductive Generated (T : OpenTheory.{u}) (G : ∀ (Δ : PortBoundary), T.Obj Δ → Prop) :
    {Δ : PortBoundary} → T.Obj Δ → Prop where
  /-- A generator is generated. -/
  | base {Δ : PortBoundary} {W : T.Obj Δ} : G Δ W → Generated T G W
  /-- Boundary adaptation of a generated system is generated. -/
  | map {Δ₁ Δ₂ : PortBoundary} {W : T.Obj Δ₁} (φ : PortBoundary.Hom Δ₁ Δ₂) :
      Generated T G W → Generated T G (T.map φ W)
  /-- A parallel composite of generated systems is generated. -/
  | par {Δ₁ Δ₂ : PortBoundary} {W₁ : T.Obj Δ₁} {W₂ : T.Obj Δ₂} :
      Generated T G W₁ → Generated T G W₂ → Generated T G (T.par W₁ W₂)
  /-- A wiring of generated systems is generated. -/
  | wire {Δ₁ Γ Δ₂ : PortBoundary} {W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
      {W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)} :
      Generated T G W₁ → Generated T G W₂ → Generated T G (T.wire W₁ W₂)
  /-- Plugging generated systems together is generated. -/
  | plug {Δ : PortBoundary} {W : T.Obj Δ} {K : T.Obj (PortBoundary.swap Δ)} :
      Generated T G W → Generated T G K → Generated T G (T.plug W K)

/--
The smallest sub-theory whose members include every generator satisfying `G`.

Its closure fields are literally the constructors of `Generated`.

The generator predicate takes its boundary *explicitly*, unlike
`SubTheory.mem`. A predicate whose leading argument is implicit gets its
implicits inserted eagerly when it is passed as an argument, which leaves the
boundary as an unsolvable metavariable at every use site; `mem` escapes this
only because it is a projection applied to a known `SubTheory`.
-/
@[expose]
def generated (T : OpenTheory.{u}) (G : ∀ (Δ : PortBoundary), T.Obj Δ → Prop) : SubTheory T where
  mem W := Generated T G W
  mem_map φ h := .map φ h
  mem_par h₁ h₂ := .par h₁ h₂
  mem_wire h₁ h₂ := .wire h₁ h₂

instance isPlugClosed_generated (T : OpenTheory.{u})
    (G : ∀ (Δ : PortBoundary), T.Obj Δ → Prop) : (generated T G).IsPlugClosed where
  mem_plug h₁ h₂ := .plug h₁ h₂

/-- Every generator belongs to the sub-theory it generates. -/
theorem mem_generated_of_gen (T : OpenTheory.{u}) (G : ∀ (Δ : PortBoundary), T.Obj Δ → Prop)
    {Δ : PortBoundary} (W : T.Obj Δ) (hW : G Δ W) : (generated T G).mem W :=
  .base hW

/--
**The induction principle for generated sub-theories.**

If every generator is allowed by `D`, then everything assembled from
generators is allowed by `D`. Contrapositively, this is the only way a
generated class can fail a property closed under the operations: one of its
generators must already fail it.

Instantiating `D` at a resource-bounded class turns the usual "a network of
efficient machines is efficient" assumption into a finite obligation — the
generators, plus the four closure fields carried by `D` itself.
-/
theorem generated_le {G : ∀ (Δ : PortBoundary), T.Obj Δ → Prop} (D : SubTheory T)
    [D.IsPlugClosed] (hG : ∀ (Δ : PortBoundary) (W : T.Obj Δ), G Δ W → D.mem W) :
    generated T G ≤ D := by
  intro Δ W hW
  induction hW with
  | base hg => exact hG _ _ hg
  | map _ _ ih => exact D.mem_map _ ih
  | par _ _ ih₁ ih₂ => exact D.mem_par ih₁ ih₂
  | wire _ _ ih₁ ih₂ => exact D.mem_wire ih₁ ih₂
  | plug _ _ ih₁ ih₂ => exact IsPlugClosed.mem_plug ih₁ ih₂

/-- The generated sub-theory is monotone in its generators. -/
theorem generated_mono {G₁ G₂ : ∀ (Δ : PortBoundary), T.Obj Δ → Prop}
    (h : ∀ (Δ : PortBoundary) (W : T.Obj Δ), G₁ Δ W → G₂ Δ W) :
    generated T G₁ ≤ generated T G₂ :=
  generated_le _ fun Δ W hW => Generated.base (h Δ W hW)

end SubTheory

end UC
end Interaction
