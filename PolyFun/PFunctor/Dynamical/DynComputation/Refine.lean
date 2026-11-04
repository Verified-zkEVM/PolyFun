/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Charge
public import PolyFun.PFunctor.Handler.Stateful.Charge

/-!
# Machines refining programs through stateful packages

A machine `L` over the interface `M` *refines* a program family `x` over `E` through a stateful
package `h : Stateful (FreeM M) S E` from the states `σ₀` (`RefinesVia`) when `L` implements the
run of `x g` through `h` from `σ₀ g`. This is the machine end of a chain of cost layers: a
specification over `E`, implemented by an algorithm or machine model over `M`, executed by `L`.

* **Transfer.** If `h` answers each call within its price (`Stateful.WithinCharge`) and every
  program of the family is within budget, the machine is within budget from every initial state
  (`RefinesVia.isChargeBound`). Prices of the specification become step counts, cycles or gate
  counts of the machine without unfolding either.
* **Construction.** The machine of the run refines it (`refinesVia_ofFreeM`), and any machine in
  lockstep simulation with that run does too (`RefinesVia.of_isSimulation`).
* **Composition.** A machine refining the outer package's programs through an inner package refines
  the original family through the linked package (`RefinesVia.link`), and the certificates compose
  along `link` (`Stateful.WithinCharge.link`).

The transfer is exact for machines that answer a call with a bounded run of visible operations.
A machine that takes several internal steps per call makes those steps visible as calls of its own
interface, as `ITree.toDynComputation` does for silent steps.
-/

@[expose] public section

universe u v uE uM uI uG w

namespace PFunctor.DynSystem.DynComputation

open PFunctor.Handler

variable {S T : Type u} {E : PFunctor.{uE, u}} {M : PFunctor.{uM, u}} {I : PFunctor.{uI, u}}
  {G : Type uG} {α : Type u}

/-- The machine `L` implements, from each input `g`, the run of `x g` through the stateful
package `h` from the state `σ₀ g`. -/
def RefinesVia (L : DynComputation.{v} M G (α × S)) (h : Stateful (FreeM M) S E)
    (x : G → FreeM E α) (σ₀ : G → S) : Prop :=
  L.Implements fun g => h.run (x g) (σ₀ g)

/-- The machine of the run refines it. -/
theorem refinesVia_ofFreeM (h : Stateful (FreeM M) S E) (x : G → FreeM E α) (σ₀ : G → S) :
    (ofFreeM fun g => h.run (x g) (σ₀ g)).RefinesVia h x σ₀ :=
  implements_ofFreeM _

/-- A machine in lockstep simulation with the machine of the run refines it. -/
theorem RefinesVia.of_isSimulation (L : DynComputation.{v} M G (α × S))
    (h : Stateful (FreeM M) S E) (x : G → FreeM E α) (σ₀ : G → S)
    (R : L.State → FreeM M (α × S) → Prop)
    (simulation : IsSimulation L.toDynSystem
      (ofFreeM fun g => h.run (x g) (σ₀ g)).toDynSystem R)
    (init_rel : ∀ g, R (L.init g) (h.run (x g) (σ₀ g))) :
    L.RefinesVia h x σ₀ :=
  implements_of_isSimulation L _ R simulation init_rel

/-- **Composition through a linked package.** A machine refining the outer package's runs of `x`
through an inner package refines `x` through the linked package, after reassociating the state. -/
theorem RefinesVia.link {outer : Stateful (FreeM M) S E} {inner : Stateful (FreeM I) T M}
    {x : G → FreeM E α} {σ₀ : G → S} {τ₀ : G → T}
    {L : DynComputation.{v} I G ((α × S) × T)}
    (hL : L.RefinesVia inner (fun g => outer.run (x g) (σ₀ g)) τ₀) :
    (L.mapResult fun r : (α × S) × T => (r.1.1, (r.1.2, r.2))).RefinesVia (outer.link inner) x
      (fun g => (σ₀ g, τ₀ g)) := by
  intro g
  have h := hL.mapResult (fun r : (α × S) × T => (r.1.1, (r.1.2, r.2))) g
  simp only at h ⊢
  rw [Stateful.run_link]
  exact h

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
  [CanonicallyOrderedAdd ω]

/-- **Transfer to the machine.** If the package answers each call within its price and each
program of the family is within budget `B`, the refining machine is within `B` from every initial
state. -/
theorem RefinesVia.isChargeBound {L : DynComputation.{v} M G (α × S)}
    {h : Stateful (FreeM M) S E} {x : G → FreeM E α} {σ₀ : G → S} {c : E.A → ω} {d : M.A → ω}
    {B : ω} (hL : L.RefinesVia h x σ₀) (hh : h.WithinCharge d c)
    (hx : ∀ g, (x g).IsChargeBound c B) (g : G) : L.IsChargeBound d B (L.init g) :=
  (Implements.isChargeBound_init_iff hL g).2 (hh.run (hx g) (σ₀ g))

end PFunctor.DynSystem.DynComputation
