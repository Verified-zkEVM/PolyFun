/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Cartesian
import Batteries.Tactic.Lint

/-!
# The vertical–cartesian factorization system on lenses

Following Spivak–Niu, *Polynomial Functors: A General Theory of Interaction*
(§5.5, Prop 5.51–5.53), the category `Poly` with lens morphisms carries an
orthogonal factorization system whose two classes are:

* **cartesian** lenses — every backward fiber `toFunB a` is a bijection
  (already `PFunctor.Lens.IsCartesian`); and
* **vertical** lenses — the forward map on positions `toFunA` is a bijection
  (`IsVertical`).

Every lens `l : Lens P Q` factors as a vertical lens followed by a cartesian
lens through the middle object `factorMid l = Σ_{i} y^{Q[l.toFunA i]}`:

`P --factorVert--> factorMid l --factorCart--> Q`,  `factorCart ⨟ factorVert = l`.

The two classes meet in the isomorphisms: a lens is a `PFunctor.Lens.Equiv`
exactly when it is both vertical (`toFunA` bijective) and cartesian (`toFunB a`
bijective), as recorded in `PFunctor/Lens/Cartesian.lean`. Building that
equivalence from the two bijections, together with the `+ / × / ⊗ / ◃` closure
of both classes (Spivak–Niu Prop 5.63, 6.88), is left to a follow-on; this file
supplies the definitions and the factorization itself.

The downstream consumer is the `LawfulSubSpec` theory in VCVio, where the
cartesian leg is the probability-preserving part of a sub-spec embedding.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **vertical** when its forward map on positions
`l.toFunA` is a bijection. Together with `IsCartesian` this forms an orthogonal
factorization system on `Poly`; the two classes meet in the isomorphisms. -/
def IsVertical (l : Lens P Q) : Prop :=
  Function.Bijective l.toFunA

namespace IsVertical

@[simp]
theorem id (P : PFunctor.{uA, uB}) : (Lens.id P).IsVertical :=
  Function.bijective_id

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) : (l₁ ∘ₗ l₂).IsVertical :=
  show Function.Bijective (l₁.toFunA ∘ l₂.toFunA) from Function.Bijective.comp h₁ h₂

end IsVertical

/-! ## The factorization -/

/-- The middle object of the vertical–cartesian factorization of `l`:
`Σ_{i : P.A} y^{Q.B (l.toFunA i)}`. It shares the positions of `P` and the
directions of `Q` (pulled along `l.toFunA`). -/
def factorMid (l : Lens P Q) : PFunctor.{uA₁, uB₂} :=
  ⟨P.A, fun i => Q.B (l.toFunA i)⟩

/-- The vertical leg `P ⇆ factorMid l`: identity on positions, `l.toFunB` on
directions. -/
def factorVert (l : Lens P Q) : Lens P (factorMid l) :=
  (fun i => i) ⇆ l.toFunB

/-- The cartesian leg `factorMid l ⇆ Q`: `l.toFunA` on positions, identity on
each direction fiber. -/
def factorCart (l : Lens P Q) : Lens (factorMid l) Q :=
  l.toFunA ⇆ (fun _ d => d)

/-- The factorization recovers the original lens. -/
@[simp]
theorem factorCart_comp_factorVert (l : Lens P Q) :
    factorCart l ∘ₗ factorVert l = l := rfl

/-- The vertical leg is vertical. -/
theorem isVertical_factorVert (l : Lens P Q) : (factorVert l).IsVertical :=
  Function.bijective_id

/-- The cartesian leg is cartesian. -/
theorem isCartesian_factorCart (l : Lens P Q) : (factorCart l).IsCartesian :=
  fun _ => Function.bijective_id

end Lens

end PFunctor
