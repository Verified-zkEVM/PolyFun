/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.Bang
public import Mathlib.Data.Multiset.Functor

/-!
# The comonad of a monad on directions

For a lawful monad `M`, the polynomial `dirMonad M P` has the positions of `P` and, at a position
`a`, the computations `M (P.B a)` as directions. On the category of lenses `dirMonad M` is a
comonad: the counit sends a direction to `pure` of it and the comultiplication sends a computation
of computations to its join. A lens `dirMonad M P ⇆ Q` is a forward map on positions with a
backward map sending a direction of `Q` to a computation in `M` of a direction of `P`, so the
co-Kleisli category of `dirMonad M` is the category of lenses with `M`-valued backward maps, whose
composite binds the backward maps. This construction is folklore; Smithe (*Mathematical
Foundations for a Compositional Account of the Bayesian Brain*, thesis, Oxford, 2022,
Remark 6.2.19) attributes it to Spivak.

At `M := Multiset` the comonad is the multiset exponential `bang`. The Seely isomorphisms and the
commutative comonoid structure of `bang` use the additive structure of multisets, which a general
monad does not have. The weighted exponential `bangW` has finitely supported weightings as
directions; `Finsupp` has no `Monad` instance, so `bangW` is not an instance of this construction.

Since `M : Type uB → Type uB`, the directions of `P` and of `dirMonad M P` lie in the same
universe `uB`; the lenses below therefore relate polynomials whose directions lie in `uB`.

## Main definitions

* `dirMonad` — the polynomial of `M`-computations of directions;
* `Lens.dirMonadMap`, `Lens.dirMonadCounit`, `Lens.dirMonadComult` — its action on lenses, counit
  and comultiplication;
* `LensCat.dirMonadFunctor`, `LensCat.dirMonadComonad` — the comonad on `LensCat`;
* `LensCat.dirMonadMultisetIso` — the isomorphism of comonads `dirMonadComonad Multiset ≅
  bangComonad`.

## Main results

* `Lens.dirMonadMap_id`, `Lens.dirMonadMap_comp`, `Lens.dirMonadCounit_natural`,
  `Lens.dirMonadComult_natural`, `Lens.dirMonadCounit_comult`, `Lens.dirMonadMap_counit_comult`,
  `Lens.dirMonadComult_coassoc` — the comonad laws;
* `Lens.dirMonad_cokleisli_comp` — the co-Kleisli composite binds the backward maps.
-/

@[expose] public section

universe uA uB uA₁ uA₂ uA₃

open CategoryTheory

namespace PFunctor

variable (M : Type uB → Type uB)

/-- The polynomial of `M`-computations of directions: the positions of `P`, and at a position the
computations in `M` of directions of `P` at it. The monad `M` acts on the universe of directions
of `P`. -/
abbrev dirMonad (P : PFunctor.{uA, uB}) : PFunctor.{uA, uB} := ⟨P.A, fun a => M (P.B a)⟩

namespace Lens

variable {M} [Monad M] [LawfulMonad M]
variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

/-- The action of `dirMonad M` on a lens: the backward map is mapped over the computation. -/
def dirMonadMap (l : Lens P Q) : Lens (dirMonad M P) (dirMonad M Q) :=
  l.toFunA ⇆ fun a m => l.toFunB a <$> m

variable (M) in
/-- The counit of `dirMonad M`: a direction demands the pure computation of itself. -/
def dirMonadCounit (P : PFunctor.{uA, uB}) : Lens (dirMonad M P) P :=
  id ⇆ fun _ d => pure d

variable (M) in
/-- The comultiplication of `dirMonad M`: a computation of computations demands its join. -/
def dirMonadComult (P : PFunctor.{uA, uB}) : Lens (dirMonad M P) (dirMonad M (dirMonad M P)) :=
  id ⇆ fun _ mm => mm >>= id

/-- `dirMonad M` preserves identities. -/
theorem dirMonadMap_id : dirMonadMap (M := M) (Lens.id P) = Lens.id (dirMonad M P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => id_map m

/-- `dirMonad M` preserves composition. -/
theorem dirMonadMap_comp (m : Lens Q R) (l : Lens P Q) :
    dirMonadMap (M := M) (m ∘ₗ l) = dirMonadMap (M := M) m ∘ₗ dirMonadMap (M := M) l :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun x =>
    comp_map (m.toFunB (l.toFunA a)) (l.toFunB a) x

/-- The counit of `dirMonad M` is natural. -/
theorem dirMonadCounit_natural (l : Lens P Q) :
    dirMonadCounit M Q ∘ₗ dirMonadMap l = l ∘ₗ dirMonadCounit M P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun d => map_pure (l.toFunB a) d

/-- The comultiplication of `dirMonad M` is natural. -/
theorem dirMonadComult_natural (l : Lens P Q) :
    dirMonadComult M Q ∘ₗ dirMonadMap l = dirMonadMap (dirMonadMap l) ∘ₗ dirMonadComult M P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (mm : M (M (Q.B (l.toFunA a)))) => by
    change l.toFunB a <$> (mm >>= id) = (Functor.map (l.toFunB a) <$> mm) >>= id
    simp [map_bind, bind_map_left]

/-- Left counit law of `dirMonad M`. -/
theorem dirMonadCounit_comult (P : PFunctor.{uA, uB}) :
    dirMonadCounit M (dirMonad M P) ∘ₗ dirMonadComult M P = Lens.id (dirMonad M P) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun m => pure_bind m id

/-- Right counit law of `dirMonad M`. -/
theorem dirMonadMap_counit_comult (P : PFunctor.{uA, uB}) :
    dirMonadMap (dirMonadCounit M P) ∘ₗ dirMonadComult M P = Lens.id (dirMonad M P) :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (m : M (P.B a)) => by
    change (pure <$> m) >>= id = m
    simp [bind_map_left]

/-- Coassociativity of the comultiplication of `dirMonad M`. -/
theorem dirMonadComult_coassoc (P : PFunctor.{uA, uB}) :
    dirMonadComult M (dirMonad M P) ∘ₗ dirMonadComult M P =
      dirMonadMap (dirMonadComult M P) ∘ₗ dirMonadComult M P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (mmm : M (M (M (P.B a)))) => by
    change (mmm >>= id) >>= id = ((fun mm => mm >>= id) <$> mmm) >>= id
    simp [bind_assoc, bind_map_left]

/-- The co-Kleisli composite of `dirMonad M` binds the backward maps: its backward map sends a
direction to the computation of the second backward map bound to the first. -/
theorem dirMonad_cokleisli_comp (g : Lens (dirMonad M Q) R) (f : Lens (dirMonad M P) Q) :
    g ∘ₗ dirMonadMap f ∘ₗ dirMonadComult M P =
      ((fun a => g.toFunA (f.toFunA a)) ⇆
        fun a d => g.toFunB (f.toFunA a) d >>= f.toFunB a) :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (d : R.B (g.toFunA (f.toFunA a))) => by
    change (f.toFunB a <$> g.toFunB (f.toFunA a) d) >>= id = g.toFunB (f.toFunA a) d >>= f.toFunB a
    simp [bind_map_left]

/-- At the multiset monad, the comultiplication of `dirMonad` is the comultiplication of the
multiset exponential: the join of a multiset of multisets is its sum. -/
theorem dirMonadComult_multiset (P : PFunctor.{uA, uB}) :
    dirMonadComult Multiset P = bangComult P :=
  Lens.ext _ _ (fun _ => rfl) fun a => funext fun (mm : Multiset (Multiset (P.B a))) => by
    change (mm.map id).join = mm.join
    rw [Multiset.map_id]

end Lens

namespace LensCat

section

variable (M : Type uB → Type uB) [Monad M] [LawfulMonad M]

/-- `dirMonad M` as an endofunctor of the category of lenses. -/
def dirMonadFunctor : LensCat.{uA, uB} ⥤ LensCat.{uA, uB} where
  obj X := LensCat.of (dirMonad M X.toPFunctor)
  map f := Lens.dirMonadMap f
  map_id _ := Lens.dirMonadMap_id
  map_comp f g := Lens.dirMonadMap_comp g f

/-- `dirMonad M` as a comonad on the category of lenses. -/
def dirMonadComonad : Comonad LensCat.{uA, uB} where
  toFunctor := dirMonadFunctor M
  ε := { app X := Lens.dirMonadCounit M X.toPFunctor,
         naturality _ _ f := Lens.dirMonadCounit_natural f }
  δ := { app X := Lens.dirMonadComult M X.toPFunctor,
         naturality _ _ f := Lens.dirMonadComult_natural f }
  coassoc X := (Lens.dirMonadComult_coassoc X.toPFunctor).symm
  left_counit X := Lens.dirMonadCounit_comult X.toPFunctor
  right_counit X := Lens.dirMonadMap_counit_comult X.toPFunctor

end

/-- At the multiset monad, the comonad of computations of directions is the multiset exponential:
the components of the isomorphism are identities, and the join of a multiset of multisets is its
sum. -/
def dirMonadMultisetIso : dirMonadComonad.{uA, uB} Multiset ≅ bangComonad :=
  ComonadIso.mk
    (NatIso.ofComponents (fun X => Iso.refl ((dirMonadComonad.{uA, uB} Multiset).obj X))
      fun _ => Lens.ext _ _ (fun _ => rfl) fun _ => rfl)
    (fun _ => Lens.ext _ _ (fun _ => rfl) fun _ => rfl)
    fun X => by
      change Lens.bangComult X.toPFunctor =
        Lens.bangMap (Lens.id (bang X.toPFunctor)) ∘ₗ Lens.dirMonadComult Multiset X.toPFunctor
      rw [Lens.bangMap_id, Lens.id_comp, Lens.dirMonadComult_multiset]

end LensCat

end PFunctor
