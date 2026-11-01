/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Lens.Factorization

/-!
# The natural-model structure of a universe polynomial

A universe is a family `El : U → Type u`; its display map is the projection
`u : Ũ = Σ a, El a → U`, and its polynomial is `univPoly El = ⟨U, El⟩`, the polynomial `P_u` of
`u` (`PFunctor.Slice.equivOfMapFst` in `PolyFun.PFunctor.Slice`). Following
Awodey [Awo18], a Σ-structure on `u` is a cartesian map of
polynomials `P_u ◃ P_u → P_u`, and a Π-structure is a cartesian map from the polynomial
`piPoly El` (positions `P_u U`, directions at `(a, b)` the dependent functions
`∀ x : El a, El (b x)`) to `P_u`; equivalently, a pullback square from `P_u Ũ → P_u U` to
`u : Ũ → U`.

A cartesian map of polynomials is a `CartLens`: a map of positions with an equivalence of
directions at each position, so that its underlying lens is cartesian
(`CartLens.toLens_isCartesian`, the predicate `PFunctor.Lens.IsCartesian`); conversely a
cartesian lens gives a `CartLens` (`CartLens.ofIsCartesian`). The fibre equivalences are data, so
that the equivalences between codes and structures below hold definitionally. The square of total
spaces of a `CartLens` is a pullback (`CartLens.pullbackEquiv`).

Codes for Σ and Π (`SigmaCodes`, `PiCodes`): a code `sig a b` (resp. `pi a b`) for each
`a : U` and `b : El a → U`, with an equivalence `El (sig a b) ≃ Σ x, El (b x)`
(resp. `El (pi a b) ≃ ∀ x, El (b x)`). Codes are the same as structures
(`sigmaCodesEquiv`, `piCodesEquiv`), and the Π-structure of codes has Awodey's pullback square
`P_u Ũ ≃ P_u U ×_U Ũ` with the abstraction map `lam` on top (`PiStructure.lamPullbackEquiv`).

## Main definitions

* `PFunctor.CartLens`: cartesian maps of polynomials, with the fibre equivalences as data.
* `PFunctor.NaturalModel.univPoly`, `PFunctor.NaturalModel.piPoly`.
* `PFunctor.NaturalModel.SigmaStructure`, `PFunctor.NaturalModel.PiStructure`.
* `PFunctor.NaturalModel.SigmaCodes`, `PFunctor.NaturalModel.PiCodes`.
* `PFunctor.NaturalModel.PiStructure.lam`: the abstraction map `P_u Ũ → Ũ`.

## Main results

* `PFunctor.CartLens.pullbackEquiv`: the square of total spaces of a cartesian map is a
  pullback, stated as the gap map being an equivalence.
* `PFunctor.NaturalModel.sigmaCodesEquiv`, `PFunctor.NaturalModel.piCodesEquiv`: codes closed
  under Σ (resp. Π) with `El`-equivalences are exactly Σ- (resp. Π-) structures.
* `PFunctor.NaturalModel.PiStructure.lam_fst`, `PFunctor.NaturalModel.PiStructure.lamPullbackEquiv`:
  Awodey's Π-square commutes and is a pullback.

## References

Awodey [Awo18] and Gambino and Kock [GK13]; see `REFERENCES.md`.
-/

@[expose] public section

universe u

namespace PFunctor

/-- A cartesian map of polynomials: a map of positions with an equivalence between the
directions at each position and the directions at its image. -/
structure CartLens (P Q : PFunctor.{u, u}) where
  /-- The map of positions. -/
  toFunA : P.A → Q.A
  /-- The equivalence of directions at each position. -/
  fibEquiv : ∀ a, P.B a ≃ Q.B (toFunA a)

namespace CartLens

variable {P Q : PFunctor.{u, u}}

/-- The underlying lens of a cartesian map. -/
def toLens (l : CartLens P Q) : Lens P Q := ⟨l.toFunA, fun a => (l.fibEquiv a).symm⟩

/-- The lens of a cartesian map is cartesian: its backward maps are bijections. -/
theorem toLens_isCartesian (l : CartLens P Q) : l.toLens.IsCartesian :=
  fun a => (l.fibEquiv a).symm.bijective

/-- The cartesian map of a cartesian lens, with the inverses of its backward maps as the fibre
equivalences. -/
noncomputable def ofIsCartesian (l : Lens P Q) (hl : l.IsCartesian) : CartLens P Q :=
  ⟨l.toFunA, fun a => (Lens.cartesianDirectionEquiv l hl a).symm⟩

/-- The lens of the cartesian map of a cartesian lens is that lens. -/
theorem toLens_ofIsCartesian (l : Lens P Q) (hl : l.IsCartesian) :
    (ofIsCartesian l hl).toLens = l :=
  rfl

/-- The map of total spaces of directions over the map of positions. -/
def total (l : CartLens P Q) : (Σ a, P.B a) → Σ q, Q.B q :=
  fun x => ⟨l.toFunA x.1, l.fibEquiv x.1 x.2⟩

/-- The square of total spaces of a cartesian map is a pullback: the gap map into
`P.A ×_{Q.A} (Σ q, Q.B q)` is an equivalence. -/
def pullbackEquiv (l : CartLens P Q) :
    (Σ a, P.B a) ≃ {p : P.A × (Σ q, Q.B q) // l.toFunA p.1 = p.2.1} where
  toFun x := ⟨(x.1, l.total x), rfl⟩
  invFun y := ⟨y.1.1, (l.fibEquiv y.1.1).symm (cast (congrArg Q.B y.2.symm) y.1.2.2)⟩
  left_inv x := by
    obtain ⟨a, b⟩ := x
    simp only [total, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact (congrArg (l.fibEquiv a).symm (cast_eq _ _)).trans ((l.fibEquiv a).symm_apply_apply b)
  right_inv y := by
    obtain ⟨⟨a, q, d⟩, h⟩ := y
    dsimp only at h
    subst h
    simp [total]

/-- The gap map of `pullbackEquiv` pairs the projection with the total map. -/
theorem pullbackEquiv_apply (l : CartLens P Q) (x : Σ a, P.B a) :
    (l.pullbackEquiv x).1 = (x.1, l.total x) :=
  rfl

end CartLens

namespace NaturalModel

variable {U : Type u} (El : U → Type u)

/-- The universe polynomial `P_u = ⟨U, El⟩`. -/
def univPoly : PFunctor.{u, u} := ⟨U, El⟩

/-- A Σ-structure on the universe: a cartesian map `P_u ◃ P_u → P_u`. -/
abbrev SigmaStructure : Type u := CartLens (univPoly El ◃ univPoly El) (univPoly El)

/-- The polynomial of dependent function types: positions `P_u U`, directions at `(a, b)` the
functions `∀ x : El a, El (b x)`. -/
def piPoly : PFunctor.{u, u} := ⟨univPoly El U, fun c => ∀ x : El c.1, El (c.2 x)⟩

/-- A Π-structure on the universe: a cartesian map `piPoly El → P_u`. -/
abbrev PiStructure : Type u := CartLens (piPoly El) (univPoly El)

/-- Codes for dependent sums in the universe. -/
structure SigmaCodes where
  /-- The code of `Σ x : El a, El (b x)`. -/
  sig : (a : U) → (El a → U) → U
  /-- Elements of `sig a b` are dependent pairs. -/
  sigEquiv : ∀ a b, El (sig a b) ≃ Σ x : El a, El (b x)

/-- Codes for dependent products in the universe. -/
structure PiCodes where
  /-- The code of `∀ x : El a, El (b x)`. -/
  pi : (a : U) → (El a → U) → U
  /-- Elements of `pi a b` are dependent functions. -/
  piEquiv : ∀ a b, El (pi a b) ≃ ∀ x : El a, El (b x)

/-- Σ-codes are Σ-structures: the code map is the map of positions `P_u ◃ P_u → P_u`, and the
pairing equivalences are the fibres of the pullback square. -/
def sigmaCodesEquiv : SigmaCodes El ≃ SigmaStructure El where
  toFun c := ⟨fun x => c.sig x.1 x.2, fun x => (c.sigEquiv x.1 x.2).symm⟩
  invFun s := ⟨fun a b => s.toFunA ⟨a, b⟩, fun a b => (s.fibEquiv ⟨a, b⟩).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Π-codes are Π-structures. -/
def piCodesEquiv : PiCodes El ≃ PiStructure El where
  toFun c := ⟨fun x => c.pi x.1 x.2, fun x => (c.piEquiv x.1 x.2).symm⟩
  invFun s := ⟨fun a b => s.toFunA ⟨a, b⟩, fun a b => (s.fibEquiv ⟨a, b⟩).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The code of the Σ-structure of Σ-codes at `(a, b)` is `sig a b`. -/
theorem sigmaCodesEquiv_toFunA (c : SigmaCodes El) (a : U) (b : El a → U) :
    (sigmaCodesEquiv El c).toFunA ⟨a, b⟩ = c.sig a b :=
  rfl

/-- The code of the Π-structure of Π-codes at `(a, b)` is `pi a b`. -/
theorem piCodesEquiv_toFunA (c : PiCodes El) (a : U) (b : El a → U) :
    (piCodesEquiv El c).toFunA ⟨a, b⟩ = c.pi a b :=
  rfl

/-- `P_u Ũ` is the total space of `piPoly El`: a family of elements is its family of codes
with an element over each. -/
def objTotalEquiv :
    univPoly El (Σ a, El a) ≃ Σ c : univPoly El U, ∀ x : El c.1, El (c.2 x) where
  toFun t := ⟨⟨t.1, fun x => (t.2 x).1⟩, fun x => (t.2 x).2⟩
  invFun y := ⟨y.1.1, fun x => ⟨y.1.2 x, y.2 x⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace PiStructure

variable {El}

/-- The abstraction map `λ : P_u Ũ → Ũ` of a Π-structure. -/
def lam (s : PiStructure El) (t : univPoly El (Σ a, El a)) : Σ a, El a :=
  s.total (objTotalEquiv El t)

/-- Awodey's Π-square commutes: `u ∘ λ = Π ∘ P_u(u)`. -/
theorem lam_fst (s : PiStructure El) (t : univPoly El (Σ a, El a)) :
    (s.lam t).1 = s.toFunA ((univPoly El).map Sigma.fst t) :=
  rfl

/-- Awodey's Π-square is a pullback: the gap map `P_u Ũ → P_u U ×_U Ũ`, `t ↦ (P_u(u) t, λ t)`,
is an equivalence. -/
def lamPullbackEquiv (s : PiStructure El) :
    univPoly El (Σ a, El a) ≃
      {p : univPoly El U × (Σ a, El a) // s.toFunA p.1 = p.2.1} :=
  (objTotalEquiv El).trans s.pullbackEquiv

/-- The gap map of `lamPullbackEquiv` is `t ↦ (P_u(u) t, λ t)`. -/
theorem lamPullbackEquiv_apply (s : PiStructure El) (t : univPoly El (Σ a, El a)) :
    (s.lamPullbackEquiv t).1 = ((univPoly El).map Sigma.fst t, s.lam t) :=
  rfl

end PiStructure

end NaturalModel

end PFunctor
