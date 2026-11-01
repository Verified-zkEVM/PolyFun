/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.IPFunctor.Basic

/-!
# Dependent sums and products along a map, and polynomial functors

A type over `A` is a family `X : A → Type u`; a map `f : B → A` (a display map) has the fibres
`Fib f a = {b // f b = a}`. Along `f` there are three functors between families:
pullback `pb f X = X ∘ f`, the dependent sum `sigmaAlong f Y a = Σ (p : Fib f a), Y p`, and the
dependent product `piAlong f Y a = Π (p : Fib f a), Y p`. They form the adjoint triple
`Σ_f ⊣ f* ⊣ Π_f`, stated as equivalences of hom-types of families, natural in both arguments.

The polynomial functor of `f` is `ofMap f`, with positions `A` and directions the fibres of
`f`; its extension is `Σ_{A → 1} ∘ Π_f ∘ (B → 1)*`. More generally the extension of an indexed
polynomial `P : IPFunctor I J`, presented as the diagram `I ← E → D → J`, is
`Σ_t ∘ Π_p ∘ s*` (`IPFunctor.objEquivSigmaPiPb`).

The distributive law ([Web15]; [GK13], Lemma 2.3) rewrites `Π_g ∘ Σ_f` for composable maps
`f : C → B`, `g : B → A` as `Σ_w ∘ Π_{g'} ∘ ε*`, where `w : N → A` is `Π_g` applied to `f`,
`g' : M → N` is the pullback of `g` along `w` and `ε : M → C` is the evaluation map.

Indexed polynomials are closed under Σ and Π along a map, on either side: post-composition
with `Σ_u` and `Π_u` (`IPFunctor.sigmaPost`, `IPFunctor.piPost`) and pre-composition with
`v*`, `Σ_v` and `Π_v` (`IPFunctor.pbPre`, `IPFunctor.sigmaPre`, `IPFunctor.piPre`), each
with explicit positions and directions and an equivalence of extensions.

## Main definitions

* `PFunctor.Slice.pb`, `PFunctor.Slice.sigmaAlong`, `PFunctor.Slice.piAlong`: the three
  functors along a map, on families.
* `PFunctor.Slice.ofMap`: the polynomial functor `P_f` of a map.
* `PFunctor.Slice.DistN`, `PFunctor.Slice.DistM`, `PFunctor.Slice.distEps`: the objects
  and the evaluation map of the distributivity diagram.
* `IPFunctor.sigmaPost`, `IPFunctor.piPost`, `IPFunctor.pbPre`, `IPFunctor.sigmaPre`,
  `IPFunctor.piPre`: closure of indexed polynomials under Σ, Π and pullback.

## Main results

* `PFunctor.Slice.sigmaAdj`, `PFunctor.Slice.piAdj`: `Σ_f ⊣ f*` and `f* ⊣ Π_f`, with
  naturality `sigmaAdj_comp_sigmaMap`, `sigmaAdj_comp_left`, `piAdj_comp_pbMap`,
  `piAdj_comp_left`.
* `PFunctor.Slice.ofMapObjEquiv`: `P_f X ≃ Σ_{A → 1} Π_f (B → 1)* X`.
* `PFunctor.Slice.equivOfMapFst`: every `PFunctor` is `P_f` of its total projection.
* `PFunctor.Slice.distribEquiv`, `PFunctor.Slice.distribEquiv_natural`: the distributive law.
* `IPFunctor.objEquivSigmaPiPb`: the extension of an indexed polynomial is `Σ_t Π_p s*`.
* `PFunctor.sigmaObjEquiv`, `PFunctor.piObjEquiv`: the extension of the indexed sum and
  product of a family of `PFunctor`s.

## References

Weber [Web15], Gambino and Kock [GK13] and Awodey [Awo18]; see `REFERENCES.md`.
-/

@[expose] public section

universe u

namespace PFunctor

namespace Slice

variable {A B C : Type u}

/-- The fibre of `f : B → A` over `a : A`. -/
abbrev Fib (f : B → A) (a : A) : Type u := {b : B // f b = a}

/-- A map of families over `A`: a function on each fibre. -/
abbrev Hom (X Y : A → Type u) : Type u := ∀ a, X a → Y a

/-- Composition of maps of families. -/
def Hom.comp {X Y Z : A → Type u} (g : Hom Y Z) (h : Hom X Y) : Hom X Z :=
  fun a x => g a (h a x)

/-- Pullback (reindexing) of a family along `f : B → A`. -/
abbrev pb (f : B → A) (X : A → Type u) : B → Type u := fun b => X (f b)

/-- The dependent sum of a family over `B` along `f : B → A`. -/
abbrev sigmaAlong (f : B → A) (Y : B → Type u) : A → Type u := fun a => Σ p : Fib f a, Y p.1

/-- The dependent product of a family over `B` along `f : B → A`. -/
abbrev piAlong (f : B → A) (Y : B → Type u) : A → Type u := fun a => (p : Fib f a) → Y p.1

/-- The action of pullback on maps of families. -/
def pbMap (f : B → A) {X X' : A → Type u} (h : Hom X X') : Hom (pb f X) (pb f X') :=
  fun b x => h (f b) x

/-- The action of the dependent sum on maps of families. -/
def sigmaMap (f : B → A) {Y Y' : B → Type u} (k : Hom Y Y') :
    Hom (sigmaAlong f Y) (sigmaAlong f Y') :=
  fun _ x => ⟨x.1, k x.1.1 x.2⟩

/-- The action of the dependent product on maps of families. -/
def piMap (f : B → A) {Y Y' : B → Type u} (k : Hom Y Y') :
    Hom (piAlong f Y) (piAlong f Y') :=
  fun _ φ p => k p.1 (φ p)

/-! ## The adjoint triple `Σ_f ⊣ f* ⊣ Π_f` -/

/-- `Σ_f ⊣ f*`: maps `Σ_f Y → X` over `A` are maps `Y → f* X` over `B`. -/
def sigmaAdj (f : B → A) (Y : B → Type u) (X : A → Type u) :
    Hom (sigmaAlong f Y) X ≃ Hom Y (pb f X) where
  toFun φ b y := φ (f b) ⟨⟨b, rfl⟩, y⟩
  invFun ψ a x := cast (congrArg X x.1.2) (ψ x.1.1 x.2)
  left_inv φ := by
    funext a x
    obtain ⟨⟨b, rfl⟩, y⟩ := x
    rfl
  right_inv ψ := rfl

/-- Naturality of `sigmaAdj` in the family over `B`. -/
theorem sigmaAdj_comp_sigmaMap (f : B → A) {Y Y' : B → Type u} (X : A → Type u)
    (k : Hom Y' Y) (φ : Hom (sigmaAlong f Y) X) :
    sigmaAdj f Y' X (φ.comp (sigmaMap f k)) = (sigmaAdj f Y X φ).comp k :=
  rfl

/-- Naturality of `sigmaAdj` in the family over `A`. -/
theorem sigmaAdj_comp_left (f : B → A) (Y : B → Type u) {X X' : A → Type u}
    (h : Hom X X') (φ : Hom (sigmaAlong f Y) X) :
    sigmaAdj f Y X' (h.comp φ) = (pbMap f h).comp (sigmaAdj f Y X φ) :=
  rfl

/-- `f* ⊣ Π_f`: maps `f* X → Y` over `B` are maps `X → Π_f Y` over `A`. -/
def piAdj (f : B → A) (X : A → Type u) (Y : B → Type u) :
    Hom (pb f X) Y ≃ Hom X (piAlong f Y) where
  toFun φ a x p := φ p.1 (cast (congrArg X p.2.symm) x)
  invFun ψ b x := ψ (f b) x ⟨b, rfl⟩
  left_inv φ := rfl
  right_inv ψ := by
    funext a x p
    obtain ⟨b, rfl⟩ := p
    rfl

/-- Naturality of `piAdj` in the family over `A`. -/
theorem piAdj_comp_pbMap (f : B → A) {X X' : A → Type u} (Y : B → Type u)
    (h : Hom X' X) (φ : Hom (pb f X) Y) :
    piAdj f X' Y (φ.comp (pbMap f h)) = (piAdj f X Y φ).comp h := by
  funext a x p
  obtain ⟨b, rfl⟩ := p
  rfl

/-- Naturality of `piAdj` in the family over `B`. -/
theorem piAdj_comp_left (f : B → A) (X : A → Type u) {Y Y' : B → Type u}
    (k : Hom Y Y') (φ : Hom (pb f X) Y) :
    piAdj f X Y' (k.comp φ) = (piMap f k).comp (piAdj f X Y φ) :=
  rfl

/-! ## The polynomial functor of a map -/

/-- The polynomial functor `P_f = Σ_{a : A} (-)^{f⁻¹(a)}` of a map `f : B → A`. -/
def ofMap (f : B → A) : PFunctor.{u, u} := ⟨A, Fib f⟩

/-- The extension of `P_f` is `Σ_{A → 1} ∘ Π_f ∘ (B → 1)*` applied to the constant family. -/
def ofMapObjEquiv (f : B → A) (X : Type u) :
    ofMap f X ≃ sigmaAlong (fun _ : A => PUnit.unit.{u + 1})
      (piAlong f (pb (fun _ : B => PUnit.unit.{u + 1}) (fun _ => X))) PUnit.unit where
  toFun x := ⟨⟨x.1, rfl⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every polynomial functor is the polynomial functor of the projection of its total space
of directions. -/
def equivOfMapFst (P : PFunctor.{u, u}) :
    P ≃ₚ ofMap (Sigma.fst : (Σ a, P.B a) → P.A) where
  equivA := _root_.Equiv.refl P.A
  equivB a := (_root_.Equiv.sigmaSubtype a).symm

/-! ## Σ and Π along the projection of a family -/

/-- The dependent sum along the projection of a family is the fibrewise sum. -/
def sigmaFstEquiv (Y : A → Type u) (Z : (Σ a, Y a) → Type u) (a : A) :
    sigmaAlong (Sigma.fst : (Σ a, Y a) → A) Z a ≃ Σ y : Y a, Z ⟨a, y⟩ where
  toFun x := by
    obtain ⟨⟨⟨a', y⟩, h⟩, z⟩ := x
    dsimp only at h
    subst h
    exact ⟨y, z⟩
  invFun x := ⟨⟨⟨a, x.1⟩, rfl⟩, x.2⟩
  left_inv x := by
    obtain ⟨⟨⟨a', y⟩, h⟩, z⟩ := x
    dsimp only at h
    subst h
    rfl
  right_inv x := rfl

/-- The dependent product along the projection of a family is the fibrewise product. -/
def piFstEquiv (Y : A → Type u) (Z : (Σ a, Y a) → Type u) (a : A) :
    piAlong (Sigma.fst : (Σ a, Y a) → A) Z a ≃ ∀ y : Y a, Z ⟨a, y⟩ where
  toFun φ y := φ ⟨⟨a, y⟩, rfl⟩
  invFun ψ p := by
    obtain ⟨⟨a', y⟩, h⟩ := p
    dsimp only at h
    subst h
    exact ψ y
  left_inv φ := by
    funext p
    obtain ⟨⟨a', y⟩, h⟩ := p
    dsimp only at h
    subst h
    rfl
  right_inv ψ := rfl

/-- `sigmaFstEquiv` commutes with the action on maps of families. -/
theorem sigmaFstEquiv_sigmaMap (Y : A → Type u) {Z Z' : (Σ a, Y a) → Type u} (k : Hom Z Z')
    (a : A) (x : sigmaAlong (Sigma.fst : (Σ a, Y a) → A) Z a) :
    sigmaFstEquiv Y Z' a (sigmaMap Sigma.fst k a x) =
      ⟨(sigmaFstEquiv Y Z a x).1, k _ (sigmaFstEquiv Y Z a x).2⟩ := by
  obtain ⟨⟨⟨a', y⟩, h⟩, z⟩ := x
  dsimp only at h
  subst h
  rfl

/-- The inverse of `sigmaFstEquiv` commutes with the action on maps of families. -/
theorem sigmaFstEquiv_symm_sigmaMap (Y : A → Type u) {Z Z' : (Σ a, Y a) → Type u}
    (k : Hom Z Z') (a : A) (x : Σ y : Y a, Z ⟨a, y⟩) :
    sigmaMap Sigma.fst k a ((sigmaFstEquiv Y Z a).symm x) =
      (sigmaFstEquiv Y Z' a).symm ⟨x.1, k _ x.2⟩ :=
  rfl

/-- The inverse of `piFstEquiv` commutes with the action on maps of families. -/
theorem piFstEquiv_symm_piMap (Y : A → Type u) {Z Z' : (Σ a, Y a) → Type u} (k : Hom Z Z')
    (a : A) (ψ : ∀ y : Y a, Z ⟨a, y⟩) :
    piMap Sigma.fst k a ((piFstEquiv Y Z a).symm ψ) =
      (piFstEquiv Y Z' a).symm (fun y => k _ (ψ y)) := by
  rw [_root_.Equiv.eq_symm_apply]
  funext y
  exact congrArg (k _) (congrFun ((piFstEquiv Y Z a).apply_symm_apply ψ) y)

/-! ## The distributive law -/

section Distrib

variable (f : C → B) (g : B → A)

/-- The object `N = Π_g f` over `A`: a point of `A` with a section of `f` over its `g`-fibre. -/
abbrev DistN : Type u := Σ a, piAlong g (Fib f) a

/-- The pullback `M = N ×_A B` of `g` along the projection `N → A`. -/
abbrev DistM : Type u := Σ n : DistN f g, Fib g n.1

/-- The evaluation map `ε : M → C`, applying the section at the point of the fibre. -/
abbrev distEps : DistM f g → C := fun m => (m.1.2 m.2).1

/-- The choice equivalence: a section of `Σ_f X` over the `g`-fibre of `a` is a section of
`f` over that fibre together with a point of `X` over each value. -/
def choiceEquiv (X : C → Type u) (a : A) :
    piAlong g (sigmaAlong f X) a ≃ Σ s : piAlong g (Fib f) a, ∀ p, X (s p).1 where
  toFun φ := ⟨fun p => (φ p).1, fun p => (φ p).2⟩
  invFun x p := ⟨x.1 p, x.2 p⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The distributive law: `Π_g ∘ Σ_f ≅ Σ_w ∘ Π_{g'} ∘ ε*` (Gambino–Kock, Lemma 2.3), where
`w : N → A` and `g' : M → N` are the projections. -/
def distribEquiv (X : C → Type u) (a : A) :
    piAlong g (sigmaAlong f X) a ≃
      sigmaAlong (Sigma.fst : DistN f g → A)
        (piAlong (Sigma.fst : DistM f g → DistN f g) (pb (distEps f g) X)) a :=
  (choiceEquiv f g X a).trans <|
    (_root_.Equiv.sigmaCongrRight fun s =>
      (piFstEquiv (fun n : DistN f g => Fib g n.1) (pb (distEps f g) X) ⟨a, s⟩).symm).trans
    (sigmaFstEquiv (piAlong g (Fib f)) _ a).symm

/-- The distributive law sends a section `φ` to the section of `f` it chooses, with the points
of `X` over that section. -/
theorem distribEquiv_apply (X : C → Type u) (a : A) (φ : piAlong g (sigmaAlong f X) a) :
    distribEquiv f g X a φ =
      (sigmaFstEquiv (piAlong g (Fib f)) _ a).symm
        ⟨fun p => (φ p).1, (piFstEquiv (fun n : DistN f g => Fib g n.1) (pb (distEps f g) X)
          ⟨a, fun p => (φ p).1⟩).symm fun p => (φ p).2⟩ :=
  rfl

/-- Naturality of the distributive law in the family over `C`. -/
theorem distribEquiv_natural {X X' : C → Type u} (k : Hom X X') (a : A)
    (φ : piAlong g (sigmaAlong f X) a) :
    distribEquiv f g X' a (piMap g (sigmaMap f k) a φ) =
      sigmaMap Sigma.fst (piMap Sigma.fst (pbMap (distEps f g) k)) a
        (distribEquiv f g X a φ) := by
  rw [distribEquiv_apply, distribEquiv_apply, sigmaFstEquiv_symm_sigmaMap]
  dsimp only
  rw [piFstEquiv_symm_piMap]
  rfl

end Distrib

end Slice

open Slice

/-! ## Indexed sums and products of `PFunctor`s -/

/-- The extension of the indexed sum of a family of polynomial functors. -/
def sigmaObjEquiv {I : Type u} (F : I → PFunctor.{u, u}) (X : Type u) :
    sigma F X ≃ Σ i, F i X where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The extension of the indexed product of a family of polynomial functors. -/
def piObjEquiv {I : Type u} (F : I → PFunctor.{u, u}) (X : Type u) :
    pi F X ≃ ∀ i, F i X where
  toFun x i := ⟨x.1 i, fun b => x.2 ⟨i, b⟩⟩
  invFun y := ⟨fun i => (y i).1, fun d => (y d.1).2 d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PFunctor

/-! ## Indexed polynomials: Σ, Π and pullback along a map -/

namespace IPFunctor

open PFunctor.Slice

variable {I I' J K : Type u}

/-- The total space of positions `D = Σ j, P.A j` of an indexed polynomial. -/
abbrev TotA (P : IPFunctor.{u, u, u, u} I J) : Type u := Σ j, P.A j

/-- The total space of directions `E = Σ (x : D), P.B x.1 x.2` of an indexed polynomial. -/
abbrev TotB (P : IPFunctor.{u, u, u, u} I J) : Type u := Σ x : TotA P, P.B x.1 x.2

/-- The extension of `P : IPFunctor I J`, presented as `I ← E → D → J`, is `Σ_t ∘ Π_p ∘ s*`
(Gambino–Kock, §1.4). -/
def objEquivSigmaPiPb (P : IPFunctor.{u, u, u, u} I J) (X : I → Type u) (j : J) :
    P.Obj X j ≃ sigmaAlong (Sigma.fst : TotA P → J)
      (piAlong (Sigma.fst : TotB P → TotA P) (pb (fun e => P.src e.1.1 e.1.2 e.2) X)) j :=
  calc P.Obj X j ≃ Σ a : P.A j, ∀ b : P.B j a, X (P.src j a b) := Equiv.refl _
    _ ≃ Σ a : P.A j, piAlong (Sigma.fst : TotB P → TotA P)
          (pb (fun e => P.src e.1.1 e.1.2 e.2) X) ⟨j, a⟩ :=
        Equiv.sigmaCongrRight fun a =>
          (piFstEquiv (fun x : TotA P => P.B x.1 x.2)
            (pb (fun e => P.src e.1.1 e.1.2 e.2) X) ⟨j, a⟩).symm
    _ ≃ _ := (sigmaFstEquiv P.A _ j).symm

/-- Post-composition with `Σ_u` for `u : J → K`. -/
def sigmaPost (u : J → K) (P : IPFunctor.{u, u, u, u} I J) : IPFunctor.{u, u, u, u} I K where
  A k := Σ p : Fib u k, P.A p.1
  B _ x := P.B x.1.1 x.2
  src _ x b := P.src x.1.1 x.2 b

/-- The extension of `sigmaPost u P` is `Σ_u` of the extension of `P`. -/
def sigmaPostObjEquiv (u : J → K) (P : IPFunctor.{u, u, u, u} I J) (X : I → Type u) (k : K) :
    (sigmaPost u P).Obj X k ≃ sigmaAlong u (P.Obj X) k where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Post-composition with `Π_u` for `u : J → K`: a position is a section of positions over
the `u`-fibre, a direction is a point of the fibre with a direction there. -/
def piPost (u : J → K) (P : IPFunctor.{u, u, u, u} I J) : IPFunctor.{u, u, u, u} I K where
  A k := (p : Fib u k) → P.A p.1
  B k s := Σ p : Fib u k, P.B p.1 (s p)
  src _ s d := P.src d.1.1 (s d.1) d.2

/-- The extension of `piPost u P` is `Π_u` of the extension of `P` (the distributive law in
polynomial form). -/
def piPostObjEquiv (u : J → K) (P : IPFunctor.{u, u, u, u} I J) (X : I → Type u) (k : K) :
    (piPost u P).Obj X k ≃ piAlong u (P.Obj X) k where
  toFun x p := ⟨x.1 p, fun b => x.2 ⟨p, b⟩⟩
  invFun y := ⟨fun p => (y p).1, fun d => (y d.1).2 d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pre-composition with the pullback `v*` for `v : I → I'`. -/
def pbPre (v : I → I') (P : IPFunctor.{u, u, u, u} I J) : IPFunctor.{u, u, u, u} I' J where
  A := P.A
  B := P.B
  src j a b := v (P.src j a b)

/-- The extension of `pbPre v P` is the extension of `P` at `v* X`. -/
def pbPreObjEquiv (v : I → I') (P : IPFunctor.{u, u, u, u} I J) (X : I' → Type u) (j : J) :
    (pbPre v P).Obj X j ≃ P.Obj (pb v X) j where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pre-composition with `Σ_v` for `v : I' → I`: a position chooses, at each direction, a
point of the `v`-fibre over its source. -/
def sigmaPre (v : I' → I) (P : IPFunctor.{u, u, u, u} I J) : IPFunctor.{u, u, u, u} I' J where
  A j := Σ a : P.A j, ∀ b : P.B j a, Fib v (P.src j a b)
  B j x := P.B j x.1
  src _ x b := (x.2 b).1

/-- The extension of `sigmaPre v P` is the extension of `P` at `Σ_v X`. -/
def sigmaPreObjEquiv (v : I' → I) (P : IPFunctor.{u, u, u, u} I J) (X : I' → Type u) (j : J) :
    (sigmaPre v P).Obj X j ≃ P.Obj (sigmaAlong v X) j where
  toFun x := ⟨x.1.1, fun b => ⟨x.1.2 b, x.2 b⟩⟩
  invFun y := ⟨⟨y.1, fun b => (y.2 b).1⟩, fun b => (y.2 b).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pre-composition with `Π_v` for `v : I' → I`: a direction is a direction of `P` with a
point of the `v`-fibre over its source. -/
def piPre (v : I' → I) (P : IPFunctor.{u, u, u, u} I J) : IPFunctor.{u, u, u, u} I' J where
  A := P.A
  B j a := Σ b : P.B j a, Fib v (P.src j a b)
  src _ _ d := d.2.1

/-- The extension of `piPre v P` is the extension of `P` at `Π_v X`. -/
def piPreObjEquiv (v : I' → I) (P : IPFunctor.{u, u, u, u} I J) (X : I' → Type u) (j : J) :
    (piPre v P).Obj X j ≃ P.Obj (piAlong v X) j where
  toFun x := ⟨x.1, fun b p => x.2 ⟨b, p⟩⟩
  invFun y := ⟨y.1, fun d => y.2 d.1 d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end IPFunctor
