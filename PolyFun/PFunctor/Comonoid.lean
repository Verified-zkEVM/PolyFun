/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Composite
public import PolyFun.PFunctor.Lens.State
public import Mathlib.CategoryTheory.Category.Basic
import Batteries.Tactic.Lint

/-!
# Comonoids in the composition-monoidal category

Following Spivak–Niu, *Polynomial Functors* (§7.1, Def 7.14), a **comonoid** in
the monoidal category `(Poly, ◃, y)` is a carrier `c : PFunctor` with a counit
`ε : c ⇆ y` and a comultiplication `δ : c ⇆ c ◃ c` satisfying counitality and
coassociativity. Comonoids in `Poly` are exactly small categories: `c.A` is the
objects, the directions are the outgoing morphisms, `ε` picks the identities, and
`δ` is composition.

Counitality and coassociativity are lens equations, phrased through the unitor and
associator equivalences `compX` / `XComp` / `compAssoc` (`PFunctor.Lens.Equiv`).
A comonoid is *data*, not a predicate: one carrier can admit many comonoid
structures (Spivak–Niu Ex 7.39), so the laws are fields, not a `Prop`-class.

The primary instance is the **state comonoid** `stateComonoid S` on the
self-monomial `S y^S` (Spivak–Niu Ex 6.44 / 7.19): the contractible groupoid on
the state set `S`, whose comultiplication is the transition lens `Lens.fixState`
(`δ = (id, tgt, run)`) and whose counit is the stay-put self-loop. `comultN`
packages the canonical `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}`
(Spivak–Niu Prop 7.20) — the comonoid data underneath the `n`-step run `Run_n`
(`PFunctor.DynSystem.nStep`).

The layer is kept à-la-carte (explicit lens laws) rather than routed through a
`MonoidalCategory (Poly, ◃, y)` instance, matching the rest of PolyFun's
monoidal machinery. The carrier's position and direction universes are
independent, matching `PFunctor`; the counit's copy of `y` is instantiated at
the universe of `compNth carrier 0` so the iterated comultiplication has a
uniform codomain.
-/

@[expose] public section

universe u uA uB

open CategoryTheory

namespace PFunctor

/-! ## The comonoid structure -/

set_option linter.checkUnivs false in
/-- A **comonoid** in the composition-monoidal category `(Poly, ◃, y)`
(Spivak–Niu Def 7.14): a carrier `c`, a counit `ε : c ⇆ y`, and a
comultiplication `δ : c ⇆ c ◃ c` satisfying left/right counitality and
coassociativity as lens equations (through the unitors `XComp` / `compX` and the
associator `compAssoc`). This is the polynomial encoding of a small category. -/
-- The carrier's position and direction universes are independent; `checkUnivs`
-- sees only their joint contribution to the structure's resulting sort.
structure Comonoid where
  /-- The carrier polynomial (the "objects and morphisms"). -/
  carrier : PFunctor.{uA, uB}
  /-- The counit `ε : c ⇆ y` — selects the identity morphisms. Its universe
  instance agrees with the zeroth composition power of `carrier`. -/
  counit : Lens carrier X.{max uA uB, uB}
  /-- The comultiplication `δ : c ⇆ c ◃ c` — the composition operation. -/
  comult : Lens carrier (carrier ◃ carrier)
  /-- Left counitality: `λ ∘ (ε ◃ id) ∘ δ = id`. -/
  counit_left : Lens.Equiv.XComp.toLens ∘ₗ (counit ◃ₗ Lens.id carrier) ∘ₗ comult
      = Lens.id carrier
  /-- Right counitality: `ρ ∘ (id ◃ ε) ∘ δ = id`. -/
  counit_right : Lens.Equiv.compX.toLens ∘ₗ (Lens.id carrier ◃ₗ counit) ∘ₗ comult
      = Lens.id carrier
  /-- Coassociativity: `α ∘ (δ ◃ id) ∘ δ = (id ◃ δ) ∘ δ`. -/
  coassoc : Lens.Equiv.compAssoc.toLens ∘ₗ (comult ◃ₗ Lens.id carrier) ∘ₗ comult
      = (Lens.id carrier ◃ₗ comult) ∘ₗ comult

namespace Comonoid

/-! ## Morphisms of comonoids (retrofunctors) -/

/-- A morphism of composition comonoids, called a **retrofunctor** under the
identification of polynomial comonoids with small categories (Niu–Spivak,
Def. 7.55). It is a lens on carriers that preserves identities and composition. -/
structure Hom (C D : Comonoid.{uA, uB}) where
  /-- The underlying lens between carrier polynomials. -/
  toLens : Lens C.carrier D.carrier
  /-- Preservation of identity arrows. -/
  map_counit : D.counit ∘ₗ toLens = C.counit
  /-- Preservation of composition. -/
  map_comult : D.comult ∘ₗ toLens =
    (toLens ◃ₗ toLens) ∘ₗ C.comult

instance {C D : Comonoid.{uA, uB}} : Coe (Hom C D) (Lens C.carrier D.carrier) :=
  ⟨Hom.toLens⟩

@[ext]
theorem Hom.ext {C D : Comonoid.{uA, uB}} (f g : Hom C D)
    (h : f.toLens = g.toLens) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity retrofunctor. -/
def Hom.id (C : Comonoid.{uA, uB}) : Hom C C where
  toLens := Lens.id C.carrier
  map_counit := rfl
  map_comult := by simp

/-- Composition of retrofunctors, in diagrammatic order. -/
def Hom.comp {C D E : Comonoid.{uA, uB}} (f : Hom C D) (g : Hom D E) : Hom C E where
  toLens := g.toLens ∘ₗ f.toLens
  map_counit := by
    rw [← Lens.comp_assoc, g.map_counit, f.map_counit]
  map_comult := by
    calc
      E.comult ∘ₗ (g.toLens ∘ₗ f.toLens) =
          (E.comult ∘ₗ g.toLens) ∘ₗ f.toLens := rfl
      _ = ((g.toLens ◃ₗ g.toLens) ∘ₗ D.comult) ∘ₗ f.toLens := by
        rw [g.map_comult]
      _ = (g.toLens ◃ₗ g.toLens) ∘ₗ (D.comult ∘ₗ f.toLens) := rfl
      _ = (g.toLens ◃ₗ g.toLens) ∘ₗ
          ((f.toLens ◃ₗ f.toLens) ∘ₗ C.comult) := by
        rw [f.map_comult]
      _ = ((g.toLens ∘ₗ f.toLens) ◃ₗ (g.toLens ∘ₗ f.toLens)) ∘ₗ
          C.comult := by
        rw [Lens.compMap_comp, Lens.comp_assoc]

@[simp] theorem Hom.id_toLens (C : Comonoid.{uA, uB}) :
    (Hom.id C).toLens = Lens.id C.carrier := rfl

@[simp] theorem Hom.comp_toLens {C D E : Comonoid.{uA, uB}}
    (f : Hom C D) (g : Hom D E) :
    (f.comp g).toLens = g.toLens ∘ₗ f.toLens := rfl

@[simp] theorem Hom.id_comp {C D : Comonoid.{uA, uB}} (f : Hom C D) :
    (Hom.id C).comp f = f :=
  Hom.ext _ _ (Lens.comp_id f.toLens)

@[simp] theorem Hom.comp_id {C D : Comonoid.{uA, uB}} (f : Hom C D) :
    f.comp (Hom.id D) = f :=
  Hom.ext _ _ (Lens.id_comp f.toLens)

theorem Hom.comp_assoc {C D E F : Comonoid.{uA, uB}}
    (f : Hom C D) (g : Hom D E) (h : Hom E F) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Hom.ext _ _ (Lens.comp_assoc h.toLens g.toLens f.toLens)

/-- The category of composition comonoids and retrofunctors (`Cat♯`). -/
instance : Category Comonoid.{uA, uB} where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-! ## The `n`-fold comultiplication `δ^{(n)}` -/

/-- The `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}` of a comonoid, defined
recursively by `δ^{(0)} = ε` and `δ^{(n+1)} = (id ◃ δ^{(n)}) ∘ δ`
(Spivak–Niu Prop 7.20). Only the definitional unfolders `comultN_zero` /
`comultN_succ` are proved here; the canonicity of Prop 7.20(d) — that every
bracketing of the `n`-fold comultiplication agrees — is a follow-on. This is
the comonoid data underneath the `n`-step run `PFunctor.DynSystem.nStep`. -/
def comultN (C : Comonoid.{uA, uB}) : (n : ℕ) → Lens C.carrier (compNth C.carrier n)
  | 0 => C.counit
  | n + 1 => (Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult

@[simp] theorem comultN_zero (C : Comonoid.{uA, uB}) : C.comultN 0 = C.counit := rfl

@[simp] theorem comultN_succ (C : Comonoid.{uA, uB}) (n : ℕ) :
    C.comultN (n + 1) = (Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult := rfl

/-- A retrofunctor preserves every iterated comultiplication. This is the
finite-path extension of `map_counit` and `map_comult`, and is the form used by
`DynSystem.nStep` consumers. -/
theorem Hom.map_comultN {C D : Comonoid.{uA, uB}} (f : Hom C D) (n : ℕ) :
    D.comultN n ∘ₗ f.toLens = f.toLens.compNthMap n ∘ₗ C.comultN n := by
  induction n with
  | zero => simpa using f.map_counit
  | succ n ih =>
      have hleft :
          (Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ (f.toLens ◃ₗ f.toLens) =
            f.toLens ◃ₗ (f.toLens.compNthMap n ∘ₗ C.comultN n) := by
        calc
          _ = (Lens.id D.carrier ∘ₗ f.toLens) ◃ₗ
                (D.comultN n ∘ₗ f.toLens) :=
              (Lens.compMap_comp f.toLens f.toLens
                (Lens.id D.carrier) (D.comultN n)).symm
          _ = _ := by rw [Lens.id_comp, ih]
      have hright :
          (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              (Lens.id C.carrier ◃ₗ C.comultN n) =
            f.toLens ◃ₗ (f.toLens.compNthMap n ∘ₗ C.comultN n) := by
        calc
          _ = (f.toLens ∘ₗ Lens.id C.carrier) ◃ₗ
                (f.toLens.compNthMap n ∘ₗ C.comultN n) :=
              (Lens.compMap_comp (Lens.id C.carrier) (C.comultN n)
                f.toLens (f.toLens.compNthMap n)).symm
          _ = _ := by rw [Lens.comp_id]
      change ((Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ D.comult) ∘ₗ f.toLens =
        (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
          ((Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult)
      calc
        ((Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ D.comult) ∘ₗ f.toLens =
            (Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ
              (D.comult ∘ₗ f.toLens) := rfl
        _ = (Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ
              ((f.toLens ◃ₗ f.toLens) ∘ₗ C.comult) := by rw [f.map_comult]
        _ = ((Lens.id D.carrier ◃ₗ D.comultN n) ∘ₗ
              (f.toLens ◃ₗ f.toLens)) ∘ₗ C.comult := rfl
        _ = ((f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              (Lens.id C.carrier ◃ₗ C.comultN n)) ∘ₗ C.comult := by
                exact congrArg (fun l => l ∘ₗ C.comult) (hleft.trans hright.symm)
        _ = (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              ((Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult) :=
                Lens.comp_assoc _ _ _

/-! ## State systems (Spivak–Niu Ex 7.22) -/

/-- A comonoid **is a state system** when, at every object, its codomain map
`d ↦ cod d` (the second component of `δ`'s position action) is a bijection: from
each object there is exactly one morphism to each object (a contractible
groupoid). A predicate, never a field (Spivak–Niu Ex 7.22).

Reference API: exercised in `PolyFunTest/PFunctor/Comonoid.lean`, staged for
downstream state-system consumers. -/
def IsStateSystem (C : Comonoid.{uA, uB}) : Prop :=
  ∀ a : C.carrier.A, Function.Bijective (C.comult.toFunA a).2

end Comonoid

/-! ## The state comonoid `S y^S` -/

/-- The **state comonoid** on `S y^S` (Spivak–Niu Ex 6.44 / 7.19): the
contractible groupoid on the state set `S`. Its comultiplication is the
transition lens `Lens.fixState` (Example 6.44, `δ = (id, tgt, run)`) and its
counit is the stay-put self-loop `s ↦ (⋆ ↦ s)`. -/
def stateComonoid (S : Type u) : Comonoid.{u, u} where
  carrier := selfMonomial S
  counit := (fun _ => PUnit.unit) ⇆ (fun s _ => s)
  comult := Lens.fixState
  counit_left := rfl
  counit_right := rfl
  coassoc := rfl

@[simp] theorem stateComonoid_carrier (S : Type u) :
    (stateComonoid S).carrier = selfMonomial S := rfl

@[simp] theorem stateComonoid_comult (S : Type u) :
    (stateComonoid S).comult = Lens.fixState := rfl

@[simp, grind =] theorem stateComonoid_counit (S : Type u) :
    (stateComonoid S).counit = ((fun _ => PUnit.unit) ⇆ (fun s _ => s)) := rfl

namespace Comonoid.Hom

variable {S T : Type u}

/-- A very-well-behaved state lens is exactly a retrofunctor between state
comonoids. Preservation of the counit is `GetPut`; preservation of
comultiplication splits into `PutGet` on positions and `PutPut` on directions. -/
def ofStateLens (L : Lens.State S T) [L.IsVeryWellBehaved] :
    Comonoid.Hom (stateComonoid S) (stateComonoid T) where
  toLens := L
  map_counit := by
    refine Lens.ext _ _ (fun _ => rfl) (fun s => ?_)
    funext _
    exact Lens.State.put_get (L := L) s
  map_comult := by
    let hA : ∀ s, ((stateComonoid T).comult ∘ₗ L).toFunA s =
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comult).toFunA s := fun s => by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (funext fun t => (Lens.State.get_put (L := L) s t).symm)
    apply Lens.ext _ _ hA
    intro s
    apply eq_of_heq
    have hraw : ((stateComonoid T).comult ∘ₗ L).toFunB s =
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comult).toFunB s := by
      funext d
      exact (Lens.State.put_put (L := L) s d.1 d.2).symm
    have hcast : (hA s ▸ ((L ◃ₗ L) ∘ₗ (stateComonoid S).comult).toFunB s) ≍
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comult).toFunB s := by
      exact eqRec_heq_self _ _
    exact (heq_of_eq hraw).trans hcast.symm

@[simp] theorem ofStateLens_toLens (L : Lens.State S T) [L.IsVeryWellBehaved] :
    (ofStateLens L).toLens = L := rfl

/-- The underlying state lens of a retrofunctor between state comonoids obeys
the three very-well-behaved lens laws. -/
theorem stateLens_isVeryWellBehaved
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    Lens.State.IsVeryWellBehaved (show Lens.State S T from F.toLens) where
  get_put s t := by
    have h := congrArg (fun l => (l.toFunA s).2 t) F.map_comult
    exact h.symm
  put_get s := by
    have h := congrArg (fun l => l.toFunB s PUnit.unit) F.map_counit
    exact h
  put_put s t₁ t₂ := by
    have h := congrArg (fun l => l.toFunB s ⟨t₁, t₂⟩) F.map_comult
    exact h.symm

/-- Retrofunctors between state comonoids are equivalent to ordinary state
lenses equipped with the very-well-behaved laws. The subtype records genuine
laws; it is not a second representation of the underlying lens. This
equivalence is universe-local because `Comonoid.Hom` compares fixed universe
instances of the composition unit. -/
def stateLensEquiv :
    Comonoid.Hom (stateComonoid S) (stateComonoid T) ≃
      { L : Lens.State S T // L.IsVeryWellBehaved } where
  toFun F := ⟨show Lens.State S T from F.toLens, stateLens_isVeryWellBehaved F⟩
  invFun L := by
    letI : L.1.IsVeryWellBehaved := L.2
    exact ofStateLens L.1
  left_inv F := Hom.ext _ _ rfl
  right_inv L := by
    apply Subtype.ext
    rfl

@[simp] theorem stateLensEquiv_apply_val
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    (stateLensEquiv F).1 = F.toLens := rfl

@[simp] theorem stateLensEquiv_symm_toLens
    (L : { L : Lens.State S T // L.IsVeryWellBehaved }) :
    ((stateLensEquiv (S := S) (T := T)).symm L).toLens = L.1 := rfl

end Comonoid.Hom

/-- The state comonoid is a state system: its codomain map `s₁ ↦ s₁` is the
identity, hence bijective (Spivak–Niu Ex 7.22). -/
theorem isStateSystem_stateComonoid (S : Type u) :
    (stateComonoid S).IsStateSystem :=
  fun _ => Function.bijective_id

end PFunctor
