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

Following Niu–Spivak, *Polynomial Functors* (§7.1, Def 7.14), a **comonoid** in
the monoidal category `(Poly, ◃, y)` is a carrier `c : PFunctor` with a counit
`ε : c ⇆ y` and a comultiplication `δ : c ⇆ c ◃ c` satisfying counitality and
coassociativity. By the Ahman–Uustalu theorem (Niu–Spivak Thm 7.28), comonoids in
`Poly` correspond to small categories: `c.A` is the objects, the directions are the
outgoing morphisms, `ε` picks the identities, and `δ` is composition.
`PFunctor/Comonoid/Category.lean` extracts the category of a comonoid.

Counitality and coassociativity are lens equations, phrased through the unitor and
associator equivalences `compY` / `yComp` / `compAssoc` (`PFunctor.Lens.Equiv`).
A comonoid is *data*, not a predicate: one carrier can admit many comonoid
structures (Niu–Spivak Ex 7.39), so the laws are fields, not a `Prop`-class.

The primary instance is the **state comonoid** `stateComonoid S` on the
self-monomial `S y^S` (Niu–Spivak Ex 6.44 / 7.19): the contractible groupoid on
the state set `S`, whose comultiplication is the transition lens `Lens.fixState`
(`δ = (id, tgt, run)`) and whose counit is the stay-put self-loop. `comulN`
packages the canonical `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}`
(Niu–Spivak Prop 7.20) — the comonoid data underneath the `n`-step run `Run_n`
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
(Niu–Spivak Def 7.14): a carrier `c`, a counit `ε : c ⇆ y`, and a
comultiplication `δ : c ⇆ c ◃ c` satisfying left/right counitality and
coassociativity as lens equations (through the unitors `yComp` / `compY` and the
associator `compAssoc`). This is the polynomial encoding of a small category.
The law fields use the names of Mathlib's `CategoryTheory.ComonObj`:
`counit_comul`, `comul_counit` and `comul_assoc`. -/
-- The carrier's position and direction universes are independent; `checkUnivs`
-- sees only their joint contribution to the structure's resulting sort.
structure Comonoid where
  /-- The carrier polynomial (the "objects and morphisms"). -/
  carrier : PFunctor.{uA, uB}
  /-- The counit `ε : c ⇆ y` — selects the identity morphisms. Its universe
  instance agrees with the zeroth composition power of `carrier`. -/
  counit : Lens carrier y.{max uA uB, uB}
  /-- The comultiplication `δ : c ⇆ c ◃ c` — the composition operation. -/
  comul : Lens carrier (carrier ◃ carrier)
  /-- Left counitality: `λ ∘ (ε ◃ id) ∘ δ = id`. -/
  counit_comul : Lens.Equiv.yComp.toLens ∘ₗ (counit ◃ₗ Lens.id carrier) ∘ₗ comul
      = Lens.id carrier
  /-- Right counitality: `ρ ∘ (id ◃ ε) ∘ δ = id`. -/
  comul_counit : Lens.Equiv.compY.toLens ∘ₗ (Lens.id carrier ◃ₗ counit) ∘ₗ comul
      = Lens.id carrier
  /-- Coassociativity: `α ∘ (δ ◃ id) ∘ δ = (id ◃ δ) ∘ δ`. -/
  comul_assoc : Lens.Equiv.compAssoc.toLens ∘ₗ (comul ◃ₗ Lens.id carrier) ∘ₗ comul
      = (Lens.id carrier ◃ₗ comul) ∘ₗ comul

namespace Comonoid

@[deprecated (since := "2026-10-19")] alias comult := comul
@[deprecated (since := "2026-10-19")] alias counit_left := counit_comul
@[deprecated (since := "2026-10-19")] alias counit_right := comul_counit
@[deprecated (since := "2026-10-19")] alias coassoc := comul_assoc

/-! ## Morphisms of comonoids (retrofunctors) -/

/-- A morphism of composition comonoids (Niu–Spivak Def 7.49), called a
**retrofunctor** under the identification of polynomial comonoids with small
categories (Def 7.55). It is a lens on carriers that preserves identities and
composition. -/
structure Hom (C D : Comonoid.{uA, uB}) where
  /-- The underlying lens between carrier polynomials. -/
  toLens : Lens C.carrier D.carrier
  /-- Preservation of identity arrows. -/
  map_counit : D.counit ∘ₗ toLens = C.counit
  /-- Preservation of composition. -/
  map_comul : D.comul ∘ₗ toLens =
    (toLens ◃ₗ toLens) ∘ₗ C.comul

@[deprecated (since := "2026-10-19")] alias Hom.map_comult := Hom.map_comul

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
  map_comul := by simp

/-- Composition of retrofunctors, in diagrammatic order. -/
def Hom.comp {C D E : Comonoid.{uA, uB}} (f : Hom C D) (g : Hom D E) : Hom C E where
  toLens := g.toLens ∘ₗ f.toLens
  map_counit := by
    rw [← Lens.comp_assoc, g.map_counit, f.map_counit]
  map_comul := by
    calc
      E.comul ∘ₗ (g.toLens ∘ₗ f.toLens) =
          (E.comul ∘ₗ g.toLens) ∘ₗ f.toLens := rfl
      _ = ((g.toLens ◃ₗ g.toLens) ∘ₗ D.comul) ∘ₗ f.toLens := by
        rw [g.map_comul]
      _ = (g.toLens ◃ₗ g.toLens) ∘ₗ (D.comul ∘ₗ f.toLens) := rfl
      _ = (g.toLens ◃ₗ g.toLens) ∘ₗ
          ((f.toLens ◃ₗ f.toLens) ∘ₗ C.comul) := by
        rw [f.map_comul]
      _ = ((g.toLens ∘ₗ f.toLens) ◃ₗ (g.toLens ∘ₗ f.toLens)) ∘ₗ
          C.comul := by
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

/-- Morphisms in `Cat♯` are determined by their underlying lenses. -/
@[ext]
theorem hom_ext {C D : Comonoid.{uA, uB}} {f g : C ⟶ D} (h : f.toLens = g.toLens) : f = g :=
  Hom.ext f g h

@[simp] theorem id_toLens (C : Comonoid.{uA, uB}) :
    (𝟙 C : C ⟶ C).toLens = Lens.id C.carrier := rfl

@[simp] theorem comp_toLens {C D E : Comonoid.{uA, uB}} (f : C ⟶ D) (g : D ⟶ E) :
    (f ≫ g).toLens = g.toLens ∘ₗ f.toLens := rfl

/-! ## The `n`-fold comultiplication `δ^{(n)}` -/

/-- The `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}` of a comonoid, defined
recursively by `δ^{(0)} = ε` and `δ^{(n+1)} = (id ◃ δ^{(n)}) ∘ δ`. Niu–Spivak
Prop 7.20 recurses on the other factor, `δ^{(n+1)} = (δ^{(n)} ◃ id) ∘ δ`; the two
agree by the canonicity of Prop 7.20(d), that every bracketing of the `n`-fold
comultiplication agrees, which is not proved here. Only the definitional
unfolders `comulN_zero` / `comulN_succ` are. This is the comonoid data
underneath the `n`-step run `PFunctor.DynSystem.nStep`. -/
def comulN (C : Comonoid.{uA, uB}) : (n : ℕ) → Lens C.carrier (compNth C.carrier n)
  | 0 => C.counit
  | n + 1 => (Lens.id C.carrier ◃ₗ C.comulN n) ∘ₗ C.comul

@[deprecated (since := "2026-10-19")] alias comultN := comulN

@[simp] theorem comulN_zero (C : Comonoid.{uA, uB}) : C.comulN 0 = C.counit := rfl

@[deprecated (since := "2026-10-19")] alias comultN_zero := comulN_zero

@[simp] theorem comulN_succ (C : Comonoid.{uA, uB}) (n : ℕ) :
    C.comulN (n + 1) = (Lens.id C.carrier ◃ₗ C.comulN n) ∘ₗ C.comul := rfl

@[deprecated (since := "2026-10-19")] alias comultN_succ := comulN_succ

/-- A retrofunctor preserves every iterated comultiplication. This is the
finite-path extension of `map_counit` and `map_comul`, and is the form used by
`DynSystem.nStep` consumers. -/
theorem Hom.map_comulN {C D : Comonoid.{uA, uB}} (f : Hom C D) (n : ℕ) :
    D.comulN n ∘ₗ f.toLens = f.toLens.compNthMap n ∘ₗ C.comulN n := by
  induction n with
  | zero => simpa using f.map_counit
  | succ n ih =>
      have hleft :
          (Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ (f.toLens ◃ₗ f.toLens) =
            f.toLens ◃ₗ (f.toLens.compNthMap n ∘ₗ C.comulN n) := by
        calc
          _ = (Lens.id D.carrier ∘ₗ f.toLens) ◃ₗ
                (D.comulN n ∘ₗ f.toLens) :=
              (Lens.compMap_comp f.toLens f.toLens
                (Lens.id D.carrier) (D.comulN n)).symm
          _ = _ := by rw [Lens.id_comp, ih]
      have hright :
          (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              (Lens.id C.carrier ◃ₗ C.comulN n) =
            f.toLens ◃ₗ (f.toLens.compNthMap n ∘ₗ C.comulN n) := by
        calc
          _ = (f.toLens ∘ₗ Lens.id C.carrier) ◃ₗ
                (f.toLens.compNthMap n ∘ₗ C.comulN n) :=
              (Lens.compMap_comp (Lens.id C.carrier) (C.comulN n)
                f.toLens (f.toLens.compNthMap n)).symm
          _ = _ := by rw [Lens.comp_id]
      change ((Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ D.comul) ∘ₗ f.toLens =
        (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
          ((Lens.id C.carrier ◃ₗ C.comulN n) ∘ₗ C.comul)
      calc
        ((Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ D.comul) ∘ₗ f.toLens =
            (Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ
              (D.comul ∘ₗ f.toLens) := rfl
        _ = (Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ
              ((f.toLens ◃ₗ f.toLens) ∘ₗ C.comul) := by rw [f.map_comul]
        _ = ((Lens.id D.carrier ◃ₗ D.comulN n) ∘ₗ
              (f.toLens ◃ₗ f.toLens)) ∘ₗ C.comul := rfl
        _ = ((f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              (Lens.id C.carrier ◃ₗ C.comulN n)) ∘ₗ C.comul := by
                exact congrArg (fun l => l ∘ₗ C.comul) (hleft.trans hright.symm)
        _ = (f.toLens ◃ₗ f.toLens.compNthMap n) ∘ₗ
              ((Lens.id C.carrier ◃ₗ C.comulN n) ∘ₗ C.comul) :=
                Lens.comp_assoc _ _ _

@[deprecated (since := "2026-10-19")] alias Hom.map_comultN := Hom.map_comulN

/-! ## State systems (Niu–Spivak Ex 7.22) -/

/-- A comonoid **is a state system** when, at every object, its codomain map
`d ↦ cod d` (the second component of `δ`'s position action) is a bijection: from
each object there is exactly one morphism to each object (a contractible
groupoid). A predicate, never a field (Niu–Spivak Ex 7.22).

Reference API: exercised in `PolyFunTest/PFunctor/Comonoid.lean`, staged for
downstream state-system consumers. -/
def IsStateSystem (C : Comonoid.{uA, uB}) : Prop :=
  ∀ a : C.carrier.A, Function.Bijective (C.comul.toFunA a).2

end Comonoid

/-! ## The state comonoid `S y^S` -/

/-- The **state comonoid** on `S y^S` (Niu–Spivak Ex 6.44 / 7.19): the
contractible groupoid on the state set `S`. Its comultiplication is the
transition lens `Lens.fixState` (Example 6.44, `δ = (id, tgt, run)`) and its
counit is the stay-put self-loop `s ↦ (⋆ ↦ s)`. -/
@[reducible]
def stateComonoid (S : Type u) : Comonoid.{u, u} where
  carrier := selfMonomial S
  counit := (fun _ => PUnit.unit) ⇆ (fun s _ => s)
  comul := Lens.fixState
  counit_comul := rfl
  comul_counit := rfl
  comul_assoc := rfl

@[simp] theorem stateComonoid_carrier (S : Type u) :
    (stateComonoid S).carrier = selfMonomial S := rfl

@[simp] theorem stateComonoid_comul (S : Type u) :
    (stateComonoid S).comul = Lens.fixState := rfl

@[deprecated (since := "2026-10-19")] alias stateComonoid_comult := stateComonoid_comul

@[simp, grind =] theorem stateComonoid_counit (S : Type u) :
    (stateComonoid S).counit = ((fun _ => PUnit.unit) ⇆ (fun s _ => s)) := rfl

namespace Comonoid.Hom

variable {S T : Type u}

/-- A very-well-behaved state lens is exactly a retrofunctor between state
comonoids. Preservation of the counit is `GetPut`; preservation of
comultiplication splits into `PutGet` on positions and `PutPut` on directions.
The argument is a get/put `Lens.State`. -/
def ofStateLens (L : Lens.State S T) [L.IsVeryWellBehaved] :
    Comonoid.Hom (stateComonoid S) (stateComonoid T) where
  toLens := L
  map_counit := by
    refine Lens.ext _ _ (fun _ => rfl) (fun s => ?_)
    funext _
    exact Lens.State.put_get (L := L) s
  map_comul := by
    have hA : ∀ s, ((stateComonoid T).comul ∘ₗ L).toFunA s =
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comul).toFunA s := fun s => by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (funext fun t => (Lens.State.get_put (L := L) s t).symm)
    apply Lens.ext _ _ hA
    intro s
    apply eq_of_heq
    have hraw : ((stateComonoid T).comul ∘ₗ L).toFunB s =
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comul).toFunB s := by
      funext d
      exact (Lens.State.put_put (L := L) s d.1 d.2).symm
    have hcast : (hA s ▸ ((L ◃ₗ L) ∘ₗ (stateComonoid S).comul).toFunB s) ≍
        ((L ◃ₗ L) ∘ₗ (stateComonoid S).comul).toFunB s :=
      eqRec_heq_self _ _
    exact (heq_of_eq hraw).trans hcast.symm

@[simp] theorem ofStateLens_toLens (L : Lens.State S T) [L.IsVeryWellBehaved] :
    (ofStateLens L).toLens = L := rfl

/-- The underlying state lens of a retrofunctor between state comonoids obeys
the three very-well-behaved lens laws. -/
theorem stateLens_isVeryWellBehaved
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    Lens.State.IsVeryWellBehaved (show Lens.State S T from F.toLens) where
  get_put s t := (congrArg (fun l => (l.toFunA s).2 t) F.map_comul).symm
  put_get s := congrArg (fun l => l.toFunB s PUnit.unit) F.map_counit
  put_put s t₁ t₂ := (congrArg (fun l => l.toFunB s ⟨t₁, t₂⟩) F.map_comul).symm

/-- Retrofunctors between state comonoids are equivalent to ordinary state
lenses equipped with the very-well-behaved laws. The subtype records genuine
laws; it is not a second representation of the underlying lens. This
equivalence is universe-local because `Comonoid.Hom` compares fixed universe
instances of the composition unit. -/
def stateLensEquiv :
    Comonoid.Hom (stateComonoid S) (stateComonoid T) ≃
      { L : Lens.State S T // L.IsVeryWellBehaved } where
  toFun F := ⟨show Lens.State S T from F.toLens, stateLens_isVeryWellBehaved F⟩
  invFun L :=
    have : L.1.IsVeryWellBehaved := L.2
    ofStateLens L.1
  left_inv _ := Hom.ext _ _ rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem stateLensEquiv_apply_val
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    (stateLensEquiv F).1 = F.toLens := rfl

@[simp] theorem stateLensEquiv_symm_toLens
    (L : { L : Lens.State S T // L.IsVeryWellBehaved }) :
    ((stateLensEquiv (S := S) (T := T)).symm L).toLens = L.1 := rfl

end Comonoid.Hom

/-- The state comonoid is a state system: its codomain map `s₁ ↦ s₁` is the
identity, hence bijective (Niu–Spivak Ex 7.22). -/
theorem isStateSystem_stateComonoid (S : Type u) :
    (stateComonoid S).IsStateSystem :=
  fun _ => Function.bijective_id

end PFunctor
