/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Relative monads

A relative monad over a functor `J : C ⥤ D` (Altenkirch, Chapman and Uustalu, *Monads need not be
endofunctors*, LMCS 2015) has a unit `J X ⟶ T X` and an extension of `J X ⟶ T Y` to
`T X ⟶ T Y`; over the identity functor it is a monad. This file presents relative monads in two
ways.

* `CategoryTheory.RelativeMonad C D J`, a structure on categories, with its induced functor and
  natural transformation, the monad of a relative monad over the identity (`monadOfId`),
  transport along a natural isomorphism (`ofNatIso`), precomposition (`precompose`), products
  (`prod`), and morphisms between relative monads over different targets (`RelativeMonadHom`).
  Postcomposition with a fully faithful functor is not provided.
* Type classes on type constructors: `RelativePure`, `RelativeBind`, `RelativeFunctor` and
  `RelativeMonad j m` over `j : Type u → Type w`, with laws (`LawfulRelativeFunctor`,
  `LawfulRelativeMonad`), isomorphisms of monads (`MonadIso`) and morphisms
  (`RelativeMonadMorphism`). Over `j := Id` they give the ordinary operations, as definitions
  (`RelativeMonad.monadOfId` and its companions) rather than instances, since an instance would
  enter every search for a `Monad`. A relative monad of relational specifications has the
  signature `Type u₁ × Type u₂ → Type v₁ × Type v₂`, outside this presentation, and is an
  instance of the categorical structure.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [CategoryTheory universes].
variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The data of a **relative monad** over a functor `J : C ⟶ D` consists of:
- a map between objects `T : C → D`
- a natural transformation `η : ∀ {X}, J X ⟶ T X`
- a natural transformation `μ : ∀ {X Y}, (J X ⟶ T Y) ⟶ (T X ⟶ T Y)`
satisfying three equations:
- `μ_{X, X} ∘ η_X = 1_{T X}` (left unit)
- `∀ f, η_X ≫ μ_{X, Y} = f` (right unit)
- `∀ f g, μ_{X, Z} (f ≫ μ_{Y, Z} g) = μ_{X, Y} f ≫ μ_{Y, Z} g` (associativity)
-/
structure RelativeMonad (J : C ⥤ D) where
  /-- The monadic mapping on objects. -/
  T : C → D
  /-- The unit for the relative monad. -/
  η : ∀ {X}, J.obj X ⟶ T X
  /-- The multiplication for the monad. -/
  μ : ∀ {X Y}, ((J.obj X) ⟶ (T Y)) → ((T X) ⟶ (T Y))
  /-- `μ` applied to `η` is identity. -/
  left_unit : ∀ {X}, μ η = 𝟙 (T X) := by aesop_cat
  /-- `η` composed with `μ` is identity. -/
  right_unit : ∀ {X Y}, ∀ f : (J.obj X) ⟶ (T Y), η ≫ (μ f) = f := by aesop_cat
  /-- `μ` is associative. -/
  assoc : ∀ {X Y Z}, ∀ f : (J.obj X) ⟶ (T Y), ∀ g : (J.obj Y) ⟶ (T Z),
    μ (f ≫ μ g) = (μ f) ≫ (μ g) := by aesop_cat

attribute [simp, reassoc] RelativeMonad.left_unit RelativeMonad.assoc
attribute [reassoc (attr := simp)] RelativeMonad.right_unit

namespace RelativeMonad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {J : C ⥤ D}

/-- The functor induced by a relative monad.

**Note:** this is _not_ the same as the underlying functor of the relative monad. -/
@[simps]
def inducedFunctor (M : RelativeMonad C D J) : C ⥤ D where
  obj X := M.T X
  map f := M.μ (J.map f ≫ M.η)
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← assoc, Category.assoc, right_unit]

/-- The natural transformation from the underlying functor of the relative monad, to the functor
induced by the relative monad. -/
def inducedNatTrans (M : RelativeMonad C D J) : NatTrans J M.inducedFunctor where
  app X := M.η
  naturality X Y f := by
    simp only [inducedFunctor_map]
    exact (M.right_unit (f := J.map f ≫ M.η)).symm

/-- If a relative monad is over the identity functor, it is a monad. -/
def monadOfId (M : RelativeMonad C _ (𝟭 _)) : Monad C where
  toFunctor := M.inducedFunctor
  η :=
    { app := fun X => M.η
      naturality := fun X Y f => by
        simp only [Functor.id_map, inducedFunctor_map]
        exact (M.right_unit (f := f ≫ M.η)).symm }
  μ := NatTrans.mk (fun X => M.μ (𝟙 (M.T X)))
    (fun X Y f => by
      simp only [Functor.comp_map, inducedFunctor_map,
        Functor.id_obj, Functor.id_map]
      calc
        M.μ (M.μ (f ≫ M.η) ≫ M.η) ≫ M.μ (𝟙 (M.T Y))
            = M.μ ((M.μ (f ≫ M.η) ≫ M.η) ≫ M.μ (𝟙 (M.T Y))) := by
                symm
                exact M.assoc (f := M.μ (f ≫ M.η) ≫ M.η) (g := 𝟙 (M.T Y))
        _ = M.μ (M.μ (f ≫ M.η)) := by
              congr 1
              simp [Category.assoc]
        _ = M.μ (𝟙 (M.T X) ≫ M.μ (f ≫ M.η)) := by simp
        _ = M.μ (𝟙 (M.T X)) ≫ M.μ (f ≫ M.η) := by
              exact M.assoc (f := 𝟙 (M.T X)) (g := f ≫ M.η))
  left_unit X := by
    exact M.right_unit (f := 𝟙 (M.T X))
  right_unit X := by
    simp only [Functor.id_obj]
    calc
      M.μ (M.η ≫ M.η) ≫ M.μ (𝟙 (M.T X))
          = M.μ ((M.η ≫ M.η) ≫ M.μ (𝟙 (M.T X))) := by
              symm
              exact M.assoc (f := M.η ≫ M.η) (g := 𝟙 (M.T X))
      _ = M.μ M.η := by
            congr 1
            simp [Category.assoc]
      _ = 𝟙 (M.T X) := by simp
  assoc X := by
    calc
      M.μ (M.μ (𝟙 (M.T X)) ≫ M.η) ≫ M.μ (𝟙 (M.T X))
          = M.μ ((M.μ (𝟙 (M.T X)) ≫ M.η) ≫ M.μ (𝟙 (M.T X))) := by
              symm
              exact M.assoc (f := M.μ (𝟙 (M.T X)) ≫ M.η) (g := 𝟙 (M.T X))
      _ = M.μ (M.μ (𝟙 (M.T X))) := by
            congr 1
            simp [Category.assoc]
      _ = M.μ (𝟙 (M.T (M.T X)) ≫ M.μ (𝟙 (M.T X))) := by simp
      _ = M.μ (𝟙 (M.T (M.T X))) ≫ M.μ (𝟙 (M.T X)) := by
            exact M.assoc (f := 𝟙 (M.T (M.T X))) (g := 𝟙 (M.T X))

/-- Transport a relative monad along a natural isomorphism of the underlying functor. -/
def ofNatIso {J₁ J₂ : C ⥤ D} (φ : J₁ ≅ J₂) (M : RelativeMonad C D J₁) : RelativeMonad C D J₂ where
  T := M.T
  η := φ.inv.app _ ≫ M.η
  μ := fun f => M.μ (φ.hom.app _ ≫ f)
  assoc f g := by rw [← assoc]; simp

/-- Precompose a relative monad `M : RelativeMonad C D J` along a functor `J' : C' ⥤ C`. -/
def precompose {C' : Type u₃} [Category.{v₃} C'] (J' : C' ⥤ C) (M : RelativeMonad C D J) :
    RelativeMonad C' D (J' ⋙ J) where
  T := M.T ∘ J'.obj
  η := M.η
  μ := M.μ
  left_unit := M.left_unit
  right_unit f := M.right_unit f
  assoc f g := M.assoc f g

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : C₁ ⥤ D₁} {J₂ : C₂ ⥤ D₂}

/-- The product of two relative monads is a relative monad on the corresponding product
categories. -/
@[simps!]
def prod (M₁ : RelativeMonad C₁ D₁ J₁) (M₂ : RelativeMonad C₂ D₂ J₂) :
    RelativeMonad (C₁ × C₂) (D₁ × D₂) (Functor.prod J₁ J₂) where
  T := fun X => (M₁.T X.fst, M₂.T X.snd)
  η := ⟨M₁.η, M₂.η⟩
  μ := fun f => ⟨M₁.μ f.fst, M₂.μ f.snd⟩
  left_unit := Prod.ext M₁.left_unit M₂.left_unit
  right_unit f := Prod.ext (M₁.right_unit f.fst) (M₂.right_unit f.snd)
  assoc f g := Prod.ext (M₁.assoc f.fst g.fst) (M₂.assoc f.snd g.snd)

end RelativeMonad

variable {C : Type u₁} [Category.{v₁} C] {D₁ : Type u₂} [Category.{v₂} D₁]
  {D₂ : Type u₃} [Category.{v₃} D₂] {J₁ : C ⥤ D₁} {J₂ : C ⥤ D₂}

/-- A morphism of relative monads, where the two ending categories may be different. We require
another functor & a natural isomorphism to correct for this discrepancy. -/
structure RelativeMonadHom (M₁ : RelativeMonad C D₁ J₁) (M₂ : RelativeMonad C D₂ J₂) where
  /-- The functor between the target categories. -/
  J₁₂ : D₁ ⥤ D₂
  /-- The second root functor as the first followed by `J₁₂`. -/
  φ : J₂ ≅ (J₁ ⋙ J₁₂)
  /-- The components of the morphism. -/
  map : ∀ {X}, J₁₂.obj (M₁.T X) ⟶ M₂.T X
  map_η : ∀ {X}, J₁₂.map M₁.η ≫ map = φ.inv.app X ≫ M₂.η := by aesop_cat
  map_μ : ∀ {X Y}, ∀ f : (J₁.obj X) ⟶ M₁.T Y,
    J₁₂.map (M₁.μ f) ≫ map = map ≫ M₂.μ (φ.hom.app _ ≫ J₁₂.map f ≫ map) := by aesop_cat

attribute [reassoc (attr := simp)] RelativeMonadHom.map_η RelativeMonadHom.map_μ

end CategoryTheory

/-! ## Relative monads on type constructors

The classes below present a relative monad over a type constructor `j : Type u → Type w`: the
operations take `j`-values where an ordinary monad takes plain values. -/

universe u w v

/-- Type class for the relative pure operation -/
class RelativePure (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative pure operation -/
  pureᵣ : {α : Type u} → j α → f α

export RelativePure (pureᵣ)

/-- Type class for the relative bind operation -/
class RelativeBind (j : Type u → Type w) (m : Type u → Type v) where
  /-- The relative bind operation -/
  bindᵣ : {α β : Type u} → m α → (j α → m β) → m β

export RelativeBind (bindᵣ)

/-- Type class for the relative map operation -/
class RelativeFunctor (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative map operation -/
  mapᵣ : {α β : Type u} → (j α → j β) → (f α → f β)
  /-- Replace every value by a constant. -/
  mapConstᵣ : {α β : Type u} → j α → f β → f α := mapᵣ ∘ Function.const _

export RelativeFunctor (mapᵣ mapConstᵣ)

/- The relative interface stops at `pure`, `bind`, and `map`: sequencing operations have no
relative counterpart here, since a relative applicative would need the sequencing structure on
the root functor as well. -/

@[inherit_doc] infixl:55  " >>=ᵣ " => RelativeBind.bindᵣ
@[inherit_doc] infixr:100 " <$>ᵣ " => RelativeFunctor.mapᵣ

/-- Type class for the relative monad -/
class RelativeMonad (j : Type u → Type w) (m : Type u → Type v)
    extends RelativePure j m, RelativeBind j m, RelativeFunctor j m where
  mapᵣ f x := bindᵣ x (pureᵣ ∘ f)

/-- The `Functor` structure of a relative monad over a functor `j`. -/
@[reducible] def RelativeMonad.toFunctor {j : Type u → Type w} [Functor j]
    {m : Type u → Type v}
    [RelativeMonad j m] : Functor m where
  map f x := bindᵣ (j := j) x (pureᵣ ∘ (Functor.map f))

/-- The `Seq` structure of a relative monad over a `Seq` type constructor `j`. -/
@[reducible] def RelativeMonad.toSeq {j : Type u → Type w} [Seq j]
    {m : Type u → Type v}
    [RelativeMonad j m] : Seq m where
  seq f x := bindᵣ (j := j) (m := m) f (fun y => mapᵣ (y <*> ·) (x ()))

variable {j : Type u → Type w} {m f : Type u → Type v}

/-- A relative `pure` over `Id` is a `pure`. -/
@[reducible] def RelativePure.pureOfId [RelativePure Id f] : Pure f where
  pure := @pureᵣ Id f _

/-- A relative `bind` over `Id` is a `bind`. -/
@[reducible] def RelativeBind.bindOfId [RelativeBind Id m] : Bind m where
  bind := @bindᵣ Id m _

/-- A relative map over `Id` is a `Functor`. -/
@[reducible] def RelativeFunctor.functorOfId [RelativeFunctor Id f] : Functor f where
  map := @mapᵣ Id f _
  mapConst := @mapConstᵣ Id f _

/-- A relative monad over `Id` is a `Monad`. -/
@[reducible] def RelativeMonad.monadOfId [RelativeMonad Id m] : Monad m where
  pure := @pureᵣ Id m _
  bind := @bindᵣ Id m _

section Lawful

/-- A relative map that preserves identities and composites and whose constant map is the map of a
constant function. -/
class LawfulRelativeFunctor (j : Type u → Type w) (f : Type u → Type v)
    [RelativeFunctor j f] where

  map_constᵣ {α β : Type u} : (mapConstᵣ : j α → f β → _) = mapᵣ ∘ (Function.const _)

  id_mapᵣ {α : Type u} (x : f α) : (id : j α → _) <$>ᵣ x = x

  comp_mapᵣ {α β γ : Type u} (g : j α → j β) (h : j β → j γ) (x : f α) :
    (h ∘ g) <$>ᵣ x = h <$>ᵣ g <$>ᵣ x

export LawfulRelativeFunctor (map_constᵣ id_mapᵣ comp_mapᵣ)

attribute [simp] id_mapᵣ

variable {α β γ : Type u}

@[simp] theorem id_mapᵣ' [RelativeFunctor j f] [LawfulRelativeFunctor j f] (x : f α) :
    (fun a : j α => a) <$>ᵣ x = x :=
  id_mapᵣ x

@[simp] theorem RelativeFunctor.map_map [RelativeFunctor j f] [LawfulRelativeFunctor j f]
    (h : j α → j β) (g : j β → j γ) (x : f α) :
      g <$>ᵣ h <$>ᵣ x = (fun a => g (h a)) <$>ᵣ x :=
  (comp_mapᵣ _ _ _).symm

/-- The relative monad laws: `pureᵣ` is a left and right unit of `bindᵣ`, which is associative, and
the map is binding with `pureᵣ`. -/
class LawfulRelativeMonad (j : Type u → Type w) (m : Type u → Type v)
    [RelativeMonad j m] extends LawfulRelativeFunctor j m where

  pure_bindᵣ {α β : Type u} (x : j α) (f : j α → m β) :
    (pureᵣ x) >>=ᵣ f = f x

  bind_pure_compᵣ {α β : Type u} (f : j α → j β) (x : m α) :
    x >>=ᵣ (fun y => pureᵣ (f y)) = f <$>ᵣ x

  bind_assocᵣ {α β γ : Type u} (x : m α) (f : j α → m β) (g : j β → m γ) :
    x >>=ᵣ f >>=ᵣ g = x >>=ᵣ fun x ↦ f x >>=ᵣ g

export LawfulRelativeMonad (pure_bindᵣ bind_pure_compᵣ bind_assocᵣ)
attribute [simp] pure_bindᵣ bind_pure_compᵣ bind_assocᵣ

@[simp] theorem bind_pureᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (x : m α) :
    x >>=ᵣ pureᵣ (j := j) = x := by
  change x >>=ᵣ (fun a => pureᵣ (id a)) = x
  rw [bind_pure_compᵣ, id_mapᵣ]

theorem map_eq_pure_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j α → j β) (x : m α) : f <$>ᵣ x = x >>=ᵣ fun a => pureᵣ (f a) := by
  rw [← bind_pure_compᵣ]

theorem bind_congrᵣ [RelativeBind j m] {x : m α} {f g : j α → m β} (h : ∀ a, f a = g a) :
    x >>=ᵣ f = x >>=ᵣ g := by
  simp [funext h]

theorem bind_pure_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {x : m PUnit} :
    (x >>=ᵣ fun y : j PUnit => pureᵣ y) = x := by
  rw [bind_pure_compᵣ]; exact id_mapᵣ x

theorem map_congrᵣ [RelativeFunctor j m] {x : m α} {f g : j α → j β} (h : ∀ a, f a = g a) :
    (f <$>ᵣ x : m β) = g <$>ᵣ x := by
  simp [funext h]

@[simp] theorem map_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j β → j γ) (x : m α) (g : j α → m β) :
      f <$>ᵣ (x >>=ᵣ g) = x >>=ᵣ fun a : j α => f <$>ᵣ g a := by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [bind_pure_compᵣ]

@[simp] theorem bind_map_leftᵣ [RelativeMonad j m] [LawfulRelativeMonad j m]
    (f : j α → j β) (x : m α) (g : j β → m γ) :
      ((f <$>ᵣ x) >>=ᵣ fun b => g b) = (x >>=ᵣ fun a : j α => g (f a)) := by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [pure_bindᵣ]

theorem RelativeFunctor.map_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {a : m PUnit} :
    (fun y : j PUnit => y) <$>ᵣ a = a := by
  simp

/-- The `Functor` of a lawful relative map over `Id` is lawful. -/
theorem LawfulRelativeFunctor.lawfulFunctorOfId [RelativeFunctor Id f]
    [LawfulRelativeFunctor Id f] :
    letI := RelativeFunctor.functorOfId (f := f)
    LawfulFunctor f :=
  letI := RelativeFunctor.functorOfId (f := f)
  { map_const := @map_constᵣ Id f _ _
    id_map := @id_mapᵣ Id f _ _
    comp_map := @comp_mapᵣ Id f _ _ }

end Lawful

/-- An isomorphism of monads presented by a pair of mutually inverse lifts. -/
class MonadIso (m : Type u → Type v) (n : Type u → Type w) where
  /-- The lift from `m` to `n`. -/
  toLift : MonadLiftT m n
  /-- The inverse lift from `n` to `m`. -/
  invLift : MonadLiftT n m
  monadLift_left_inv {α : Type u} :
    Function.LeftInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))
  monadLift_right_inv {α : Type u} :
    Function.RightInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- A morphism from a relative monad over `r₁` to one over `r₂`, along a functor `r₁₂` and an
isomorphism of `r₂` with `r₁₂ ∘ r₁`, that commutes with `pureᵣ` and `bindᵣ`. -/
class RelativeMonadMorphism (r₁ : Type u → Type v₁) (m₁ : Type u → Type v₁)
    (r₂ : Type u → Type v₂) (m₂ : Type u → Type v₂)
    [RelativeMonad r₁ m₁] [RelativeMonad r₂ m₂] where
  /-- The functor between the targets of the roots. -/
  r₁₂ : Type v₁ → Type v₂
  /-- The functor structure of `r₁₂`. -/
  [instFunctor : Functor r₁₂]
  /-- The second root as the first followed by `r₁₂`. -/
  φ : MonadIso r₂ (r₁₂ ∘ r₁)
  /-- The components of the morphism. -/
  mmapᵣ {α : Type u} : r₁₂ (m₁ α) → m₂ α
  mmapᵣ_pureᵣ {α} :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (@pureᵣ r₁ m₁ _ α)) = pureᵣ ∘ φ.invLift.monadLift
  mmapᵣ_bindᵣ {α β : Type u} (f : r₁ α → m₁ β) :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (bindᵣ · f)) =
      (· >>=ᵣ mmapᵣ ∘ Functor.map (f := r₁₂) f ∘ φ.toLift.monadLift) ∘ mmapᵣ
