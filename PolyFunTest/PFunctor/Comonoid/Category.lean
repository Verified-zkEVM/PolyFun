/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid.Category

/-!
# Regression tests for the category encoded by a polynomial comonoid

The generic canaries keep position and direction universes independent. The
state-comonoid examples make identities, targets, path-order composition, and
the backward arrow action of a retrofunctor computationally observable.
-/

@[expose] public section

universe uA uB

namespace PFunctor
namespace ComonoidCategoryTest

/-! ## Independent-universe API canaries -/

example (C : Comonoid.{uA, uB}) (c : C.carrier.A) : C.carrier.B c :=
  Comonoid.identity C c

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (d : C.carrier.B c) : C.carrier.A :=
  Comonoid.target C c d

example (C : Comonoid.{uA, uB}) (c : C.carrier.A) :
    C.comult.toFunA c = ⟨c, Comonoid.target C c⟩ :=
  Comonoid.comultPosition_eq C c

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (d : C.carrier.B c)
    (e : C.carrier.B (Comonoid.target C c d)) : C.carrier.B c :=
  Comonoid.compose C c d e

example (C : Comonoid.{uA, uB}) (c : C.carrier.A) :
    Comonoid.target C c (Comonoid.identity C c) = c :=
  Comonoid.target_identity C c

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (d : C.carrier.B c) :
    Comonoid.compose C c d
        (Comonoid.identity C (Comonoid.target C c d)) = d :=
  Comonoid.compose_identity_right C c d

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (e : C.carrier.B
      (Comonoid.target C c (Comonoid.identity C c))) :
    Comonoid.compose C c (Comonoid.identity C c) e =
      cast (congrArg C.carrier.B (Comonoid.target_identity C c)) e :=
  Comonoid.compose_identity_left C c e

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (e : C.carrier.B c) :
    Comonoid.compose C c (Comonoid.identity C c)
        (cast (congrArg C.carrier.B
          (Comonoid.target_identity C c).symm) e) = e :=
  Comonoid.identity_compose C c e

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (d : C.carrier.B c)
    (e : C.carrier.B (Comonoid.target C c d)) :
    Comonoid.target C c (Comonoid.compose C c d e) =
      Comonoid.target C (Comonoid.target C c d) e :=
  Comonoid.target_compose C c d e

example (C : Comonoid.{uA, uB}) (c : C.carrier.A)
    (d : C.carrier.B c)
    (e : C.carrier.B (Comonoid.target C c d))
    (f : C.carrier.B
      (Comonoid.target C (Comonoid.target C c d) e)) :
    Comonoid.compose C c (Comonoid.compose C c d e)
        (cast (congrArg C.carrier.B
          (Comonoid.target_compose C c d e).symm) f) =
      Comonoid.compose C c d
        (Comonoid.compose C (Comonoid.target C c d) e f) :=
  Comonoid.compose_assoc C c d e f

example {C D : Comonoid.{uA, uB}} (F : Comonoid.Hom C D)
    (c : C.carrier.A) :
    F.toLens.toFunB c
        (Comonoid.identity D (F.toLens.toFunA c)) =
      Comonoid.identity C c :=
  F.map_identity c

example {C D : Comonoid.{uA, uB}} (F : Comonoid.Hom C D)
    (c : C.carrier.A) (d : D.carrier.B (F.toLens.toFunA c)) :
    F.toLens.toFunA
        (Comonoid.target C c (F.toLens.toFunB c d)) =
      Comonoid.target D (F.toLens.toFunA c) d :=
  F.map_target c d

example {C D : Comonoid.{uA, uB}} (F : Comonoid.Hom C D)
    (c : C.carrier.A) (d : D.carrier.B (F.toLens.toFunA c))
    (e : D.carrier.B (Comonoid.target D (F.toLens.toFunA c) d)) :
    F.toLens.toFunB c
        (Comonoid.compose D (F.toLens.toFunA c) d e) =
      Comonoid.compose C c (F.toLens.toFunB c d)
        (F.toLens.toFunB
          (Comonoid.target C c (F.toLens.toFunB c d))
          (cast (congrArg D.carrier.B (F.map_target c d).symm) e)) :=
  F.map_compose c d e

/-! ## Reconstruction from the outgoing-category laws -/

/-- The converse constructor keeps position and direction universes
independent and requires exactly the three laws exposed by a retrofunctor. -/
example {C D : Comonoid.{uA, uB}}
    (F : Lens C.carrier D.carrier)
    (mapIdentity : ∀ c : C.carrier.A,
      F.toFunB c (Comonoid.identity D (F.toFunA c)) =
        Comonoid.identity C c)
    (mapTarget : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c)),
      F.toFunA (Comonoid.target C c (F.toFunB c d)) =
        Comonoid.target D (F.toFunA c) d)
    (mapCompose : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c))
      (e : D.carrier.B (Comonoid.target D (F.toFunA c) d)),
      F.toFunB c (Comonoid.compose D (F.toFunA c) d e) =
        Comonoid.compose C c (F.toFunB c d)
          (F.toFunB (Comonoid.target C c (F.toFunB c d))
            (cast (congrArg D.carrier.B (mapTarget c d).symm) e))) :
    Comonoid.Hom C D :=
  Comonoid.Hom.ofCategoryLaws F mapIdentity mapTarget mapCompose

/-- Reconstructing an existing homomorphism from its derived category laws
preserves its exact underlying lens. -/
example {C D : Comonoid.{uA, uB}} (F : Comonoid.Hom C D) :
    Comonoid.Hom.ofCategoryLaws F.toLens
        (fun c => F.map_identity c)
        (fun c d => F.map_target c d)
        (fun c d e => F.map_compose c d e) = F :=
  F.ofCategoryLaws_map

/-! ## Observable state-category behavior -/

/-- Three genuinely distinct objects make the source, intermediate target, and
final target of a two-arrow path independently observable. -/
inductive ThreeState where
  | source
  | middle
  | final
  deriving DecidableEq, Repr

/-- A one-object, non-thin category with Boolean lists as arrows. This
test-local comonoid makes composition order observable independently of arrow
targets: the composite of `first` and `second` is `first ++ second`. -/
def listMonoidComonoid : Comonoid where
  carrier := purePower (List Bool)
  counit := (fun _ => PUnit.unit) ⇆ (fun _ _ => [])
  comult :=
    (fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩) ⇆
      (fun _ directions =>
        (show List Bool from directions.1) ++
          (show List Bool from directions.2))
  counit_left := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    exact List.nil_append direction
  counit_right := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    exact List.append_nil direction
  coassoc := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    change
      ((show List Bool from direction.1) ++
        (show List Bool from direction.2.1)) ++
          (show List Bool from direction.2.2) =
        (show List Bool from direction.1) ++
          ((show List Bool from direction.2.1) ++
            (show List Bool from direction.2.2))
    exact List.append_assoc direction.1 direction.2.1 direction.2.2

/-- In the contractible state category, the identity outgoing arrow names the
current state. -/
example : Comonoid.identity (stateComonoid Bool) false = false := rfl

/-- Every state is the target of its uniquely determined outgoing arrow. -/
example : Comonoid.target (stateComonoid Bool) false true = true := rfl

/-- State-category composition returns the final target, not either of the
other two objects on the path. -/
example :
    Comonoid.compose (stateComonoid ThreeState)
      .source .middle .final = .final := rfl

/-- Unlike the codiscrete state model, this category has parallel arrows.
Composition must preserve both arrows and their path order. -/
example :
    Comonoid.compose listMonoidComonoid PUnit.unit
      [false] [true] = [false, true] := rfl

/-- The first projection is a nontrivial retrofunctor between state
comonoids: it maps objects by `Prod.fst` and reconstructs a source-state arrow
by retaining the hidden second component. -/
def fstHom : Comonoid.Hom
    (stateComonoid (ThreeState × Bool)) (stateComonoid ThreeState) :=
  Comonoid.Hom.ofStateLens (Lens.State.fst ThreeState Bool)

/-- Rebuild the concrete first-projection retrofunctor only from its
identity/target/composition behavior. -/
def fstHomFromCategoryLaws : Comonoid.Hom
    (stateComonoid (ThreeState × Bool)) (stateComonoid ThreeState) :=
  Comonoid.Hom.ofCategoryLaws fstHom.toLens
    (fun c => fstHom.map_identity c)
    (fun c d => fstHom.map_target c d)
    (fun c d e => fstHom.map_compose c d e)

example : fstHomFromCategoryLaws = fstHom := by
  apply Comonoid.Hom.ext
  rfl

/-- Reconstruction retains the concrete backward state update, not merely the
forward object projection. -/
example :
    fstHomFromCategoryLaws.toLens.toFunB (.source, true) .final =
      (.final, true) :=
  rfl

/-- The reconstructed raw comultiplication proof re-derives the concrete
composition law, including the hidden state component. -/
example :
    fstHomFromCategoryLaws.toLens.toFunB (.source, true)
        (Comonoid.compose (stateComonoid ThreeState)
          (fstHomFromCategoryLaws.toLens.toFunA (.source, true))
          .middle .final) =
      Comonoid.compose (stateComonoid (ThreeState × Bool)) (.source, true)
        (fstHomFromCategoryLaws.toLens.toFunB (.source, true) .middle)
        (fstHomFromCategoryLaws.toLens.toFunB
          (Comonoid.target (stateComonoid (ThreeState × Bool))
            (.source, true)
            (fstHomFromCategoryLaws.toLens.toFunB
              (.source, true) .middle)) .final) :=
  fstHomFromCategoryLaws.map_compose (.source, true) .middle .final

example :
    fstHom.toLens.toFunB (.source, true)
        (Comonoid.identity (stateComonoid ThreeState) .source) =
      (.source, true) := rfl

example :
    fstHom.toLens.toFunA
        (Comonoid.target (stateComonoid (ThreeState × Bool)) (.source, true)
          (fstHom.toLens.toFunB (.source, true) .middle)) =
      .middle := rfl

example :
    fstHom.toLens.toFunB (.source, true)
        (Comonoid.compose (stateComonoid ThreeState)
          (fstHom.toLens.toFunA (.source, true)) .middle .final) =
      (.final, true) := rfl

end ComonoidCategoryTest
end PFunctor
