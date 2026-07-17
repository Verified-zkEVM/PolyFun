/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid

/-!
# The category encoded by a polynomial comonoid

The Ahman–Uustalu correspondence (Spivak–Niu, Theorem 7.28) identifies a
comonoid in `(Poly, ◃, y)` with a small category in outgoing-arrow form. For
`C : Comonoid`, the positions `C.carrier.A` are objects and a direction
`d : C.carrier.B c` is an arrow with source `c`. The counit selects the identity
at `c`; the comultiplication determines the target of `d` and composes `d` with
an arrow leaving that target.

This file exposes that dictionary and derives the five category laws directly
from the two counitality equations and coassociativity. It also projects the
laws of `Comonoid.Hom` into the identity/target/composition laws of a
retrofunctor (Spivak–Niu, Definition 7.55): objects move forward while outgoing
arrows move backward. Conversely, `Comonoid.Hom.ofCategoryLaws` reconstructs
the raw comonoid-homomorphism equations from exactly those three laws, keeping
dependent transport localized in this producer module.

The scope here is the extraction direction of the correspondence. The reverse
construction from an outgoing-arrow category to a polynomial comonoid, and a
packaged equivalence proving the full Ahman–Uustalu theorem, are not supplied by
this module.

No `Category` instance is installed on `C.carrier.A`. A carrier can support
several comonoid structures, and an instance on the bare position type could
not remember which structure supplies composition. The outgoing-arrow API is
also the form used directly by cofree-comonoid coiteration.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uR

namespace PFunctor
namespace Comonoid

private theorem lens_toFunB_apply_eq_of_eq
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {left right : Lens P Q} (h : left = right) (position : P.A)
    (direction : Q.B (right.toFunA position)) :
    left.toFunB position
        (cast (congrArg Q.B
          (congrArg (fun lens : Lens P Q => lens.toFunA position) h).symm)
          direction) =
      right.toFunB position direction := by
  subst right
  rfl

private theorem eqRec_function_apply {A : Type uA} (B : A → Type uB)
    {a b : A} (h : a = b) {R : Type uR} (f : B b → R) (x : B a) :
    (h ▸ f) x = f (cast (congrArg B h) x) := by
  subst b
  rfl

private theorem cast_comp_direction
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (position : P.A) {children children' : P.B position → Q.A}
    (h : children = children') (direction : P.B position)
    (next : Q.B (children direction)) :
    cast (congrArg (P ◃ Q).B
      (congrArg
        (fun current => (⟨position, current⟩ : (P ◃ Q).A)) h))
      (⟨direction, next⟩ : (P ◃ Q).B ⟨position, children⟩) =
    (⟨direction,
      cast (congrArg Q.B (congrFun h direction)) next⟩ :
      (P ◃ Q).B ⟨position, children'⟩) := by
  subst h
  rfl

variable (C : Comonoid.{uA, uB})

/-- The outer source object selected by comultiplication is the original
object. -/
theorem comultOuter_eq (c : C.carrier.A) :
    (C.comult.toFunA c).1 = c :=
  congrArg (fun lens => lens.toFunA c) C.counit_right

/-! ## Outgoing-arrow operations -/

/-- The identity outgoing arrow at an object, selected by the comonoid
counit. -/
def identity (c : C.carrier.A) : C.carrier.B c :=
  C.counit.toFunB c PUnit.unit

private theorem identity_transport {a b : C.carrier.A} (h : a = b) :
    identity C a = cast (congrArg C.carrier.B h.symm) (identity C b) := by
  subst b
  rfl

/-- The target (categorical codomain) of an outgoing arrow. The source is
already recorded by the direction fiber `C.carrier.B c`. -/
def target (c : C.carrier.A) (d : C.carrier.B c) : C.carrier.A :=
  (C.comult.toFunA c).2
    (cast (congrArg C.carrier.B (comultOuter_eq C c).symm) d)

/-- The original comultiplication-based definition of a state system is
equivalent to bijectivity of the canonical outgoing-arrow target map. -/
theorem isStateSystem_iff_target_bijective :
    C.IsStateSystem ↔
      ∀ c : C.carrier.A, Function.Bijective (target C c) := by
  constructor
  · intro h c
    let e := _root_.Equiv.cast
      (congrArg C.carrier.B (comultOuter_eq C c).symm)
    change Function.Bijective ((C.comult.toFunA c).2 ∘ e)
    exact Function.Bijective.comp (h c) e.bijective
  · intro h c
    let e := _root_.Equiv.cast
      (congrArg C.carrier.B (comultOuter_eq C c).symm)
    have hTarget := h c
    change Function.Bijective ((C.comult.toFunA c).2 ∘ e) at hTarget
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using
      Function.Bijective.comp hTarget e.symm.bijective

/-- The position action of comultiplication is canonically the source object
paired with the target of every outgoing arrow. -/
theorem comultPosition_eq (c : C.carrier.A) :
    C.comult.toFunA c = ⟨c, target C c⟩ := by
  apply Sigma.ext (comultOuter_eq C c)
  apply Function.hfunext (congrArg C.carrier.B (comultOuter_eq C c))
  intro rawDirection canonicalDirection hDirection
  apply heq_of_eq
  unfold target
  apply congrArg ((C.comult.toFunA c).2)
  exact ((cast_eq_iff_heq).2 hDirection.symm).symm

/-- Compose an arrow `d` leaving `c` with an arrow `e` leaving the target of
`d`, in path order. -/
def compose (c : C.carrier.A) (d : C.carrier.B c)
    (e : C.carrier.B (target C c d)) : C.carrier.B c :=
  C.comult.toFunB c
    (cast (congrArg (C.carrier ◃ C.carrier).B
      (comultPosition_eq C c).symm) ⟨d, e⟩)

private def normalizedComult : Lens C.carrier (C.carrier ◃ C.carrier) where
  toFunA c := ⟨c, target C c⟩
  toFunB c direction := compose C c direction.1 direction.2

private theorem normalizedComult_eq : normalizedComult C = C.comult := by
  refine Lens.ext _ _ (fun c => (comultPosition_eq C c).symm) ?_
  intro c
  funext direction
  unfold normalizedComult compose
  rw [eqRec_function_apply (h := (comultPosition_eq C c).symm)]
  rcases direction with ⟨d, e⟩
  rfl

private theorem normalized_counit_right :
    Lens.Equiv.compX.toLens ∘ₗ
        (Lens.id C.carrier ◃ₗ C.counit) ∘ₗ normalizedComult C =
      Lens.id C.carrier := by
  simpa only [normalizedComult_eq] using C.counit_right

private theorem normalized_counit_left :
    Lens.Equiv.XComp.toLens ∘ₗ
        (C.counit ◃ₗ Lens.id C.carrier) ∘ₗ normalizedComult C =
      Lens.id C.carrier := by
  simpa only [normalizedComult_eq] using C.counit_left

private theorem normalized_coassoc :
    Lens.Equiv.compAssoc.toLens ∘ₗ
          (normalizedComult C ◃ₗ Lens.id C.carrier) ∘ₗ
        normalizedComult C =
      (Lens.id C.carrier ◃ₗ normalizedComult C) ∘ₗ
        normalizedComult C := by
  simpa only [normalizedComult_eq] using C.coassoc

/-! ## Category laws -/

/-- The target of the identity arrow at `c` is `c`. -/
@[simp]
theorem target_identity (c : C.carrier.A) :
    target C c (identity C c) = c := by
  have h := congrArg (fun lens : Lens C.carrier C.carrier => lens.toFunA c)
    C.counit_left
  change (C.comult.toFunA c).2
      (C.counit.toFunB (C.comult.toFunA c).1 PUnit.unit) = c at h
  change (C.comult.toFunA c).2
      (cast (congrArg C.carrier.B (comultOuter_eq C c).symm)
        (identity C c)) = c
  rw [← identity_transport C (comultOuter_eq C c)]
  exact h

/-- Composing an outgoing arrow with the identity at its target leaves the
arrow unchanged. -/
@[simp]
theorem compose_identity_right (c : C.carrier.A) (d : C.carrier.B c) :
    compose C c d (identity C (target C c d)) = d := by
  change
    (Lens.Equiv.compX.toLens ∘ₗ
        (Lens.id C.carrier ◃ₗ C.counit) ∘ₗ
      normalizedComult C).toFunB c d = d
  exact lens_toFunB_apply_eq_of_eq (normalized_counit_right C) c d

/-- Composing the identity at `c` with an arrow leaving its propositionally
equal target returns that arrow in the canonical fiber over `c`. -/
theorem compose_identity_left (c : C.carrier.A)
    (e : C.carrier.B (target C c (identity C c))) :
    compose C c (identity C c) e =
      cast (congrArg C.carrier.B (target_identity C c)) e := by
  have h := congrArg
    (fun lens : Lens C.carrier C.carrier =>
      Lens.mapObj lens
        (⟨c, id⟩ : C.carrier.Obj (C.carrier.B c)))
    (normalized_counit_left C)
  change
    (⟨target C c (identity C c),
      fun direction => compose C c (identity C c) direction⟩ :
      C.carrier.Obj (C.carrier.B c)) = ⟨c, id⟩ at h
  have hFunctions :
      (fun direction => compose C c (identity C c) direction) ≍
        (fun direction : C.carrier.B c => direction) :=
    (Sigma.ext_iff.mp h).2
  have hInput : e ≍
      cast (congrArg C.carrier.B (target_identity C c)) e :=
    (cast_heq (congrArg C.carrier.B (target_identity C c)) e).symm
  exact @congr_heq
    (C.carrier.B (target C c (identity C c))) (C.carrier.B c)
    (C.carrier.B c)
    (fun direction => compose C c (identity C c) direction)
    (fun direction => direction) e
    (cast (congrArg C.carrier.B (target_identity C c)) e)
    hFunctions hInput

/-- Canonical-fiber form of left identity. -/
@[simp]
theorem identity_compose (c : C.carrier.A) (e : C.carrier.B c) :
    compose C c (identity C c)
        (cast (congrArg C.carrier.B (target_identity C c).symm) e) = e := by
  simpa using compose_identity_left C c
    (cast (congrArg C.carrier.B (target_identity C c).symm) e)

/-- The target of a composite is the target of its second arrow. -/
@[simp]
theorem target_compose (c : C.carrier.A) (d : C.carrier.B c)
    (e : C.carrier.B (target C c d)) :
    target C c (compose C c d e) = target C (target C c d) e := by
  have h := congrArg (fun lens => lens.toFunA c)
    (normalized_coassoc C)
  change
    (⟨c, fun d => ⟨target C c d,
      fun e => target C c (compose C c d e)⟩⟩ :
      (C.carrier ◃ (C.carrier ◃ C.carrier)).A) =
    ⟨c, fun d => ⟨target C c d,
      fun e => target C (target C c d) e⟩⟩ at h
  have hOuter :
      (fun d : C.carrier.B c =>
        (⟨target C c d,
          fun e => target C c (compose C c d e)⟩ :
          (C.carrier ◃ C.carrier).A)) =
      (fun d : C.carrier.B c =>
        (⟨target C c d,
          fun e => target C (target C c d) e⟩ :
          (C.carrier ◃ C.carrier).A)) := by
    exact eq_of_heq (Sigma.ext_iff.mp h).2
  have hAtDirection := congrFun hOuter d
  have hInner :
      (fun e => target C c (compose C c d e)) =
      (fun e => target C (target C c d) e) :=
    eq_of_heq (Sigma.ext_iff.mp hAtDirection).2
  exact congrFun hInner e

/-- Composition of outgoing arrows is associative. The final arrow is
transported from the right-associated target fiber to the propositionally
equal left-associated target fiber. -/
theorem compose_assoc (c : C.carrier.A) (d : C.carrier.B c)
    (e : C.carrier.B (target C c d))
    (f : C.carrier.B (target C (target C c d) e)) :
    compose C c (compose C c d e)
        (cast (congrArg C.carrier.B (target_compose C c d e).symm) f) =
      compose C c d (compose C (target C c d) e f) := by
  let leftTargets (d : C.carrier.B c) :
      C.carrier.B (target C c d) → C.carrier.A :=
    fun e => target C c (compose C c d e)
  let rightTargets (d : C.carrier.B c) :
      C.carrier.B (target C c d) → C.carrier.A :=
    target C (target C c d)
  let targetEq (d : C.carrier.B c) :
      leftTargets d = rightTargets d :=
    funext fun e => target_compose C c d e
  let leftChildren (d : C.carrier.B c) :
      (C.carrier ◃ C.carrier).A :=
    ⟨target C c d, leftTargets d⟩
  let rightChildren (d : C.carrier.B c) :
      (C.carrier ◃ C.carrier).A :=
    ⟨target C c d, rightTargets d⟩
  let childrenEq : leftChildren = rightChildren := by
    funext direction
    exact Sigma.ext rfl (heq_of_eq (targetEq direction))
  let leftPosition :
      (C.carrier ◃ (C.carrier ◃ C.carrier)).A :=
    ⟨c, leftChildren⟩
  let rightPosition :
      (C.carrier ◃ (C.carrier ◃ C.carrier)).A :=
    ⟨c, rightChildren⟩
  let positionEq : leftPosition = rightPosition :=
    congrArg
      (fun current =>
        (⟨c, current⟩ :
          (C.carrier ◃ (C.carrier ◃ C.carrier)).A))
      childrenEq
  let leftDirection :
      (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        leftPosition :=
    ⟨d, ⟨e,
      cast (congrArg C.carrier.B
        (target_compose C c d e).symm) f⟩⟩
  let rightDirection :
      (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        rightPosition :=
    ⟨d, ⟨e, f⟩⟩
  have hTransport :
      cast (congrArg (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        positionEq) leftDirection = rightDirection := by
    let innerLeft : (C.carrier ◃ C.carrier).B (leftChildren d) :=
      ⟨e, cast (congrArg C.carrier.B
        (target_compose C c d e).symm) f⟩
    let innerRight : (C.carrier ◃ C.carrier).B (rightChildren d) :=
      ⟨e, f⟩
    change
      cast (congrArg (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        (congrArg
          (fun current =>
            (⟨c, current⟩ :
              (C.carrier ◃ (C.carrier ◃ C.carrier)).A))
          childrenEq))
        (⟨d, innerLeft⟩ :
          (C.carrier ◃ (C.carrier ◃ C.carrier)).B
            (⟨c, leftChildren⟩ :
              (C.carrier ◃ (C.carrier ◃ C.carrier)).A)) =
      (⟨d, innerRight⟩ :
        (C.carrier ◃ (C.carrier ◃ C.carrier)).B
          (⟨c, rightChildren⟩ :
            (C.carrier ◃ (C.carrier ◃ C.carrier)).A))
    have hAtDirection : congrFun childrenEq d =
        congrArg
          (fun current =>
            (⟨target C c d, current⟩ :
              (C.carrier ◃ C.carrier).A))
          (targetEq d) := Subsingleton.elim _ _
    have hAtTarget : congrFun (targetEq d) e =
        target_compose C c d e := Subsingleton.elim _ _
    have hInner :
        cast (congrArg (C.carrier ◃ C.carrier).B
          (congrFun childrenEq d)) innerLeft = innerRight := by
      rw [hAtDirection]
      calc
        _ =
            (⟨e, cast (congrArg C.carrier.B
              (congrFun (targetEq d) e)) innerLeft.2⟩ :
              (C.carrier ◃ C.carrier).B (rightChildren d)) :=
          cast_comp_direction
            (P := C.carrier) (Q := C.carrier)
            (target C c d) (targetEq d) e innerLeft.2
        _ = innerRight := by
          rw [hAtTarget]
          simp [innerLeft, innerRight]
    calc
      _ =
          (⟨d, cast (congrArg (C.carrier ◃ C.carrier).B
            (congrFun childrenEq d)) innerLeft⟩ :
            (C.carrier ◃ (C.carrier ◃ C.carrier)).B
              (⟨c, rightChildren⟩ :
                (C.carrier ◃ (C.carrier ◃ C.carrier)).A)) :=
        cast_comp_direction
          (P := C.carrier) (Q := C.carrier ◃ C.carrier)
          c childrenEq d innerLeft
      _ = ⟨d, innerRight⟩ := by
        exact congrArg
          (fun next =>
            (⟨d, next⟩ :
              (C.carrier ◃ (C.carrier ◃ C.carrier)).B
                (⟨c, rightChildren⟩ :
                  (C.carrier ◃ (C.carrier ◃ C.carrier)).A)))
          hInner
  have h := lens_toFunB_apply_eq_of_eq (normalized_coassoc C).symm c
    leftDirection
  have hPosition :
      congrArg
        (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        (congrArg
          (fun lens => lens.toFunA c)
          (normalized_coassoc C).symm).symm =
      congrArg
        (C.carrier ◃ (C.carrier ◃ C.carrier)).B positionEq :=
    Subsingleton.elim _ _
  have hTransportActual :
      cast (congrArg
        (C.carrier ◃ (C.carrier ◃ C.carrier)).B
        (congrArg (fun lens => lens.toFunA c)
          (normalized_coassoc C).symm).symm) leftDirection =
        rightDirection := by
    rw [hPosition]
    exact hTransport
  rw [hTransportActual] at h
  change compose C c d (compose C (target C c d) e f) =
    compose C c (compose C c d e)
      (cast (congrArg C.carrier.B
        (target_compose C c d e).symm) f) at h
  exact h.symm

/-! ## Retrofunctor laws -/

variable {C D : Comonoid.{uA, uB}}

/-- A retrofunctor pulls the identity at the image object back to the source
identity. -/
@[simp]
theorem Hom.map_identity (F : Hom C D) (c : C.carrier.A) :
    F.toLens.toFunB c (identity D (F.toLens.toFunA c)) = identity C c :=
  congrArg (fun lens => lens.toFunB c PUnit.unit) F.map_counit

private theorem Hom.map_normalizedComult (F : Hom C D) :
    normalizedComult D ∘ₗ F.toLens =
      (F.toLens ◃ₗ F.toLens) ∘ₗ normalizedComult C := by
  simpa only [normalizedComult_eq] using F.map_comult

/-- A retrofunctor preserves targets forward after pulling an outgoing arrow
backward. -/
theorem Hom.map_target (F : Hom C D) (c : C.carrier.A)
    (d : D.carrier.B (F.toLens.toFunA c)) :
    F.toLens.toFunA (target C c (F.toLens.toFunB c d)) =
      target D (F.toLens.toFunA c) d := by
  have h := congrArg (fun lens => lens.toFunA c)
    (F.map_normalizedComult)
  change
    (⟨F.toLens.toFunA c,
      target D (F.toLens.toFunA c)⟩ :
      (D.carrier ◃ D.carrier).A) =
    ⟨F.toLens.toFunA c, fun d =>
      F.toLens.toFunA
        (target C c (F.toLens.toFunB c d))⟩ at h
  have hTargets :
      target D (F.toLens.toFunA c) =
      (fun d => F.toLens.toFunA
        (target C c (F.toLens.toFunB c d))) :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  exact (congrFun hTargets d).symm

/-- A retrofunctor pulls a composite back to the composite of the pulled-back
arrows. The second arrow is transported across target preservation before it
is pulled back at the intermediate source object. -/
theorem Hom.map_compose (F : Hom C D) (c : C.carrier.A)
    (d : D.carrier.B (F.toLens.toFunA c))
    (e : D.carrier.B (target D (F.toLens.toFunA c) d)) :
    F.toLens.toFunB c (compose D (F.toLens.toFunA c) d e) =
      compose C c (F.toLens.toFunB c d)
        (F.toLens.toFunB (target C c (F.toLens.toFunB c d))
          (cast (congrArg D.carrier.B (F.map_target c d).symm) e)) := by
  let leftTargets :
      D.carrier.B (F.toLens.toFunA c) → D.carrier.A :=
    target D (F.toLens.toFunA c)
  let rightTargets :
      D.carrier.B (F.toLens.toFunA c) → D.carrier.A :=
    fun d => F.toLens.toFunA
      (target C c (F.toLens.toFunB c d))
  let targetsEq : leftTargets = rightTargets :=
    funext fun d => (F.map_target c d).symm
  let leftPosition : (D.carrier ◃ D.carrier).A :=
    ⟨F.toLens.toFunA c, leftTargets⟩
  let rightPosition : (D.carrier ◃ D.carrier).A :=
    ⟨F.toLens.toFunA c, rightTargets⟩
  let positionEq : leftPosition = rightPosition :=
    congrArg
      (fun current =>
        (⟨F.toLens.toFunA c, current⟩ :
          (D.carrier ◃ D.carrier).A)) targetsEq
  let leftDirection :
      (D.carrier ◃ D.carrier).B
        leftPosition :=
    ⟨d, e⟩
  let rightDirection :
      (D.carrier ◃ D.carrier).B
        rightPosition :=
    ⟨d, cast (congrArg D.carrier.B
      (F.map_target c d).symm) e⟩
  have hTransport :
      cast (congrArg (D.carrier ◃ D.carrier).B
        positionEq)
        leftDirection = rightDirection := by
    have hCast := cast_comp_direction
      (P := D.carrier) (Q := D.carrier)
      (F.toLens.toFunA c) targetsEq d e
    convert hCast using 1
  have h := lens_toFunB_apply_eq_of_eq
    (F.map_normalizedComult).symm c leftDirection
  have hPosition :
      congrArg (D.carrier ◃ D.carrier).B
        (congrArg (fun lens => lens.toFunA c)
          (F.map_normalizedComult).symm).symm =
      congrArg (D.carrier ◃ D.carrier).B
        positionEq :=
    Subsingleton.elim _ _
  have hTransportActual :
      cast (congrArg (D.carrier ◃ D.carrier).B
        (congrArg (fun lens => lens.toFunA c)
          (F.map_normalizedComult).symm).symm) leftDirection =
        rightDirection := by
    rw [hPosition]
    exact hTransport
  rw [hTransportActual] at h
  change compose C c (F.toLens.toFunB c d)
      (F.toLens.toFunB (target C c (F.toLens.toFunB c d))
        (cast (congrArg D.carrier.B (F.map_target c d).symm) e)) =
    F.toLens.toFunB c (compose D (F.toLens.toFunA c) d e) at h
  exact h.symm

/-! ## Constructing retrofunctors from category laws -/

private theorem normalizedComult_natural_of_categoryLaws
    (F : Lens C.carrier D.carrier)
    (mapTarget : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c)),
      F.toFunA (target C c (F.toFunB c d)) =
        target D (F.toFunA c) d)
    (mapCompose : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c))
      (e : D.carrier.B (target D (F.toFunA c) d)),
      F.toFunB c (compose D (F.toFunA c) d e) =
        compose C c (F.toFunB c d)
          (F.toFunB (target C c (F.toFunB c d))
            (cast (congrArg D.carrier.B (mapTarget c d).symm) e))) :
    normalizedComult D ∘ₗ F =
      (F ◃ₗ F) ∘ₗ normalizedComult C := by
  let hobj : ∀ c : C.carrier.A,
      Lens.mapObj (normalizedComult D ∘ₗ F)
          (⟨c, id⟩ : C.carrier.Obj (C.carrier.B c)) =
        Lens.mapObj ((F ◃ₗ F) ∘ₗ normalizedComult C)
          (⟨c, id⟩ : C.carrier.Obj (C.carrier.B c)) := fun c => by
    let leftTargets :
        D.carrier.B (F.toFunA c) → D.carrier.A :=
      target D (F.toFunA c)
    let rightTargets :
        D.carrier.B (F.toFunA c) → D.carrier.A :=
      fun d => F.toFunA (target C c (F.toFunB c d))
    let targetsEq : leftTargets = rightTargets :=
      funext fun d => (mapTarget c d).symm
    let leftPosition : (D.carrier ◃ D.carrier).A :=
      ⟨F.toFunA c, leftTargets⟩
    let rightPosition : (D.carrier ◃ D.carrier).A :=
      ⟨F.toFunA c, rightTargets⟩
    let positionEq : leftPosition = rightPosition :=
      congrArg
        (fun current =>
          (⟨F.toFunA c, current⟩ :
            (D.carrier ◃ D.carrier).A))
        targetsEq
    apply Sigma.ext positionEq
    apply Function.hfunext
      (congrArg (D.carrier ◃ D.carrier).B positionEq)
    intro leftDirection rightDirection hDirection
    have hcast :
        cast (congrArg (D.carrier ◃ D.carrier).B positionEq)
            leftDirection = rightDirection :=
      (cast_eq_iff_heq).2 hDirection
    rcases leftDirection with ⟨d, e⟩
    let canonical : (D.carrier ◃ D.carrier).B rightPosition :=
      ⟨d, cast (congrArg D.carrier.B (mapTarget c d).symm) e⟩
    have hcanonical :
        cast (congrArg (D.carrier ◃ D.carrier).B positionEq)
            (⟨d, e⟩ : (D.carrier ◃ D.carrier).B leftPosition) =
          canonical := by
      have hCast := cast_comp_direction
        (P := D.carrier) (Q := D.carrier)
        (F.toFunA c) targetsEq d e
      convert hCast using 1
    have hright : canonical = rightDirection :=
      hcanonical.symm.trans hcast
    subst rightDirection
    apply heq_of_eq
    rw [hcanonical]
    dsimp only [Lens.mapObj, Lens.comp, normalizedComult, Lens.compMap]
    change F.toFunB c (compose D (F.toFunA c) d e) =
      compose C c (F.toFunB c d)
        (F.toFunB (target C c (F.toFunB c d))
          (cast (congrArg D.carrier.B (mapTarget c d).symm) e))
    exact mapCompose c d e
  let hA : ∀ c,
      (normalizedComult D ∘ₗ F).toFunA c =
        ((F ◃ₗ F) ∘ₗ normalizedComult C).toFunA c :=
    fun c => congrArg Sigma.fst (hobj c)
  refine Lens.ext _ _ hA ?_
  intro c
  apply eq_of_heq
  have hraw :
      (normalizedComult D ∘ₗ F).toFunB c ≍
        ((F ◃ₗ F) ∘ₗ normalizedComult C).toFunB c :=
    (Sigma.ext_iff.mp (hobj c)).2
  have htransport :
      (hA c ▸ ((F ◃ₗ F) ∘ₗ normalizedComult C).toFunB c) ≍
        ((F ◃ₗ F) ∘ₗ normalizedComult C).toFunB c :=
    eqRec_heq_self _ _
  exact hraw.trans htransport.symm

/-- Construct a comonoid homomorphism from a carrier lens satisfying the three
outgoing-category laws of a retrofunctor. This is the converse of
`Hom.map_identity`, `Hom.map_target`, and `Hom.map_compose`: identities and
composites are pulled backward, while targets are preserved forward. -/
def Hom.ofCategoryLaws (F : Lens C.carrier D.carrier)
    (mapIdentity : ∀ c : C.carrier.A,
      F.toFunB c (identity D (F.toFunA c)) = identity C c)
    (mapTarget : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c)),
      F.toFunA (target C c (F.toFunB c d)) =
        target D (F.toFunA c) d)
    (mapCompose : ∀ (c : C.carrier.A)
      (d : D.carrier.B (F.toFunA c))
      (e : D.carrier.B (target D (F.toFunA c) d)),
      F.toFunB c (compose D (F.toFunA c) d e) =
        compose C c (F.toFunB c d)
          (F.toFunB (target C c (F.toFunB c d))
            (cast (congrArg D.carrier.B (mapTarget c d).symm) e))) :
    Hom C D where
  toLens := F
  map_counit := by
    refine Lens.ext _ _ (fun _ => rfl) ?_
    intro c
    funext direction
    cases direction
    exact mapIdentity c
  map_comult := by
    simpa only [normalizedComult_eq] using
      normalizedComult_natural_of_categoryLaws F mapTarget mapCompose

@[simp]
theorem Hom.ofCategoryLaws_toLens (F : Lens C.carrier D.carrier)
    (mapIdentity mapTarget mapCompose) :
    (Hom.ofCategoryLaws F mapIdentity mapTarget mapCompose).toLens = F :=
  rfl

/-- Reconstructing an existing retrofunctor from its three derived
outgoing-category laws returns the original homomorphism. -/
@[simp]
theorem Hom.ofCategoryLaws_map (F : Hom C D) :
    Hom.ofCategoryLaws F.toLens
        (fun c => F.map_identity c)
        (fun c d => F.map_target c d)
        (fun c d e => F.map_compose c d e) = F :=
  Hom.ext _ _ rfl

end Comonoid
end PFunctor
