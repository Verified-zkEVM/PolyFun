/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Handler
public import PolyFun.PFunctor.Free.Universal

/-!
# Free handlers as polynomial Kleisli lenses

A free handler `Handler (FreeM Q) P` assigns to every `P`-operation a finite
`Q`-program whose leaves are labelled by the answer returned to the original
operation.  The polynomial extension equivalence for `FreeP Q` packages
exactly the same data as a lens `P ⇆ FreeP Q`.

This file makes that identification structural and shows that it preserves
the existing categorical operations:

* `Handler.id` is `FreeP.generator`;
* `Handler.comp` is composition with the existing universal
  `FreeP.foldLens` into `FreeP.substMonoid`.

Thus no second category of paper-specific objects is introduced.  The
`Display.Handler` fibers over ordinary handlers retain their `Type`-valued,
proof-relevant data; their identity and composition laws are expressed by
transport along the corresponding base-handler equalities rather than by
collapsing displayed witnesses into ordinary hom equality.
-/

@[expose] public section

universe u u' uA uA' uA'' uA''' uC uD uC' uD' uC'' uD'' uC''' uD'''

namespace PFunctor
namespace Handler

/-- Package a free handler as the corresponding lens into the free
polynomial.  The forward map is the erased program shape and the backward map
reads the label at the selected complete path. -/
def toFreeLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Handler (FreeM Q) P) : Lens P (FreeP Q) where
  toFunA operation := (FreeP.encode (f operation)).1
  toFunB operation := (FreeP.encode (f operation)).2

/-- Decode a lens into a free polynomial as a free handler. -/
def ofFreeLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (lens : Lens P (FreeP Q)) : Handler (FreeM Q) P :=
  fun operation =>
    FreeP.decode ⟨lens.toFunA operation, lens.toFunB operation⟩

/-- Free handlers are structurally equivalent to lenses into the free
polynomial, with independent position and direction universes for the source
and target interfaces. -/
def freeLensEquiv {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}} :
    Handler (FreeM Q) P ≃ Lens P (FreeP Q) where
  toFun := toFreeLens
  invFun := ofFreeLens
  left_inv f := by
    funext operation
    exact FreeP.decode_encode (f operation)
  right_inv lens := by
    apply Lens.ext_mapObj
    intro operation
    exact FreeP.encode_decode
      (⟨lens.toFunA operation, lens.toFunB operation⟩ :
        (FreeP Q).Obj (P.B operation))

@[simp]
theorem freeLensEquiv_apply
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Handler (FreeM Q) P) :
    freeLensEquiv f = toFreeLens f :=
  rfl

@[simp]
theorem freeLensEquiv_symm_apply
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (lens : Lens P (FreeP Q)) :
    freeLensEquiv.symm lens = ofFreeLens lens :=
  rfl

@[simp]
theorem toFreeLens_id (P : PFunctor.{uA, u}) :
    toFreeLens (Handler.id P) = FreeP.generator P := by
  rfl

private theorem decode_extension_bind
    {R : PFunctor.{u, u}} {E F : Type u}
    (x : SubstMonoid.Extension (FreeP.substMonoid R) E)
    (f : E → SubstMonoid.Extension (FreeP.substMonoid R) F) :
    FreeP.decode
        (SubstMonoid.Extension.bind (FreeP.substMonoid R) x f) =
      FreeM.bind (FreeP.decode x) (fun value => FreeP.decode (f value)) := by
  let source : (FreeP R ◃ FreeP R).Obj F :=
    ⟨⟨x.1, fun path => (f (x.2 path)).1⟩,
      fun direction => (f (x.2 direction.1)).2 direction.2⟩
  change FreeP.decode (Lens.mapObj (FreeP.mult (P := R)) source) = _
  rw [FreeP.decode_mult]
  have hnest : FreeP.nest source =
      FreeP.relabel (fun value => FreeP.decode (f value)) x := by
    rfl
  rw [hnest, FreeP.decode_relabel]
  let g := fun value => FreeP.decode (f value)
  calc
    FreeM.bind (FreeM.map g (FreeP.decode x)) _root_.id =
        FreeM.bind
          (FreeM.bind (FreeP.decode x) (FreeM.pure ∘ g)) _root_.id :=
      congrArg (fun tree => FreeM.bind tree _root_.id)
        (FreeM.bind_pure_comp g (FreeP.decode x)).symm
    _ = FreeM.bind (FreeP.decode x)
          (fun value => FreeM.bind (FreeM.pure (g value)) _root_.id) :=
      FreeM.bind_assoc _ _ _
    _ = FreeM.bind (FreeP.decode x) g := by
      rfl

private theorem liftM_encode
    {Q R : PFunctor.{u, u}}
    (second : Handler (FreeM R) Q) {E : Type u}
    (program : FreeM Q E) :
    FreeM.liftM
        (m := SubstMonoid.Extension (FreeP.substMonoid R))
        (fun query =>
          (FreeP.encode (second query) :
            SubstMonoid.Extension (FreeP.substMonoid R) (Q.B query)))
        program =
      FreeP.encode (program.liftM second) := by
  induction program with
  | pure value => rfl
  | lift_bind query next ih =>
      apply (FreeP.objEquiv (P := R) (α := E)).injective
      let extHandler : (q : Q.A) →
          SubstMonoid.Extension (FreeP.substMonoid R) (Q.B q) :=
        fun q => FreeP.encode (second q)
      have hleft : FreeM.liftM extHandler ((FreeM.lift query).bind next) =
          SubstMonoid.Extension.bind (FreeP.substMonoid R)
            (FreeP.encode (second query)) (fun direction =>
              FreeM.liftM extHandler (next direction)) := by
        rfl
      have hright : FreeM.liftM second ((FreeM.lift query).bind next) =
          FreeM.bind (second query)
            (fun direction => FreeM.liftM second (next direction)) := by
        rfl
      change FreeP.decode (FreeM.liftM extHandler
          ((FreeM.lift query).bind next)) =
        FreeP.decode (FreeP.encode
          (FreeM.liftM second ((FreeM.lift query).bind next)))
      rw [hleft, hright]
      rw [decode_extension_bind, FreeP.decode_encode]
      rw [FreeP.decode_encode]
      apply congrArg (FreeM.bind (second query))
      funext direction
      rw [ih direction, FreeP.decode_encode]

private theorem foldObjAt_encode
    {Q R : PFunctor.{u, u}}
    (second : Handler (FreeM R) Q) {E : Type u}
    (program : FreeM Q E) :
    FreeP.foldObjAt (FreeP.substMonoid R) (toFreeLens second)
        (FreeP.encode program).1 (FreeP.encode program).2 =
      FreeP.encode (program.liftM second) := by
  unfold FreeP.foldObjAt
  rw [show FreeP.decodeAt (FreeP.encode program).1
      (FreeP.encode program).2 = program from FreeP.decode_encode _]
  exact liftM_encode second program

/-- Under `freeLensEquiv`, categorical free-handler composition is the
existing universal free-polynomial fold followed by ordinary lens
composition.  This theorem is stated in the homogeneous categorical fragment
required by `FreeP.substMonoid`; the structural equivalence itself above is
fully heterogeneous in position universes. -/
theorem toFreeLens_comp
    {P Q R : PFunctor.{u, u}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P) :
    toFreeLens (second.comp first) =
      FreeP.foldLens (FreeP.substMonoid R) (toFreeLens second) ∘ₗ
        toFreeLens first := by
  apply Lens.ext_mapObj
  intro operation
  change FreeP.encode ((first operation).liftM second) = _
  change FreeP.encode ((first operation).liftM second) =
    Lens.mapObj
      (FreeP.foldLens (FreeP.substMonoid R) (toFreeLens second))
      (FreeP.encode (first operation))
  calc
    _ = FreeP.foldObjAt (FreeP.substMonoid R) (toFreeLens second)
        (FreeP.encode (first operation)).1
        (FreeP.encode (first operation)).2 :=
      (foldObjAt_encode second (first operation)).symm
    _ = _ := FreeP.foldObjAt_eq _ _ _ _

end Handler
end PFunctor
