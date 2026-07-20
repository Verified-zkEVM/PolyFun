/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Chart
public import PolyFun.PFunctor.Display.Handler

/-!
# Fiberwise lenses between polynomial displays

A `Display.Lens S T base` is a lift of an ordinary polynomial lens `base` to
the displayed position and direction fibers.  Displayed positions map
forward, while displayed directions map backward over the corresponding base
direction map.  This is the one-step structural fragment of
`Display.Handler`; `Display.Lens.toHandler` embeds it as a one-operation
displayed free handler.
-/

@[expose] public section

universe uA₁ uB₁ uC₁ uD₁ uA₂ uB₂ uC₂ uD₂
  uA₃ uB₃ uC₃ uD₃ uA₄ uB₄ uC₄ uD₄

namespace PFunctor
namespace Display

/-- A fiberwise lift of an ordinary polynomial lens between two displays. -/
structure Lens
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (S : Display.{uA₁, uB₁, uC₁, uD₁} P)
    (T : Display.{uA₂, uB₂, uC₂, uD₂} Q)
    (base : PFunctor.Lens P Q) where
  /-- Map displayed positions over the base position map. -/
  toPosition : (a : P.A) → S.position a → T.position (base.toFunA a)
  /-- Pull displayed directions back over the base direction map. -/
  toDirection : (a : P.A) → (c : S.position a) →
    (answer : Q.B (base.toFunA a)) →
    T.direction (base.toFunA a) (toPosition a c) answer →
      S.direction a c (base.toFunB a answer)

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}}
  {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
  {T : Display.{uA₂, uB₂, uC₂, uD₂} Q}
  {U : Display.{uA₃, uB₃, uC₃, uD₃} R}
  {f : PFunctor.Lens P Q} {g : PFunctor.Lens Q R}

/-- Extensionality for fiberwise lenses over a fixed base lens.  The direction
comparison transports only along the displayed-position equality, keeping the
public statement in ordinary equality rather than heterogeneous equality. -/
@[ext (iff := false)]
theorem ext {left right : Display.Lens S T f}
    (hPosition : ∀ a c, left.toPosition a c = right.toPosition a c)
    (hDirection : ∀ a c answer
      (direction : T.direction (f.toFunA a) (left.toPosition a c) answer),
      left.toDirection a c answer direction =
        right.toDirection a c answer (hPosition a c ▸ direction)) :
    left = right := by
  cases left with
  | mk leftPosition leftDirection =>
      cases right with
      | mk rightPosition rightDirection =>
          have positionEq : leftPosition = rightPosition := by
            funext a c
            exact hPosition a c
          subst rightPosition
          have directionEq : leftDirection = rightDirection := by
            funext a c answer direction
            exact hDirection a c answer direction
          subst rightDirection
          rfl

/-- Identity fiberwise lens. -/
def id (S : Display.{uA₁, uB₁, uC₁, uD₁} P) :
    Display.Lens S S (PFunctor.Lens.id P) where
  toPosition _ c := c
  toDirection _ _ _ d := d

@[simp] theorem id_toPosition (a : P.A) (c : S.position a) :
    (id S).toPosition a c = c :=
  rfl

@[simp] theorem id_toDirection (a : P.A) (c : S.position a)
    (answer : P.B a) (direction : S.direction a c answer) :
    (id S).toDirection a c answer direction = direction :=
  rfl

/-- Composition of fiberwise lenses, in the same categorical order as base
lens composition. -/
def comp (second : Display.Lens T U g) (first : Display.Lens S T f) :
    Display.Lens S U (g ∘ₗ f) where
  toPosition a c := second.toPosition (f.toFunA a) (first.toPosition a c)
  toDirection a c answer d :=
    first.toDirection a c (g.toFunB (f.toFunA a) answer)
      (second.toDirection (f.toFunA a) (first.toPosition a c) answer d)

/-- Forget the fiberwise/base split and view a displayed lens as the induced
ordinary lens between total polynomials. -/
def toTotal (displayed : Display.Lens S T f) :
    PFunctor.Lens S.total T.total where
  toFunA position :=
    ⟨f.toFunA position.1, displayed.toPosition position.1 position.2⟩
  toFunB position direction :=
    ⟨f.toFunB position.1 direction.1,
      displayed.toDirection position.1 position.2 direction.1 direction.2⟩

@[simp] theorem toTotal_toFunA (displayed : Display.Lens S T f)
    (a : P.A) (c : S.position a) :
    displayed.toTotal.toFunA ⟨a, c⟩ =
      ⟨f.toFunA a, displayed.toPosition a c⟩ :=
  rfl

@[simp] theorem toTotal_toFunB (displayed : Display.Lens S T f)
    (a : P.A) (c : S.position a) (answer : Q.B (f.toFunA a))
    (direction : T.direction (f.toFunA a)
      (displayed.toPosition a c) answer) :
    displayed.toTotal.toFunB ⟨a, c⟩ ⟨answer, direction⟩ =
      ⟨f.toFunB a answer,
        displayed.toDirection a c answer direction⟩ :=
  rfl

@[simp] theorem comp_toPosition (second : Display.Lens T U g)
    (first : Display.Lens S T f) (a : P.A) (c : S.position a) :
    (comp second first).toPosition a c =
      second.toPosition (f.toFunA a) (first.toPosition a c) :=
  rfl

@[simp] theorem comp_toDirection (second : Display.Lens T U g)
    (first : Display.Lens S T f) (a : P.A) (c : S.position a)
    (answer : R.B (g.toFunA (f.toFunA a)))
    (direction : U.direction (g.toFunA (f.toFunA a))
      (second.toPosition (f.toFunA a) (first.toPosition a c)) answer) :
    (comp second first).toDirection a c answer direction =
      first.toDirection a c (g.toFunB (f.toFunA a) answer)
        (second.toDirection (f.toFunA a) (first.toPosition a c)
          answer direction) :=
  rfl

@[simp] theorem id_comp (first : Display.Lens S T f) :
    comp (id T) first = first :=
  rfl

@[simp] theorem comp_id (second : Display.Lens S T f) :
    comp second (id S) = second :=
  rfl

theorem comp_assoc
    {V : PFunctor.{uA₄, uB₄}}
    {W : Display.{uA₄, uB₄, uC₄, uD₄} V}
    {h : PFunctor.Lens R V}
    (third : Display.Lens U W h)
    (second : Display.Lens T U g) (first : Display.Lens S T f) :
    comp (comp third second) first = comp third (comp second first) :=
  rfl

/-- Transport a fiberwise lens along equality of its base lens. -/
def transport {f g : PFunctor.Lens P Q} (h : f = g)
    (displayed : Display.Lens S T f) : Display.Lens S T g := by
  subst g
  exact displayed

@[simp] theorem transport_rfl (displayed : Display.Lens S T f) :
    transport rfl displayed = displayed :=
  rfl

theorem transport_proof_irrel {g : PFunctor.Lens P Q} (h h' : f = g)
    (displayed : Display.Lens S T f) :
    transport h displayed = transport h' displayed := by
  cases h
  rfl

@[simp] theorem transport_toPosition {g : PFunctor.Lens P Q} (h : f = g)
    (displayed : Display.Lens S T f) (a : P.A) (c : S.position a) :
    (transport h displayed).toPosition a c =
      (congrFun (congrArg PFunctor.Lens.toFunA h) a) ▸
        displayed.toPosition a c := by
  subst g
  rfl

theorem transport_trans
    {g h : PFunctor.Lens P Q} (first : f = g) (second : g = h)
    (displayed : Display.Lens S T f) :
    transport second (transport first displayed) =
      transport (first.trans second) displayed := by
  subst g
  rfl

/-- Base-lens transport does not change the induced map of total
polynomials.  This is the transport-free observational boundary for
fiberwise-lens coherence. -/
@[simp] theorem toTotal_transport {g : PFunctor.Lens P Q} (h : f = g)
    (displayed : Display.Lens S T f) :
    (transport h displayed).toTotal = displayed.toTotal := by
  subst g
  rfl

/-- Equality of fiberwise lenses as their induced maps of total
polynomials.  Unlike equality inside a fixed base-lens fiber, `TotalEq`
compares lenses over possibly different base maps without exposing
dependent casts or heterogeneous equality. -/
def TotalEq {g : PFunctor.Lens P Q}
    (left : Display.Lens S T f) (right : Display.Lens S T g) : Prop :=
  left.toTotal = right.toTotal

/-- The total-polynomial action faithfully records a fiberwise lens over a
fixed base lens. -/
theorem toTotal_injective :
    Function.Injective
      (toTotal : Display.Lens S T f → PFunctor.Lens S.total T.total) := by
  intro left right h
  cases left with
  | mk leftPosition leftDirection =>
      cases right with
      | mk rightPosition rightDirection =>
          simp only [toTotal] at h
          simp only [Display.Lens.mk.injEq]
          rw [PFunctor.Lens.mk.injEq] at h
          have hPosition : leftPosition = rightPosition := by
            funext a c
            have hA := congrFun h.1 ⟨a, c⟩
            exact eq_of_heq (Sigma.mk.inj_iff.mp hA).2
          subst rightPosition
          refine ⟨rfl, ?_⟩
          have hDirection := eq_of_heq h.2
          have hDirection' : leftDirection = rightDirection := by
            funext a c answer direction
            have hB := congrFun (congrFun hDirection ⟨a, c⟩)
              ⟨answer, direction⟩
            exact eq_of_heq (Sigma.mk.inj_iff.mp hB).2
          cases hDirection'
          rfl

/-- A total-polynomial equality plus equality of the base lenses recovers
ordinary equality in the target fiber. -/
theorem transport_eq_of_totalEq {g : PFunctor.Lens P Q} (baseEq : f = g)
    (left : Display.Lens S T f) (right : Display.Lens S T g)
    (h : TotalEq left right) : transport baseEq left = right := by
  apply toTotal_injective
  rw [toTotal_transport]
  exact h

@[refl] theorem TotalEq.refl (displayed : Display.Lens S T f) :
    TotalEq displayed displayed :=
  rfl

@[symm] theorem TotalEq.symm {g : PFunctor.Lens P Q}
    {left : Display.Lens S T f} {right : Display.Lens S T g}
    (h : TotalEq left right) : TotalEq right left :=
  Eq.symm h

@[trans] theorem TotalEq.trans {g h : PFunctor.Lens P Q}
    {left : Display.Lens S T f} {middle : Display.Lens S T g}
    {right : Display.Lens S T h}
    (first : TotalEq left middle) (second : TotalEq middle right) :
    TotalEq left right :=
  Eq.trans first second

@[simp] theorem TotalEq.transport_left {g : PFunctor.Lens P Q}
    (h : f = g) (left : Display.Lens S T f)
    (right : Display.Lens S T g) :
    TotalEq (transport h left) right ↔ TotalEq left right := by
  simp [TotalEq]

/-- Embed a fiberwise lens as a displayed one-operation free handler. -/
def toHandler (displayed : Display.Lens S T f) :
    Display.Handler S T (PFunctor.Handler.ofLens f) :=
  fun a c =>
    ⟨displayed.toPosition a c, fun answer direction =>
      T.leaf (S.direction a c) (f.toFunB a answer)
        (displayed.toDirection a c answer direction)⟩

@[simp] theorem toHandler_position (displayed : Display.Lens S T f)
    (a : P.A) (c : S.position a) :
    (displayed.toHandler a c).1 = displayed.toPosition a c :=
  rfl

@[simp] theorem toHandler_direction (displayed : Display.Lens S T f)
    (a : P.A) (c : S.position a) (answer : Q.B (f.toFunA a))
    (direction : T.direction (f.toFunA a)
      (displayed.toPosition a c) answer) :
    ((displayed.toHandler a c).2 answer direction).down =
      displayed.toDirection a c answer direction :=
  rfl

@[simp] theorem toHandler_id
    (S : Display.{uA₁, uB₁, uC₁, uD₁} P) :
    (id S).toHandler = Display.Handler.id S :=
  rfl

/-- Conversion to a displayed handler commutes with transport of the base
lens. -/
theorem toHandler_transport {g : PFunctor.Lens P Q} (h : f = g)
    (displayed : Display.Lens S T f) :
    Display.Handler.transport (congrArg PFunctor.Handler.ofLens h)
        displayed.toHandler =
      (transport h displayed).toHandler := by
  cases h
  rfl

/-- Converting a composite displayed lens to a handler agrees pointwise with
displayed Kleisli composition, after transport along `Handler.ofLens_comp`. -/
theorem toHandler_comp_apply
    {P₀ : PFunctor.{uA₁, uB₁}} {Q₀ : PFunctor.{uA₂, uB₁}}
    {R₀ : PFunctor.{uA₃, uB₃}}
    {S₀ : Display.{uA₁, uB₁, uC₁, uD₁} P₀}
    {T₀ : Display.{uA₂, uB₁, uC₂, uD₂} Q₀}
    {U₀ : Display.{uA₃, uB₃, uC₃, uD₃} R₀}
    {f₀ : PFunctor.Lens P₀ Q₀} {g₀ : PFunctor.Lens Q₀ R₀}
    (second : Display.Lens T₀ U₀ g₀) (first : Display.Lens S₀ T₀ f₀)
    (a : P₀.A) (c : S₀.position a) :
    U₀.transport (S₀.direction a c)
        (congrFun (PFunctor.Handler.ofLens_comp g₀ f₀) a)
        ((comp second first).toHandler a c) =
      (second.toHandler.comp first.toHandler) a c := by
  rw [U₀.transport_proof_irrel (S₀.direction a c)
    (congrFun (PFunctor.Handler.ofLens_comp g₀ f₀) a) rfl]
  rfl

/-- Conversion of a composite fiberwise lens is displayed-handler
composition, after transport along the corresponding base-handler law. -/
theorem toHandler_comp
    {P₀ : PFunctor.{uA₁, uB₁}} {Q₀ : PFunctor.{uA₂, uB₁}}
    {R₀ : PFunctor.{uA₃, uB₃}}
    {S₀ : Display.{uA₁, uB₁, uC₁, uD₁} P₀}
    {T₀ : Display.{uA₂, uB₁, uC₂, uD₂} Q₀}
    {U₀ : Display.{uA₃, uB₃, uC₃, uD₃} R₀}
    {f₀ : PFunctor.Lens P₀ Q₀} {g₀ : PFunctor.Lens Q₀ R₀}
    (second : Display.Lens T₀ U₀ g₀) (first : Display.Lens S₀ T₀ f₀) :
    Display.Handler.transport (PFunctor.Handler.ofLens_comp g₀ f₀)
        ((comp second first).toHandler) =
      second.toHandler.comp first.toHandler := by
  funext a c
  rw [Display.Handler.transport_apply]
  exact toHandler_comp_apply second first a c

/-- The inverse orientation of `toHandler_comp`, convenient when a generic
handler-composition theorem has already produced the Kleisli composite. -/
theorem toHandler_comp_symm
    {P₀ : PFunctor.{uA₁, uB₁}} {Q₀ : PFunctor.{uA₂, uB₁}}
    {R₀ : PFunctor.{uA₃, uB₃}}
    {S₀ : Display.{uA₁, uB₁, uC₁, uD₁} P₀}
    {T₀ : Display.{uA₂, uB₁, uC₂, uD₂} Q₀}
    {U₀ : Display.{uA₃, uB₃, uC₃, uD₃} R₀}
    {f₀ : PFunctor.Lens P₀ Q₀} {g₀ : PFunctor.Lens Q₀ R₀}
    (second : Display.Lens T₀ U₀ g₀) (first : Display.Lens S₀ T₀ f₀) :
    Display.Handler.transport (PFunctor.Handler.ofLens_comp g₀ f₀).symm
        (second.toHandler.comp first.toHandler) =
      (comp second first).toHandler := by
  rw [← toHandler_comp second first, Display.Handler.transport_trans]
  rw [Display.Handler.transport_proof_irrel
    ((PFunctor.Handler.ofLens_comp g₀ f₀).trans
      (PFunctor.Handler.ofLens_comp g₀ f₀).symm) rfl]
  rfl

end Lens
end Display
end PFunctor
