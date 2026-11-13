/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Free.CodeRel
public import PolyFun.PFunctor.Free.Quotient

/-!
# Relations between free monads modulo equational theories

A signature relation `S : SigRel P Q` lifts to the free monads by `HFreeRel S R`. Given
equational theories `T₁` over `P` and `T₂` over `Q`, the induced relation `QFreeRel S T₁ T₂ R`
relates two classes of `QFreeM T₁ α` and `QFreeM T₂ β` when they have `HFreeRel S R`-related
representatives. The theories are compatible with `S` (`SigRel.Compat`) when the lift is a
bisimulation up to the congruences: a program related to `y` stays related to a program
congruent to `y` after a congruence step on its own side, and symmetrically. Under compatibility
the induced relation does not depend on the choice of representative on either side.

A relational lifting `RelLift m m'` of two monads relates computations `m α` and `m' β` along a
relation `α → β → Prop`, with a rule for `pure` and a rule for bind. Handlers that send related
positions to computations related along the direction relation interpret related programs to
related computations (`HFreeRel.liftM_rel`), and, when they validate `T₁` and `T₂`, related
classes to related computations (`QFreeRel.lift_rel`).

## Main definitions

* `PFunctor.RelLift` — a relational lifting of two monads
* `PFunctor.SigRel.Compat` — compatibility of two equational theories with a signature relation
* `PFunctor.QFreeRel` — the relation induced by a signature relation on the quotients

## Main results

* `PFunctor.HFreeRel.liftM_rel` — related handlers interpret related programs to related
  computations
* `PFunctor.QFreeRel.lift_rel` — related validating handlers interpret related classes to related
  computations
* `PFunctor.QFreeRel.mk_iff_left`, `PFunctor.QFreeRel.mk_iff_right` — under compatibility, the
  relation between two classes is the relation up to the congruence on one side
* `PFunctor.QFreeRel.eq_iff` — identity extension: along an identity signature relation and one
  theory, the relation induced by equality is equality
* `PFunctor.EqTheory.cong_iff_eq_of_isEmpty`, `PFunctor.SigRel.compat_of_isEmpty` — a theory
  without equations generates equality, and theories without equations are compatible with
  every signature relation
-/

@[expose] public section

universe uA uB uA' uB' w w' v v' x x'

namespace PFunctor

/-! ## Relational handlers -/

/-- A relational lifting of the monads `m` and `m'`: a relation `rel R` between computations of
`m α` and `m' β` for each relation `R : α → β → Prop`, with the rule for `pure` (related values
give related computations) and the rule for bind (related computations continued by functions
that send `R`-related results to `R'`-related computations give `R'`-related computations). -/
structure RelLift (m : Type v → Type x) (m' : Type v' → Type x') [Monad m] [Monad m'] where
  /-- The lifted relation between computations. -/
  rel : {α : Type v} → {β : Type v'} → (α → β → Prop) → m α → m' β → Prop
  /-- The rule for `pure`. -/
  rel_pure : ∀ {α : Type v} {β : Type v'} {R : α → β → Prop} {a : α} {b : β}, R a b →
    rel R (pure a) (pure b)
  /-- The rule for bind. -/
  rel_bind : ∀ {α γ : Type v} {β δ : Type v'} {R : α → β → Prop} {R' : γ → δ → Prop}
    {c : m α} {c' : m' β} {f : α → m γ} {g : β → m' δ}, rel R c c' →
    (∀ a b, R a b → rel R' (f a) (g b)) → rel R' (c >>= f) (c' >>= g)

/-- Handlers `h` of `P` in `m` and `h'` of `Q` in `m'` that send positions related by `S` to
computations related by the lifting of the direction relation interpret programs related by
`HFreeRel S R` to computations related by the lifting of `R`. -/
theorem HFreeRel.liftM_rel {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}} {S : SigRel P Q}
    {m : Type uB → Type x} {m' : Type uB' → Type x'} [Monad m] [Monad m'] (L : RelLift m m')
    {h : (a : P.A) → m (P.B a)} {h' : (a' : Q.A) → m' (Q.B a')}
    (hh : ∀ a a', S.pos a a' → L.rel (S.dir a a') (h a) (h' a'))
    {α : Type uB} {β : Type uB'} {R : α → β → Prop} {x : P.FreeM α} {y : Q.FreeM β}
    (hxy : HFreeRel S R x y) : L.rel R (x.liftM h) (y.liftM h') := by
  induction hxy with
  | pure hab => exact L.rel_pure hab
  | liftBind hpos _ ih => exact L.rel_bind (hh _ _ hpos) ih

/-! ## Compatibility of theories with a signature relation -/

/-- The theories `T₁` over `P` and `T₂` over `Q` are compatible with the signature relation `S`
when the lift `HFreeRel S R` is a bisimulation up to the congruences: a congruence step on one
side of a related pair is matched by a congruence step on the other side. -/
structure SigRel.Compat {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}} (S : SigRel P Q)
    (T₁ : EqTheory.{uA, uB, w} P) (T₂ : EqTheory.{uA', uB', w'} Q) : Prop where
  /-- A congruence step on the left is matched on the right. -/
  left : ∀ {α : Type v} {β : Type v'} (R : α → β → Prop) {x x' : P.FreeM α} {y : Q.FreeM β},
    T₁.Cong x x' → HFreeRel S R x y → ∃ y', T₂.Cong y y' ∧ HFreeRel S R x' y'
  /-- A congruence step on the right is matched on the left. -/
  right : ∀ {α : Type v} {β : Type v'} (R : α → β → Prop) {x : P.FreeM α} {y y' : Q.FreeM β},
    T₂.Cong y y' → HFreeRel S R x y → ∃ x', T₁.Cong x x' ∧ HFreeRel S R x' y'

namespace EqTheory

variable {P : PFunctor.{uA, uB}}

/-- A theory without equations generates equality. -/
theorem cong_iff_eq_of_isEmpty (T : EqTheory.{uA, uB, w} P) [IsEmpty T.Eqn] {α : Type v}
    {x x' : P.FreeM α} : T.Cong x x' ↔ x = x' := by
  refine ⟨fun h => ?_, fun h => h ▸ .refl x⟩
  induction h with
  | ax e => exact (IsEmpty.false e).elim
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | liftBind a _ ih => exact congrArg (FreeM.liftBind a) (funext ih)

end EqTheory

/-- Theories without equations are compatible with every signature relation. -/
theorem SigRel.compat_of_isEmpty {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (S : SigRel P Q) (T₁ : EqTheory.{uA, uB, w} P) (T₂ : EqTheory.{uA', uB', w'} Q)
    [IsEmpty T₁.Eqn] [IsEmpty T₂.Eqn] : SigRel.Compat.{uA, uB, uA', uB', w, w', v, v'} S T₁ T₂ where
  left _ _ _ _ hx hxy := ⟨_, .refl _, (T₁.cong_iff_eq_of_isEmpty.1 hx) ▸ hxy⟩
  right _ _ _ _ hy hxy := ⟨_, .refl _, (T₂.cong_iff_eq_of_isEmpty.1 hy) ▸ hxy⟩

/-! ## The induced relation on the quotients -/

/-- The relation induced by the signature relation `S` and `R : α → β → Prop` between the free
monads modulo `T₁` and `T₂`: two classes are related when they have representatives related by
`HFreeRel S R`. -/
def QFreeRel {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}} (S : SigRel P Q)
    (T₁ : EqTheory.{uA, uB, w} P) (T₂ : EqTheory.{uA', uB', w'} Q) {α : Type v} {β : Type v'}
    (R : α → β → Prop) (q₁ : QFreeM T₁ α) (q₂ : QFreeM T₂ β) : Prop :=
  ∃ x y, QFreeM.mk x = q₁ ∧ QFreeM.mk y = q₂ ∧ HFreeRel S R x y

namespace QFreeRel

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}} {S : SigRel P Q}
variable {T₁ : EqTheory.{uA, uB, w} P} {T₂ : EqTheory.{uA', uB', w'} Q}

/-- Classes of related programs are related. -/
theorem mk {α : Type v} {β : Type v'} {R : α → β → Prop} {x : P.FreeM α} {y : Q.FreeM β}
    (hxy : HFreeRel S R x y) : QFreeRel S T₁ T₂ R (QFreeM.mk x) (QFreeM.mk y) :=
  ⟨x, y, rfl, rfl, hxy⟩

/-- Related values give related `pure` classes. -/
theorem pure {α : Type v} {β : Type v'} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    QFreeRel S T₁ T₂ R (QFreeM.pure a) (QFreeM.pure b) :=
  mk (.pure hab)

/-- The generic operations at related positions are related along the direction relation. -/
theorem op {a : P.A} {a' : Q.A} (ha : S.pos a a') :
    QFreeRel S T₁ T₂ (S.dir a a') (QFreeM.op a) (QFreeM.op a') :=
  mk (.liftBind ha fun _ _ hd => .pure hd)

/-- The induced relation is monotone in the relation on results. -/
theorem mono {α : Type v} {β : Type v'} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b)
    {q₁ : QFreeM T₁ α} {q₂ : QFreeM T₂ β} (hq : QFreeRel S T₁ T₂ R q₁ q₂) :
    QFreeRel S T₁ T₂ R' q₁ q₂ :=
  let ⟨x, y, hx, hy, hxy⟩ := hq
  ⟨x, y, hx, hy, hxy.mono h⟩

/-- Under compatibility, two classes are related exactly when a given representative on the
left is related to a program congruent to a given representative on the right. -/
theorem mk_iff_left (hC : SigRel.Compat.{uA, uB, uA', uB', w, w', v, v'} S T₁ T₂) {α : Type v}
    {β : Type v'} {R : α → β → Prop} {x : P.FreeM α} {y : Q.FreeM β} :
    QFreeRel S T₁ T₂ R (QFreeM.mk x) (QFreeM.mk y) ↔ ∃ y', T₂.Cong y y' ∧ HFreeRel S R x y' := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨y', hvy', hxy'⟩ := hC.left R (Quotient.exact hu) huv
    exact ⟨y', (Quotient.exact hv).symm.trans hvy', hxy'⟩
  · rintro ⟨y', hy, hxy'⟩
    exact ⟨x, y', rfl, (QFreeM.sound hy).symm, hxy'⟩

/-- Under compatibility, two classes are related exactly when a program congruent to a given
representative on the left is related to a given representative on the right. -/
theorem mk_iff_right (hC : SigRel.Compat.{uA, uB, uA', uB', w, w', v, v'} S T₁ T₂) {α : Type v}
    {β : Type v'} {R : α → β → Prop} {x : P.FreeM α} {y : Q.FreeM β} :
    QFreeRel S T₁ T₂ R (QFreeM.mk x) (QFreeM.mk y) ↔ ∃ x', T₁.Cong x x' ∧ HFreeRel S R x' y := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨x', hux', hxy'⟩ := hC.right R (Quotient.exact hv) huv
    exact ⟨x', (Quotient.exact hu).symm.trans hux', hxy'⟩
  · rintro ⟨x', hx, hxy'⟩
    exact ⟨x', y, (QFreeM.sound hx).symm, rfl, hxy'⟩

/-- **Relational handlers on the quotients.** Handlers that validate `T₁` and `T₂` and send
positions related by `S` to computations related by the lifting of the direction relation
interpret related classes to computations related by the lifting of `R`. -/
theorem lift_rel {m : Type uB → Type x} {m' : Type uB' → Type x'} [Monad m] [LawfulMonad m]
    [Monad m'] [LawfulMonad m'] (L : RelLift m m')
    {h : (a : P.A) → m (P.B a)} {h' : (a' : Q.A) → m' (Q.B a')}
    (hT₁ : T₁.Validates h) (hT₂ : T₂.Validates h')
    (hh : ∀ a a', S.pos a a' → L.rel (S.dir a a') (h a) (h' a'))
    {α : Type uB} {β : Type uB'} {R : α → β → Prop} {q₁ : QFreeM T₁ α} {q₂ : QFreeM T₂ β}
    (hq : QFreeRel S T₁ T₂ R q₁ q₂) : L.rel R (QFreeM.lift h hT₁ q₁) (QFreeM.lift h' hT₂ q₂) := by
  obtain ⟨x, y, rfl, rfl, hxy⟩ := hq
  exact hxy.liftM_rel L hh

/-- **Identity extension.** Along an identity signature relation and one theory, the relation
induced by equality is equality. -/
theorem eq_iff {S : SigRel P P} (hS : S.IsId) {T : EqTheory.{uA, uB, w} P} {α : Type v}
    {q q' : QFreeM T α} : QFreeRel S T T (· = ·) q q' ↔ q = q' := by
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    rw [freeRel_eq_iff.1 ((hFreeRel_iff_freeRel hS).1 hxy)]
  · rintro rfl
    obtain ⟨x, rfl⟩ := QFreeM.exists_mk q
    exact mk ((hFreeRel_iff_freeRel hS).2 (freeRel_eq_iff.2 rfl))

end QFreeRel

end PFunctor

end
