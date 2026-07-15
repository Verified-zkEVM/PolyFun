/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.SubstMonoid
public import PolyFun.Control.Monad.Hom

/-!
# Extensions of substitution monoids

A polynomial lens induces a natural map between polynomial extensions.  In
particular, the unit and multiplication of a substitution monoid equip the
extension of its carrier with a lawful monad.  This is the extension-level
bridge between monoid objects for polynomial substitution and ordinary
monads on types.
-/

@[expose] public section

universe uA uB

namespace PFunctor

namespace SubstMonoid

/-- The extension of the carrier polynomial of a substitution monoid.  It is
kept as a named type constructor so its monad instance determines the source
substitution monoid unambiguously. -/
@[reducible]
def Extension (M : SubstMonoid.{uA, uB}) (α : Type uB) :
    Type (max uA uB) :=
  M.carrier.Obj α

namespace Extension

variable (M : SubstMonoid.{uA, uB})

/-- The extension-level unit induced by the polynomial unit lens. -/
def pure {α : Type uB} (x : α) : Extension M α :=
  Lens.mapObj M.unit
    (⟨PUnit.unit, fun _ => x⟩ : X.{max uA uB, uB}.Obj α)

/-- The extension-level bind induced by polynomial substitution. -/
def bind {α β : Type uB} (x : Extension M α)
    (f : α → Extension M β) : Extension M β :=
  Lens.mapObj M.mult
    (⟨⟨x.1, fun d => (f (x.2 d)).1⟩,
      fun direction => (f (x.2 direction.1)).2 direction.2⟩ :
      (M.carrier ◃ M.carrier).Obj β)

instance instMonad : Monad (Extension M) where
  pure := pure M
  bind := bind M

@[simp]
theorem pure_def {α : Type uB} (x : α) :
    (Pure.pure x : Extension M α) = pure M x :=
  rfl

@[simp]
theorem bind_def {α β : Type uB} (x : Extension M α)
    (f : α → Extension M β) : x >>= f = bind M x f :=
  rfl

theorem pure_bind {α β : Type uB} (x : α)
    (f : α → Extension M β) :
    (Pure.pure x : Extension M α) >>= f = f x := by
  have h := congrArg (fun lens => Lens.mapObj lens (f x)) M.unit_left
  exact h

theorem bind_pure {α : Type uB} (x : Extension M α) :
    x >>= (fun y => (Pure.pure y : Extension M α)) = x := by
  have h := congrArg (fun lens => Lens.mapObj lens x) M.unit_right
  exact h

theorem bind_assoc {α β γ : Type uB} (x : Extension M α)
    (f : α → Extension M β) (g : β → Extension M γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  let source : ((M.carrier ◃ M.carrier) ◃ M.carrier).Obj γ :=
    ⟨⟨⟨x.1, fun d => (f (x.2 d)).1⟩,
        fun direction => (g ((f (x.2 direction.1)).2 direction.2)).1⟩,
      fun direction =>
        (g ((f (x.2 direction.1.1)).2 direction.1.2)).2 direction.2⟩
  have h := congrArg (fun lens => Lens.mapObj lens source) M.assoc
  exact h

instance instLawfulMonad : LawfulMonad (Extension M) := LawfulMonad.mk'
  (bind_pure_comp := by
    intro α β f x
    have h := congrArg
      (fun lens => Lens.mapObj lens
        (⟨x.1, f ∘ x.2⟩ : M.carrier.Obj β))
      M.unit_right
    exact h)
  (id_map := by intros; rfl)
  (pure_bind := by
    intro α β x f
    exact pure_bind M x f)
  (bind_assoc := by
    intro α β γ x f g
    exact bind_assoc M x f g)

end Extension

namespace Hom

variable {M N : SubstMonoid.{uA, uB}}

/-- A substitution-monoid homomorphism induces a monad homomorphism between
the extensions of its carrier polynomials. -/
def toMonadHom (f : SubstMonoid.Hom M N) :
    (Extension M) →ᵐ (Extension N) where
  toFun _ := Lens.mapObj f.toLens
  toFun_pure' x := by
    have h := congrArg (fun lens => Lens.mapObj lens
      (⟨PUnit.unit, fun _ => x⟩ : X.{max uA uB, uB}.Obj _)) f.map_unit
    exact h
  toFun_bind' x k := by
    let source : (M.carrier ◃ M.carrier).Obj _ :=
      ⟨⟨x.1, fun d => (k (x.2 d)).1⟩,
        fun direction => (k (x.2 direction.1)).2 direction.2⟩
    have h := congrArg (fun lens => Lens.mapObj lens source) f.map_mult
    exact h

@[simp]
theorem toMonadHom_apply (f : SubstMonoid.Hom M N) {α : Type uB}
    (x : Extension M α) :
    f.toMonadHom x = Lens.mapObj f.toLens x :=
  rfl

end Hom

end SubstMonoid

end PFunctor
