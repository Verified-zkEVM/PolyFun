/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Displayed.Decoration
public import PolyFun.PFunctor.Free.Path

/-!
# Decoration along `FreeM.append`

Concatenation of node-local metadata along the dependent sequential composition
`FreeM.append`. The decoration of an appended tree is the `Decoration` of the
prefix paired (per canonical prefix path) with the `Decoration` of the suffix.

This file lives below the protocol layer: nothing here mentions `TypeTree`,
`Path`, or any interaction-specific notion. Protocol-flavored append
combinators are thin specializations of these definitions.
-/

@[expose] public section

universe u v w w₂ w₃ w₄ w₅

namespace PFunctor
namespace FreeM
namespace Displayed
namespace Decoration

variable {P : PFunctor.{u, v}} {α : Type w} {β : Type w₄}

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
rewriting appended decorations over `FreeM.liftBind` trees needs `FreeM.bind`
to unfold there so that `(lift a).bind rest` and `liftBind a rest` agree. -/
attribute [local implicit_reducible] PFunctor.FreeM.bind

/-- Concatenate per-node metadata along `FreeM.append`. -/
@[implicit_reducible]
def append {Γ : P.A → Type w₂}
    {s₁ : FreeM P α} {s₂ : Path s₁ → FreeM P β}
    (d₁ : Decoration Γ s₁)
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) :
    Decoration Γ (FreeM.append s₁ s₂) :=
  match s₁, d₁ with
  | .pure _, _ => d₂ ⟨⟩
  | .liftBind _ _, ⟨γ, dRest⟩ =>
      ⟨γ, fun b => append (dRest b) (fun path => d₂ ⟨b, path⟩)⟩

@[simp, freeM_unfold]
theorem append_pure {Γ : P.A → Type w₂} (x : α)
    (d₁ : Decoration Γ (FreeM.pure (P := P) x))
    (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.pure (P := P) x)) → Decoration Γ (s₂ path₁)) :
    append d₁ d₂ = d₂ ⟨⟩ :=
  rfl

@[simp, freeM_unfold]
theorem append_liftBind {Γ : P.A → Type w₂} (a : P.A) (rest : P.B a → FreeM P α)
    (d₁ : Decoration Γ (FreeM.liftBind a rest))
    (s₂ : Path (FreeM.liftBind a rest) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.liftBind a rest)) → Decoration Γ (s₂ path₁)) :
    append d₁ d₂ =
      ⟨d₁.1, fun b => append (d₁.2 b) (fun path => d₂ ⟨b, path⟩)⟩ :=
  rfl

namespace Over

/-- Concatenate dependent over-decorations along `FreeM.append`, over an
appended base decoration. -/
@[implicit_reducible]
def append {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {s₁ : FreeM P α} {s₂ : Path s₁ → FreeM P β}
    {d₁ : Decoration Γ s₁}
    {d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)}
    (r₁ : Decoration.Over Γ F s₁ d₁)
    (r₂ : (path₁ : Path s₁) → Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Decoration.Over Γ F (FreeM.append s₁ s₂) (Decoration.append d₁ d₂) :=
  match s₁, d₁, r₁ with
  | .pure _, _, _ => r₂ ⟨⟩
  | .liftBind _ _, ⟨_, _⟩, ⟨fData, rRest⟩ =>
      ⟨fData, fun b => append (rRest b) (fun path => r₂ ⟨b, path⟩)⟩

@[simp, freeM_unfold]
theorem append_pure {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (x : α)
    (d₁ : Decoration Γ (FreeM.pure (P := P) x))
    (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.pure (P := P) x)) → Decoration Γ (s₂ path₁))
    (r₁ : Decoration.Over Γ F (FreeM.pure (P := P) x) d₁)
    (r₂ : (path₁ : Path (FreeM.pure (P := P) x)) →
      Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Over.append (s₁ := FreeM.pure (P := P) x) (s₂ := s₂) (d₁ := d₁) (d₂ := d₂)
      r₁ r₂ = r₂ ⟨⟩ :=
  rfl

@[simp, freeM_unfold]
theorem append_liftBind {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    (a : P.A) (rest : P.B a → FreeM P α)
    (d₁ : Decoration Γ (FreeM.liftBind a rest))
    (s₂ : Path (FreeM.liftBind a rest) → FreeM P β)
    (d₂ : (path₁ : Path (FreeM.liftBind a rest)) → Decoration Γ (s₂ path₁))
    (r₁ : Decoration.Over Γ F (FreeM.liftBind a rest) d₁)
    (r₂ : (path₁ : Path (FreeM.liftBind a rest)) →
      Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) :
    Over.append (s₁ := FreeM.liftBind a rest) (s₂ := s₂) (d₁ := d₁) (d₂ := d₂)
      r₁ r₂ =
      ⟨r₁.1, fun b => Over.append (r₁.2 b) (fun path => r₂ ⟨b, path⟩)⟩ :=
  rfl

/-- `Decoration.Over.map` commutes with `Decoration.Over.append`. -/
theorem map_append {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃} {G : (a : P.A) → Γ a → Type w₅}
    (η : ∀ a γ, F a γ → G a γ) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (d₁ : Decoration Γ s₁) →
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) →
    (r₁ : Decoration.Over Γ F s₁ d₁) →
    (r₂ : (path₁ : Path s₁) → Decoration.Over Γ F (s₂ path₁) (d₂ path₁)) →
    Decoration.Over.map η (FreeM.append s₁ s₂) (Decoration.append d₁ d₂)
        (Decoration.Over.append r₁ r₂) =
      Decoration.Over.append (Decoration.Over.map η s₁ d₁ r₁)
        (fun path₁ => Decoration.Over.map η (s₂ path₁) (d₂ path₁) (r₂ path₁))
  | .pure _, _, _, _, _, _ => rfl
  | .liftBind a rest, s₂, ⟨γ, dRest⟩, d₂, ⟨fd, rRest⟩, r₂ => by
      -- Lean 4.33: the `toHom_liftBind` rewrite no longer applies here (its
      -- metavariable assignments fail the implicit-transparency type check),
      -- so the node layer is exposed by `change` instead.
      change
        (η a γ fd, fun b => Decoration.Over.map η
          (FreeM.append (rest b) (fun path => s₂ ⟨b, path⟩))
          (Decoration.append (dRest b) (fun path => d₂ ⟨b, path⟩))
          (Decoration.Over.append (rRest b) (fun path => r₂ ⟨b, path⟩))) =
        (η a γ fd, fun b => Decoration.Over.append
          (Decoration.Over.map η (rest b) (dRest b) (rRest b))
          (fun path => Decoration.Over.map η (s₂ ⟨b, path⟩)
            (d₂ ⟨b, path⟩) (r₂ ⟨b, path⟩)))
      congr 1; funext b
      exact map_append η (rest b) (fun path => s₂ ⟨b, path⟩)
        (dRest b) (fun path => d₂ ⟨b, path⟩) (rRest b)
        (fun path => r₂ ⟨b, path⟩)

end Over

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem map_append {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (d₁ : Decoration Γ s₁) →
    (d₂ : (path₁ : Path s₁) → Decoration Γ (s₂ path₁)) →
    Decoration.map f (FreeM.append s₁ s₂) (Decoration.append d₁ d₂) =
      Decoration.append (Decoration.map f s₁ d₁)
        (fun path₁ => Decoration.map f (s₂ path₁) (d₂ path₁))
  | .pure _, _, _, _ => rfl
  | .liftBind a rest, s₂, ⟨γ, dRest⟩, d₂ => by
      -- Lean 4.33: the `toHom_liftBind` rewrite no longer applies here (its
      -- metavariable assignments fail the implicit-transparency type check),
      -- so the node layer is exposed by `change` instead.
      change
        (f a γ, fun b => Decoration.map f
          (FreeM.append (rest b) (fun path => s₂ ⟨b, path⟩))
          (Decoration.append (dRest b) (fun path => d₂ ⟨b, path⟩))) =
        (f a γ, fun b => Decoration.append
          (Decoration.map f (rest b) (dRest b))
          (fun path => Decoration.map f (s₂ ⟨b, path⟩) (d₂ ⟨b, path⟩)))
      congr 1; funext b
      exact map_append f (rest b) (fun path => s₂ ⟨b, path⟩)
        (dRest b) (fun path => d₂ ⟨b, path⟩)

end Decoration
end Displayed
end FreeM
end PFunctor
