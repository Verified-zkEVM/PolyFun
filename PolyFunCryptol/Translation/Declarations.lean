/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.OpenElaboration
public import PolyFunCryptol.Model.PolyLaws

/-!
# Ordered typed declaration environments

Each nonrecursive body sees only earlier declarations. A recursive group sees
its own members and the earlier environment. Closing a consumer uses the
canonical polynomial `letE` and `letRec` constructors, with one fixed point per
recursive group and no additional suspension at module boundaries.
-/

public section

namespace Cryptol.Translation

open Polymorphic OmegaCompletePartialOrder

/-- Source identities paired with their checked schemes, nearest binding first. -/
abbrev Signatures (w : Scope) := List (Reference.Name × w.ValueSort)

/-- A sequence of declarations extending a named typed environment. -/
inductive Declarations (w : Scope) : Signatures w → Signatures w → Type 1 where
  | nil (Γ : Signatures w) : Declarations w Γ Γ
  | nonrecursive {Γ Δ : Signatures w} (name : Reference.Name) (s : w.ValueSort)
      (value : Term w (Γ.map Prod.snd) s)
      (rest : Declarations w ((name, s) :: Γ) Δ) : Declarations w Γ Δ
  | recursive {Γ Δ : Signatures w} (bindings : Signatures w)
      (values : (i : Fin (bindings.map Prod.snd).length) →
        Term w (bindings.map Prod.snd ++ Γ.map Prod.snd) (bindings.map Prod.snd)[i])
      (rest : Declarations w (bindings ++ Γ) Δ) : Declarations w Γ Δ

namespace Declarations

/-- New declarations in the order in which the final environment stores them. -/
@[expose] def introduced {w : Scope} {Γ Δ : Signatures w} : Declarations w Γ Δ → Signatures w
  | .nil _ => []
  | .nonrecursive name s _ rest => rest.introduced ++ [(name, s)]
  | .recursive bindings _ rest => rest.introduced ++ bindings

/-- A declaration sequence retains its entire ambient environment as a suffix. -/
theorem bindings_eq {w : Scope} {Γ Δ : Signatures w} (ds : Declarations w Γ Δ) :
    Δ = ds.introduced ++ Γ := by
  induction ds with
  | nil => rfl
  | nonrecursive name s value rest ih => simpa [introduced, List.append_assoc] using ih
  | recursive bindings values rest ih => simpa [introduced, List.append_assoc] using ih

/-- Sequence checked declaration blocks without flattening their recursive groups. -/
@[expose] def append {w : Scope} {Γ Δ Ω : Signatures w}
    (first : Declarations w Γ Δ) (second : Declarations w Δ Ω) : Declarations w Γ Ω :=
  match first with
  | .nil _ => second
  | .nonrecursive name s value rest => .nonrecursive name s value (rest.append second)
  | .recursive bindings values rest => .recursive bindings values (rest.append second)

/-- Sequencing preserves both blocks' declaration identities. -/
theorem introduced_append {w : Scope} {Γ Δ Ω : Signatures w}
    (first : Declarations w Γ Δ) (second : Declarations w Δ Ω) :
    (first.append second).introduced = second.introduced ++ first.introduced := by
  induction first with
  | nil => simp [append, introduced]
  | nonrecursive name s value rest ih => simp [append, introduced, ih, List.append_assoc]
  | recursive bindings values rest ih => simp [append, introduced, ih, List.append_assoc]

/-- Close a consumer under the original ordered declaration groups. -/
@[expose] def close {w : Scope} {Γ Δ : Signatures w} (ds : Declarations w Γ Δ)
    {s : w.ValueSort} (body : Term w (Δ.map Prod.snd) s) : Term w (Γ.map Prod.snd) s :=
  match ds with
  | .nil _ => body
  | .nonrecursive _ _ value rest => .letE value (rest.close body)
  | .recursive bindings values rest =>
      .letRec (bindings.map Prod.snd) values (List.map_append ▸ rest.close body)

/-- Interpret the sequence by extending the environment in source order. -/
@[expose] noncomputable def denote {w : Scope} {Γ Δ : Signatures w}
    (ds : Declarations w Γ Δ) (ρ : w.Assignment) :
    Env ρ (Γ.map Prod.snd) →𝒄 Env ρ (Δ.map Prod.snd) :=
  match ds with
  | .nil _ => .id
  | .nonrecursive _ _ value rest =>
      (rest.denote ρ).comp ((Env.cons ρ).comp (.ofFun (fun η => (η, value.denote ρ η))))
  | .recursive bindings values rest =>
      let group := IPFunctor.ScopedDomain.Env.fixGroup (fun s => s.domain ρ.val)
        (fun i => (values i).denote ρ)
      let extend := (Env.append ρ).comp (.ofFun (fun η => (group η, η)))
      (rest.denote ρ).comp (List.map_append.symm ▸ extend)

/-- Interpretation of sequenced blocks is composition of their environment maps. -/
theorem denote_append {w : Scope} {Γ Δ Ω : Signatures w}
    (first : Declarations w Γ Δ) (second : Declarations w Δ Ω) (ρ : w.Assignment) :
    (first.append second).denote ρ = (second.denote ρ).comp (first.denote ρ) := by
  induction first with
  | nil => rfl
  | nonrecursive name s value rest ih =>
      simp only [append, denote, ih]
      rfl
  | recursive bindings values rest ih =>
      simp only [append, denote, ih]
      rfl

/-- Closing syntax and interpreting declaration environments give the same meaning. -/
theorem denote_close {w : Scope} {Γ Δ : Signatures w} (ds : Declarations w Γ Δ)
    (ρ : w.Assignment) {s : w.ValueSort} (body : Term w (Δ.map Prod.snd) s)
    (η : Env ρ (Γ.map Prod.snd)) :
    (ds.close body).denote ρ η = body.denote ρ (ds.denote ρ η) := by
  induction ds with
  | nil => rfl
  | nonrecursive name s value rest ih =>
      rw [close, Term.denote_letE, ih]
      rfl
  | recursive bindings values rest ih =>
      rw [close, Term.denote_letRec]
      have cast_denote {Ξ Ω : List w.ValueSort} (h : Ξ = Ω)
          (term : Term w Ξ s) (env : Env ρ Ω) :
          (h ▸ term).denote ρ env = term.denote ρ (h.symm ▸ env) := by
        cases h
        rfl
      rw [cast_denote, ih]
      have cast_apply {Γ₀ Ξ Ω : List w.ValueSort} (h : Ξ = Ω)
          (f : Env ρ Γ₀ →𝒄 Env ρ Ξ) (env : Env ρ Γ₀) :
          (h ▸ f) env = h ▸ f env := by
        cases h
        rfl
      simp only [denote, ContinuousHom.comp_apply, cast_apply, ContinuousHom.ofFun_apply]

end Declarations

namespace OpenElaboration

/-- Check each body in precisely the context provided by its declaration group. -/
@[expose] def declarations : Nat → {w : Scope} →
    OpenTypes.Parameters w.numbers w.types → (Γ : Signatures w) →
    List Reference.DeclGroup → Except String ((Δ : Signatures w) × Declarations w Γ Δ)
  | 0, _, _, _, _ => .error "declaration sequence budget exhausted"
  | _ + 1, _, _, Γ, [] => .ok ⟨Γ, .nil Γ⟩
  | fuel + 1, _, params, Γ, .nonrecursive d :: rest => do
      let ⟨s⟩ ← liftCheck (OpenTypes.scheme params fuel d.schema)
      let ⟨body⟩ ← liftCheck (definitionBody d)
      let value ← (elaborate fuel params (Names.ofSignatures Γ) body >>= expect s).mapError
        (fun message => s!"{d.name.origin}: {message}")
      let ⟨Δ, tail⟩ ← declarations fuel params ((d.name, s) :: Γ) rest
      return ⟨Δ, .nonrecursive d.name s value tail⟩
  | fuel + 1, w, params, Γ, .recursive ds :: rest => do
      let ⟨sigs⟩ ← liftCheck (signatures (w := w) params fuel ds)
      let names := Names.extendMany (Names.ofSignatures Γ) sigs
      let values ← bodies fuel params names ds sigs
      let ⟨Δ, tail⟩ ← declarations fuel params (sigs ++ Γ) rest
      return ⟨Δ, .recursive sigs values tail⟩

end OpenElaboration
end Cryptol.Translation
