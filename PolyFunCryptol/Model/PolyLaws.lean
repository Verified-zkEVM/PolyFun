/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.PolyConstructors
public import PolyFunCryptol.Model.PolyDenotation

/-! # Public equations of the staged polymorphic semantics -/

public section

open OmegaCompletePartialOrder

namespace Cryptol.Polymorphic

/-- Explicit finite-width evidence identifies the symbolic primitive with its
existing instantiated reference meaning. The choice of evidence is irrelevant. -/
theorem wordLogic_finite {w : Scope} (l : NumExpr w.numbers) (op : BitOp)
    (valid : w.Entails (.fin l)) (ρ : w.Assignment) (n : Nat)
    (hn : l.eval ρ.val.numbers = .finite n) :
    wordLogic l op valid ρ = castComputation (a := .arrow (wordTy n)
      (.arrow (wordTy n) (wordTy n)))
        (by simp only [ParameterAssignment.apply, Ty.instantiate]; rw [hn])
        (Primitive.wordLogic n op).denote := by
  have he : Classical.choose (valid ρ) = n :=
    Length.finite.inj ((Classical.choose_spec (valid ρ)).symm.trans hn)
  subst n
  rfl

namespace Env

variable {w : Scope} (ρ : w.Assignment) {Γ : List w.ValueSort}

/-- Identity context normalization changes no variable value. -/
theorem same_eq (η : Env ρ Γ) : same ρ η = (List.map_id Γ).symm ▸ η := by
  exact IPFunctor.ScopedDomain.Env.reindex_id η

/-- Normalize an ambient identity map beneath one value binder. -/
theorem cons_same {s : w.ValueSort} (η : Env ρ Γ) (x : s.Meaning ρ.val) :
    cons ρ (same ρ η, x) =
      (congrArg (s :: ·) (List.map_id Γ)).symm ▸ cons ρ (η, x) := by
  rw [same_eq]
  exact transport (List.map_id Γ).symm η x
where
  transport {Δ : List w.ValueSort} (h : Γ = Δ) (η : Env ρ Γ) (x : s.Meaning ρ.val) :
      cons ρ (h ▸ η, x) = congrArg (s :: ·) h ▸ cons ρ (η, x) := by
    cases h
    rfl

/-- Normalize an ambient identity map beneath a simultaneous declaration group. -/
theorem append_same {Ξ : List w.ValueSort} (ξ : Env ρ Ξ) (η : Env ρ Γ) :
    append ρ (ξ, same ρ η) =
      (congrArg (Ξ ++ ·) (List.map_id Γ)).symm ▸ append ρ (ξ, η) := by
  rw [same_eq]
  exact transport (List.map_id Γ).symm ξ η
where
  transport {Δ Ξ : List w.ValueSort} (h : Γ = Δ) (ξ : Env ρ Ξ) (η : Env ρ Γ) :
      append ρ (ξ, h ▸ η) = congrArg (Ξ ++ ·) h ▸ append ρ (ξ, η) := by
    cases h
    rfl

end Env

namespace Term

variable {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort} (ρ : w.Assignment)

@[simp] theorem denote_var (x : IPFunctor.ScopedVar Γ s) (η : Env ρ Γ) :
    (var x).denote ρ η = η s x := rfl

/-- Transport syntax and its environment along the same context equality. -/
theorem denote_cast {Δ : List w.ValueSort} (h : Γ = Δ) (t : Term w Γ s) (η : Env ρ Γ) :
    (h ▸ t).denote ρ (h ▸ η) = t.denote ρ η := by
  cases h
  rfl

@[simp] theorem denote_same (t : Term w Γ s) (η : Env ρ Γ) :
    t.same.denote ρ (Env.same ρ η) = t.denote ρ η := by
  rw [Env.same_eq]
  unfold same
  exact denote_cast ρ (List.map_id Γ).symm t η

/-- Normalize the polynomial context map beneath a local value binder. -/
theorem denote_underSame_cons {a : w.ValueSort} (t : Term w (a :: Γ) s)
    (η : Env ρ Γ) (x : a.Meaning ρ.val) :
    (underSame [a] t).denote ρ (Env.cons ρ (Env.same ρ η, x)) =
      t.denote ρ (Env.cons ρ (η, x)) := by
  rw [Env.cons_same]
  exact denote_cast ρ _ t _

/-- Normalize context transport beneath all members of a recursive group. -/
theorem denote_underSame_append (Ξ : List w.ValueSort) (t : Term w (Ξ ++ Γ) s)
    (ξ : Env ρ Ξ) (η : Env ρ Γ) :
    (underSame Ξ t).denote ρ (Env.append ρ (ξ, Env.same ρ η)) =
      t.denote ρ (Env.append ρ (ξ, η)) := by
  rw [Env.append_same]
  exact denote_cast ρ _ t _

@[simp] theorem denote_bit (b : Bool) (η : Env ρ Γ) :
    (bit b).denote ρ η = DomainResult.value ⟨b⟩ := rfl

@[simp] theorem denote_error (e : EvalError) (η : Env ρ Γ) :
    (error s e).denote ρ η = s.error ρ.val e := rfl

@[simp] theorem denote_numAbs {body : Scheme (w.numbers + 1) w.types}
    (t : Term w.bindNum
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types))) body)
    (η : Env ρ Γ) :
    (numAbs t).denote ρ η = DomainResult.value
      (fun l => t.denote (ρ.extendNum l) (Env.enterNum ρ l η)) := rfl

@[simp] theorem denote_typeAbs {body : Scheme w.numbers (w.types + 1)}
    (t : Term w.bindType
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types))) body)
    (η : Env ρ Γ) :
    (typeAbs t).denote ρ η = DomainResult.value
      (fun a => t.denote (ρ.extendType a) (Env.enterType ρ a η)) := rfl

@[simp] theorem denote_numApp {body : Scheme (w.numbers + 1) w.types}
    (t : Term w Γ (.allNum body)) (a : NumExpr w.numbers) (η : Env ρ Γ) :
    (numApp t a).denote ρ η = body.applyNum a ρ.val (t.denote ρ η) := by
  change body.applyNum a ρ.val (t.same.denote ρ (Env.same ρ η)) = _
  rw [denote_same]

@[simp] theorem denote_typeApp {body : Scheme w.numbers (w.types + 1)}
    (t : Term w Γ (.allType body)) (a : PolyTy w.numbers w.types) (η : Env ρ Γ) :
    (typeApp t a).denote ρ η = body.applyType a ρ.val (t.denote ρ η) := by
  change body.applyType a ρ.val (t.same.denote ρ (Env.same ρ η)) = _
  rw [denote_same]

/-- Numeric beta reduction selects the body under the extended assignment. -/
theorem denote_numBeta {body : Scheme (w.numbers + 1) w.types}
    (t : Term w.bindNum
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types))) body)
    (a : NumExpr w.numbers) (η : Env ρ Γ) :
    (numApp (numAbs t) a).denote ρ η =
      PointedDomain.cast (body.domain_singleNum a ρ.val).symm
        (t.denote (ρ.extendNum (a.eval ρ.val.numbers))
          (Env.enterNum ρ (a.eval ρ.val.numbers) η)) := by
  rw [denote_numApp, denote_numAbs]
  rfl

/-- Type beta reduction selects the body under the extended assignment. -/
theorem denote_typeBeta {body : Scheme w.numbers (w.types + 1)}
    (t : Term w.bindType
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types))) body)
    (a : PolyTy w.numbers w.types) (η : Env ρ Γ) :
    (typeApp (typeAbs t) a).denote ρ η =
      PointedDomain.cast (body.domain_singleType a ρ.val).symm
        (t.denote (ρ.extendType (ρ.val.apply a)) (Env.enterType ρ (ρ.val.apply a) η)) := by
  rw [denote_typeApp, denote_typeAbs]
  rfl

@[simp] theorem denote_lam {a b : PolyTy w.numbers w.types}
    (t : Term w (.mono a :: Γ) (.mono b)) (η : Env ρ Γ) :
    (lam t).denote ρ η = DomainResult.value (ContinuousHom.ofFun
      (fun x : Computation (ρ.val.apply a) => t.denote ρ (Env.cons ρ (η, x)))) := by
  apply congrArg DomainResult.value
  apply ContinuousHom.ext
  intro x
  exact denote_underSame_cons ρ t η x

@[simp] theorem denote_app {a b : PolyTy w.numbers w.types}
    (f : Term w Γ (.mono (.arrow a b))) (x : Term w Γ (.mono a)) (η : Env ρ Γ) :
    (app f x).denote ρ η = DomainResult.applyContinuous (f.denote ρ η) (x.denote ρ η) := by
  change DomainResult.applyContinuous (f.same.denote ρ (Env.same ρ η))
    (x.same.denote ρ (Env.same ρ η)) = _
  rw [denote_same, denote_same]

/-- Lazy value beta reduction passes a suspended argument into the body environment. -/
theorem denote_beta {a b : PolyTy w.numbers w.types}
    (body : Term w (.mono a :: Γ) (.mono b)) (value : Term w Γ (.mono a)) (η : Env ρ Γ) :
    (app (lam body) value).denote ρ η =
      body.denote ρ (Env.cons ρ (η, value.denote ρ η)) := by
  rw [denote_app, denote_lam]
  rfl

@[simp] theorem denote_letE {a b : w.ValueSort} (value : Term w Γ a)
    (body : Term w (a :: Γ) b) (η : Env ρ Γ) :
    (letE value body).denote ρ η = body.denote ρ (Env.cons ρ (η, value.denote ρ η)) := by
  change (underSame [a] body).denote ρ
    (Env.cons ρ (Env.same ρ η, value.same.denote ρ (Env.same ρ η))) = _
  rw [denote_same, denote_underSame_cons]

/-- Recursive groups use the shared environment fixed point, without context casts in clients. -/
theorem denote_letRec (bindings : List w.ValueSort)
    (rhs : (i : Fin bindings.length) → Term w (bindings ++ Γ) bindings[i])
    (body : Term w (bindings ++ Γ) s) (η : Env ρ Γ) :
    (letRec bindings rhs body).denote ρ η = body.denote ρ
      (Env.append ρ (IPFunctor.ScopedDomain.Env.fixGroup
        (fun i => (rhs i).denote ρ) η, η)) := by
  change (underSame bindings body).denote ρ (Env.append ρ
    (IPFunctor.ScopedDomain.Env.fixGroup
      (fun i => (underSame bindings (rhs i)).denote ρ) (Env.same ρ η), Env.same ρ η)) = _
  rw [denote_underSame_append]
  congr 2
  apply congrArg (fun ξ => (ξ, η))
  apply IPFunctor.ScopedDomain.Env.fixGroup_congr
  intro ξ i
  exact denote_underSame_append ρ bindings (rhs i) ξ η

@[simp] theorem denote_proofAbs (c : Constraint w.numbers w.types) (t : Term (w.assume c) Γ s)
    (η : Env ρ Γ) :
    (proofAbs c t).denote ρ η =
      fun h : PLift (c.Holds ρ.val.numbers ρ.val.types) => t.denote (ρ.assume h.down) η := by
  funext h
  exact denote_same (ρ.assume h.down) t η

@[simp] theorem denote_proofApp {c : Constraint w.numbers w.types} (t : Term w Γ (.guard c s))
    (valid : w.Entails c) (η : Env ρ Γ) :
    (proofApp t valid).denote ρ η = t.denote ρ η ⟨valid ρ⟩ := by
  change t.same.denote ρ (Env.same ρ η) ⟨valid ρ⟩ = _
  rw [denote_same]

/-- The closed embedding preserves the existing resolved semantics exactly. -/
@[simp] theorem denote_closed {a : ClosedTy} (t : Resolved.Term [] a) (η : Env ρ Γ) :
    (closed t).denote ρ η = castComputation (apply_quoteType ρ.val a).symm
      (Resolved.denote t Environment.empty) := rfl

end Term
end Cryptol.Polymorphic
