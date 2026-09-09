/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.EmulatesQuotient
public import PolyFun.Interaction.UC.OpenSyntax.Expr
public import Mathlib.Data.Setoid.Basic

/-!
# Quotient-theory examples

Regression checks for quotient open theories. A theory whose laws hold modulo
a congruence has a strictly lawful quotient; a strict theory satisfies every
law modulo any congruence; the free syntax model is the quotient of raw syntax
by its congruence, so raw syntax inherits the whole `Emulates` composition
suite at the observation pulled back from equality of classes.
-/

@[expose] public section

universe u

namespace Interaction.UC.QuotientExamples

open OpenTheory OpenSyntax

/-- A strict theory satisfies every law modulo the discrete congruence, and the
quotient by it is again strict. -/
example (T : OpenTheory.{u}) [HasPlugWireFactor T] :
    HasPlugWireFactorMod (Congruence.eq T) :=
  inferInstance

example (T : OpenTheory.{u}) [HasPlugWireFactor T] :
    HasPlugWireFactor (T.quotient (Congruence.eq T)) :=
  inferInstance

example (T : OpenTheory.{u}) [HasPlugFactorization T] :
    HasPlugFactorization (T.quotient (Congruence.eq T)) :=
  inferInstance

/-- The free syntax model is the quotient of raw syntax, and raw syntax
satisfies the laws modulo its congruence. -/
example (Atom : PortBoundary → Type u) :
    Expr.theory Atom = (Raw.theory Atom).quotient (Raw.congruence Atom) :=
  rfl

example (Atom : PortBoundary → Type u) : HasPlugWireFactorMod (Raw.congruence Atom) :=
  inferInstance

example (Atom : PortBoundary → Type u) : HasPlugWireFactor (Expr.theory Atom) :=
  inferInstance

/-- Raw syntax is not lawful, but emulation over raw syntax at the observation
pulled back from equality of classes has the full composition suite: the
quotient satisfies plug factorization, so the pulled-back observation respects
it. -/
example (Atom : PortBoundary → Type u) {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : Raw Atom Δ₁} {real₂ ideal₂ : Raw Atom Δ₂}
    (h₁ : Emulates (T := Raw.theory Atom) real₁ ideal₁
      ((Observation.eq ((Raw.theory Atom).quotient (Raw.congruence Atom))).comap
        (Raw.congruence Atom)))
    (h₂ : Emulates (T := Raw.theory Atom) real₂ ideal₂
      ((Observation.eq ((Raw.theory Atom).quotient (Raw.congruence Atom))).comap
        (Raw.congruence Atom))) :
    Emulates (T := Raw.theory Atom) (Raw.par real₁ real₂) (Raw.par ideal₁ ideal₂)
      ((Observation.eq ((Raw.theory Atom).quotient (Raw.congruence Atom))).comap
        (Raw.congruence Atom)) :=
  Emulates.par_compose h₁ h₂

/-- Emulation of classes is emulation of representatives; at the free model
the pulled-back observation is `Raw.Equiv` on closed raw terms. -/
example (Atom : PortBoundary → Type u) {Δ : PortBoundary} {real ideal : Raw Atom Δ} :
    Emulates (T := Expr.theory Atom) (Expr.mk real) (Expr.mk ideal)
        (Observation.eq (Expr.theory Atom)) ↔
      Emulates (T := Raw.theory Atom) real ideal
        (Observation.ofCongruence (Raw.congruence Atom)) :=
  (Emulates.ofCongruence_iff (Raw.congruence Atom)).symm

example (Atom : PortBoundary → Type u) (c₁ c₂ : Raw Atom PortBoundary.empty) :
    (Observation.ofCongruence (Raw.congruence Atom)).rel c₁ c₂ ↔ Raw.Equiv c₁ c₂ :=
  Iff.rfl

/-- An `E`-invariant observation descends to the quotient and pulls back to
itself. -/
example (T : OpenTheory.{u}) (E : Congruence T) (Obs : Observation T)
    (hInv : ∀ {c₁ c₂ : T.Closed}, E.rel c₁ c₂ → Obs.rel c₁ c₂) (c₁ c₂ : T.Closed) :
    ((Obs.descend E hInv).comap E).rel c₁ c₂ ↔ Obs.rel c₁ c₂ :=
  Observation.comap_descend_rel E Obs hInv

/-! ## A nontrivial congruence repairs failed laws -/

/-- Boundary transport adds two, so identity transport fails before quotienting. -/
abbrev shiftedTheory : OpenTheory where
  Obj _ := Nat
  map _ n := n + 2
  par := (· + ·)
  wire := (· + ·)
  plug := (· + ·)

/-- The kernel of parity identifies exactly the even shifts. -/
def parity : Congruence shiftedTheory where
  setoid _ := Setoid.ker (· % 2)
  map_congr := by
    intro Δ Δ' f a b h
    change a % 2 = b % 2 at h
    change (a + 2) % 2 = (b + 2) % 2
    simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using h
  par_congr := by
    intro Δ Δ' a b c d h k
    change a % 2 = b % 2 at h
    change c % 2 = d % 2 at k
    change (a + c) % 2 = (b + d) % 2
    simp only [Nat.add_mod, Nat.mod_mod, h, k]
  wire_congr := by
    intro Δ Γ Δ' a b c d h k
    change a % 2 = b % 2 at h
    change c % 2 = d % 2 at k
    change (a + c) % 2 = (b + d) % 2
    simp only [Nat.add_mod, Nat.mod_mod, h, k]
  plug_congr := by
    intro Δ a b c d h k
    change a % 2 = b % 2 at h
    change c % 2 = d % 2 at k
    change (a + c) % 2 = (b + d) % 2
    simp only [Nat.add_mod, Nat.mod_mod, h, k]

instance : IsLawfulMod parity where
  map_id _ := by change (_ + 2) % 2 = _ % 2; simp
  map_comp _ _ _ := by change (_ + 2) % 2 = ((_ + 2) + 2) % 2; simp
  map_par _ _ _ _ := by change ((_ + _) + 2) % 2 = ((_ + 2) + (_ + 2)) % 2; simp [Nat.add_mod]
  map_wire _ _ _ _ := by change ((_ + _) + 2) % 2 = ((_ + 2) + (_ + 2)) % 2; simp [Nat.add_mod]
  map_plug _ _ _ := by change ((_ + 2) + _) % 2 = (_ + (_ + 2)) % 2; simp [Nat.add_mod]

/-- Strict lawfulness fails even though lawfulness modulo parity holds. -/
example : ¬ IsLawful shiftedTheory := by
  intro h
  have bad := OpenTheory.map_id (T := shiftedTheory) (Δ := PortBoundary.empty) 0
  change 2 = 0 at bad
  contradiction

example : IsLawful (shiftedTheory.quotient parity) := inferInstance
example : parity.cls (Δ := PortBoundary.empty) 1 = parity.cls 3 := by
  apply parity.cls_eq_cls.mpr
  rfl
example : parity.cls (Δ := PortBoundary.empty) 0 ≠ parity.cls 1 := by
  intro h
  have bad := parity.cls_eq_cls.mp h
  change 0 % 2 = 1 % 2 at bad
  contradiction

/-- Equality of representatives is not invariant under parity and cannot descend. -/
example : ¬ (∀ {a b : shiftedTheory.Closed}, parity.rel a b → (Observation.eq _).rel a b) := by
  intro h
  have hE : parity.rel (Δ := PortBoundary.empty) 1 3 := by rfl
  have bad : (1 : Nat) = 3 := Observation.eq_rel.mp (h hE)
  omega

/-! ## Contexts can forget distinctions between classes -/

/-- Closing a process discards its value. -/
abbrev blindTheory : OpenTheory where
  Obj _ := Nat
  map _ := id
  par := (· + ·)
  wire := (· + ·)
  plug _ _ := 0

example : (Congruence.eq blindTheory).cls (Δ := PortBoundary.empty) 0 ≠
    (Congruence.eq blindTheory).cls 1 := by
  intro h
  exact Nat.zero_ne_one (Congruence.eq_rel.mp ((Congruence.eq blindTheory).cls_eq_cls.mp h))

example :
    Emulates ((Congruence.eq blindTheory).cls (Δ := PortBoundary.empty) 0)
      ((Congruence.eq blindTheory).cls 1)
      (Observation.eq (blindTheory.quotient (Congruence.eq blindTheory))) := by
  apply (Emulates.quotient_iff (Congruence.eq blindTheory)).mpr
  refine ⟨fun K => ?_⟩
  apply (Observation.comap_eq_rel (Congruence.eq blindTheory)).mpr
  exact Congruence.eq_rel.mpr rfl

end Interaction.UC.QuotientExamples
