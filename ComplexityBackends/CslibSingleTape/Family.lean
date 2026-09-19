/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Description
public import ComplexityBackends.CslibSingleTape.BasicMachines
public import PolyFun.Realizability.Quantitative.Family

/-!
# The single-tape backend as a polynomial backend

A witness's canonical time polynomial is its certified `time`; the output-size envelope is
`1 + X + p` (`EncPolyTime.length_le`), and the composition overhead is `q.comp (1 + X + p)`
(`EncPolyTime.comp_time_eval`), the second machine's polynomial evaluated at the first's output
envelope. Description size is the state count and adds under composition.

With these certificates the backend's `EncPolyTimeFam` is the generic `FamRealizer` field for
field: `EncPolyTimeFam.toFam` and `EncPolyTimeFam.ofFam` are mutually inverse by reflexivity.
`Backend.finiteTables` packages the finite-table machine `EncPolyTime.ofFintype` with its two
bounds as the advice primitive.
-/

public section

open PFunctor Cslib.Turing.SingleTapeTM

namespace ComplexityBackends.CslibSingleTape

namespace Backend

/-- The single-tape backend's canonical polynomial certificates. Exposed so that `timeOf` reduces
to `EncPolyTime.time` and the envelope and overhead reduce to their polynomial shapes. -/
@[expose] noncomputable def polynomialBackend : description.PolynomialBackend where
  timeOf r := r.time
  cost_le _ _ := le_rfl
  envelope p := 1 + Polynomial.X + p
  size_le r x := by
    have h := r.length_le x
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    omega
  envelope_le n hp k := by
    have := hp k
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    omega
  overhead p q := q.comp (1 + Polynomial.X + p)
  overhead_le n hp hq k := by
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    refine (hq _).trans (Polynomial.eval_le_eval ?_)
    have := hp k
    omega
  timeOf_compose_le r s k := by
    change (r.comp s).time.eval k ≤ _
    rw [EncPolyTime.comp_time_eval]
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    omega
  idTime := .C 1
  timeOf_identity_le a k := by
    change (EncPolyTime.id a).time.eval k ≤ _
    simp [EncPolyTime.time_id]
  idDesc := 1
  descSize_identity_le a := by
    change (EncPolyTime.id a).size ≤ 1
    simp [EncPolyTime.size_id]
  descSize_compose_le r s := by
    change (r.comp s).size ≤ r.size + s.size
    exact (EncPolyTime.size_comp r s).le

/-- The canonical time polynomial of a witness is its certified time. -/
@[simp] theorem timeOf_eq {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}
    (r : EncPolyTime a b f) : polynomialBackend.timeOf r = r.time :=
  rfl

/-- The finite-table primitive, from `EncPolyTime.ofFintype` and its size and time bounds;
faithfulness of the input representation is injectivity. Exposed so that `table` reduces to the
finite-table machine. -/
@[expose] noncomputable def finiteTables : description.FiniteTables polynomialBackend Faithful where
  table a ha b f := EncPolyTime.ofFintype a ha b f
  descSize_table_le := by
    intro A B _ a ha b f K La Lb hcard hla hB
    exact EncPolyTime.size_ofFintype_le_of_bounds ha hcard hla hB
  time_table_le := by
    intro A B _ a ha b f Lb hB k
    exact EncPolyTime.time_ofFintype_eval_le ha hB k

end Backend

namespace EncPolyTimeFam

variable {D E : ℕ → Type} {ea : ∀ n, D n → List Bool} {eb : ∀ n, E n → List Bool}
  {f : ∀ n, D n → E n}

/-- A uniform machine family is a generic realizer family over the single-tape backend, field for
field. Exposed so that the round trip with `ofFam` holds by reflexivity. -/
@[expose] def toFam (h : EncPolyTimeFam ea eb f) :
    Backend.description.FamRealizer Backend.polynomialBackend ea eb f where
  wit := h.wit
  time := h.time
  time_le := h.time_le
  desc := h.size
  desc_le := h.size_le

/-- A generic realizer family over the single-tape backend is a uniform machine family. Exposed so
that the round trip with `toFam` holds by reflexivity. -/
@[expose] def ofFam (X : Backend.description.FamRealizer Backend.polynomialBackend ea eb f) :
    EncPolyTimeFam ea eb f where
  wit := X.wit
  time := X.time
  time_le := X.time_le
  size := X.desc
  size_le := X.desc_le

/-- The two presentations are inverse. -/
theorem ofFam_toFam (h : EncPolyTimeFam ea eb f) : ofFam h.toFam = h :=
  rfl

/-- The two presentations are inverse. -/
theorem toFam_ofFam (X : Backend.description.FamRealizer Backend.polynomialBackend ea eb f) :
    (ofFam X).toFam = X :=
  rfl

end EncPolyTimeFam

end ComplexityBackends.CslibSingleTape
