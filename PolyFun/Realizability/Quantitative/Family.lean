/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Counting
public import ToCslib.Algebra.Polynomial

/-!
# Polynomial backends and families of realizers

A `FamRealizer` is a parameter-indexed family of realizers: one realizer per security parameter
`n`, whose canonical time polynomials are uniformly dominated by a single polynomial in `n + k`
(`k` the encoded input size), and whose description sizes are dominated by a polynomial in `n`
(the advice bound). The `n + k` form is the formal content of the `1^n` convention at this layer:
a resource bound polynomial in the parameter plus the input length, and nothing else.

The composition theorem controls the backend's *canonical* time polynomials at every input
length, including hypothetical lengths used by an output envelope. A per-use `PolyRealizer`
bounds costs on actual inputs but need not dominate the backend's selected polynomial at every
length. Uniform families therefore need uniform control of composition overhead as well as
local cost bounds. `PolynomialTimeBackend` supplies this through canonical certificates and
shifted envelope laws; `DescriptionComposition` supplies the separate advice bounds.

`FiniteTables` is the advice primitive: every function out of a finite domain with a faithful
input representation has a realizer with linear canonical time and a description of the size of
its table, so families over polynomially small domains stay within a polynomial advice bound.

`FamRealizer.mem_realizableLE` is the bridge to the counting layer: a family's advice bound is
exactly a polynomial description bound at every parameter, so `exists_not_famRealizer` reads the
counting separation back as the non-existence of a uniform realizer family. Without that bridge
the separation and the composition layer would be about unrelated objects.
-/

public section

universe u v w x

open Filter

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}

/-- Canonical polynomial time certificates, output-size envelopes and executable composition
bounds. This contract does not require a description measure or an advice bound. -/
structure PolynomialTimeBackend (Q : QuantitativeStepClass.{u, v, w} C)
    [Q.HasComposition] where
  /-- Canonical time polynomial of a realizer. -/
  timeOf : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    Q.Realizer a b f → Polynomial ℕ
  /-- Cost at an input is bounded by the canonical polynomial at the input size. -/
  cost_le : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.Realizer a b f)
    (x : A), Q.cost r x ≤ (timeOf r).eval (Q.size a x)
  /-- Output-size envelope as a function of the canonical polynomial. -/
  envelope : Polynomial ℕ → Polynomial ℕ
  /-- Output sizes are bounded by the envelope of the canonical polynomial. -/
  size_le : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.Realizer a b f)
    (x : A), Q.size b (f x) ≤ (envelope (timeOf r)).eval (Q.size a x)
  /-- The envelope respects shifted uniform domination. -/
  envelope_le : ∀ {p P : Polynomial ℕ} (n : ℕ), (∀ k, p.eval k ≤ P.eval (n + k)) →
    ∀ k, (envelope p).eval k ≤ (envelope P).eval (n + k)
  /-- Composition overhead as a function of the two canonical polynomials. -/
  overhead : Polynomial ℕ → Polynomial ℕ → Polynomial ℕ
  /-- The overhead respects shifted uniform domination in both arguments. -/
  overhead_le : ∀ {p P q Q' : Polynomial ℕ} (n : ℕ), (∀ k, p.eval k ≤ P.eval (n + k)) →
    (∀ k, q.eval k ≤ Q'.eval (n + k)) →
    ∀ k, (overhead p q).eval k ≤ (overhead P Q').eval (n + k)
  /-- The canonical polynomial of a composite is bounded by the first component's, the second's
  at the first's envelope, and the overhead. -/
  timeOf_compose_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} (r : Q.Realizer a b f) (s : Q.Realizer b d g) (k : ℕ),
    (timeOf (Q.compose r s)).eval k ≤
      (timeOf r).eval k + (timeOf s).eval ((envelope (timeOf r)).eval k) +
        (overhead (timeOf r) (timeOf s)).eval k
  /-- Uniform canonical polynomial of identities. -/
  idTime : Polynomial ℕ
  /-- Identities respect the uniform identity polynomial. -/
  timeOf_identity_le : ∀ {A : Type u} (a : C.Str A) (k : ℕ),
    (timeOf (Q.identity a)).eval k ≤ idTime.eval k
namespace DescriptionMeasure

variable {Faithful : ∀ {B : Type u}, C.Str B → Prop} (M : Q.DescriptionMeasure Faithful)

/-- Uniform identity-description and subadditive composition-description bounds for a selected
measure. These laws are independent of running-time certificates. -/
structure DescriptionComposition [Q.HasComposition] where
  /-- Uniform description size of identities. -/
  idDesc : ℕ
  /-- Identities respect the uniform description bound. -/
  descSize_identity_le : ∀ {A : Type u} (a : C.Str A), M.descSize (Q.identity a) ≤ idDesc
  /-- Description size is subadditive under composition. -/
  descSize_compose_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} (r : Q.Realizer a b f) (s : Q.Realizer b d g),
    M.descSize (Q.compose r s) ≤ M.descSize r + M.descSize s

/-- A canonical polynomial time backend together with description bounds for identity and
composition. Families use both contracts; time-only consumers use `PolynomialTimeBackend`. -/
structure PolynomialBackend [Q.HasComposition]
    extends Q.PolynomialTimeBackend, M.DescriptionComposition

/-- A parameter-indexed family of realizers with a uniform polynomial time bound in `n + k` and
a uniform polynomial description bound in `n`. -/
structure FamRealizer [Q.HasComposition] (PB : M.PolynomialBackend) {D E : ℕ → Type u}
    (a : ∀ n, C.Str (D n)) (b : ∀ n, C.Str (E n)) (f : ∀ n, D n → E n) where
  /-- The realizer at each parameter. -/
  wit : ∀ n, Q.Realizer (a n) (b n) (f n)
  /-- Uniform time bound, in `n + k`. -/
  time : Polynomial ℕ
  /-- Every per-parameter canonical polynomial is dominated by the uniform bound. -/
  time_le : ∀ n k, (PB.timeOf (wit n)).eval k ≤ time.eval (n + k)
  /-- Uniform description-size bound, in `n` (the advice bound). -/
  desc : Polynomial ℕ
  /-- Every per-parameter description is within the advice bound. -/
  desc_le : ∀ n, M.descSize (wit n) ≤ desc.eval n

namespace FamRealizer

variable {M} [Q.HasComposition] {PB : M.PolynomialBackend} {D E F : ℕ → Type u}
  {a : ∀ n, C.Str (D n)} {b : ∀ n, C.Str (E n)} {c : ∀ n, C.Str (F n)}
  {f : ∀ n, D n → E n} {g : ∀ n, E n → F n}

/-- Every member's cost is uniformly polynomially bounded in `n + input size`. -/
theorem cost_le (X : M.FamRealizer PB a b f) (n : ℕ) (x : D n) :
    Q.cost (X.wit n) x ≤ X.time.eval (n + Q.size (a n) x) :=
  (PB.cost_le _ x).trans (X.time_le n _)

/-- A family's advice bound is a description bound at every parameter: this is what makes the
uniform-family layer and the `RealizableLE` counting layer talk about the same functions. -/
theorem mem_realizableLE (X : M.FamRealizer PB a b f) (n : ℕ) :
    f n ∈ M.RealizableLE (a n) (b n) (X.desc.eval n) :=
  M.mem_realizableLE.mpr ⟨X.wit n, X.desc_le n⟩

/-- Enlarge the time and description certificates without changing any family member. -/
@[expose] def weaken (X : M.FamRealizer PB a b f) (time desc : Polynomial ℕ)
    (htime : ∀ k, X.time.eval k ≤ time.eval k)
    (hdesc : ∀ n, X.desc.eval n ≤ desc.eval n) : M.FamRealizer PB a b f where
  wit := X.wit
  time := time
  time_le n k := (X.time_le n k).trans (htime (n + k))
  desc := desc
  desc_le n := (X.desc_le n).trans (hdesc n)

@[simp] theorem wit_weaken (X : M.FamRealizer PB a b f) (time desc : Polynomial ℕ)
    (htime : ∀ k, X.time.eval k ≤ time.eval k)
    (hdesc : ∀ n, X.desc.eval n ≤ desc.eval n) (n : ℕ) :
    (X.weaken time desc htime hdesc).wit n = X.wit n := rfl

/-- The identity family. Exposed so that its projection laws hold by reflexivity downstream. -/
@[expose] noncomputable def id (PB : M.PolynomialBackend) (a : ∀ n, C.Str (D n)) :
    M.FamRealizer PB a a (fun _ ↦ _root_.id) where
  wit n := Q.identity (a n)
  time := PB.idTime
  time_le n k :=
    (PB.timeOf_identity_le (a n) k).trans (Polynomial.eval_le_eval (Nat.le_add_left k n))
  desc := .C PB.idDesc
  desc_le n := by simpa using PB.descSize_identity_le (a n)

@[simp] theorem wit_id (PB : M.PolynomialBackend) (a : ∀ n, C.Str (D n)) (n : ℕ) :
    (id PB a).wit n = Q.identity (a n) :=
  rfl

@[simp] theorem time_id (PB : M.PolynomialBackend) (a : ∀ n, C.Str (D n)) :
    (id PB a).time = PB.idTime :=
  rfl

@[simp] theorem desc_id (PB : M.PolynomialBackend) (a : ∀ n, C.Str (D n)) :
    (id PB a).desc = .C PB.idDesc :=
  rfl

/-- Sequential composition of families: composition at each parameter, the uniform time bound by
substitution through the envelope (the parameter is folded into the envelope's argument), and an
additive description bound. Exposed so that its projection laws hold by reflexivity downstream. -/
@[expose] noncomputable def comp (X : M.FamRealizer PB a b f) (Y : M.FamRealizer PB b c g) :
    M.FamRealizer PB a c (fun n ↦ g n ∘ f n) where
  wit n := Q.compose (X.wit n) (Y.wit n)
  time := X.time + Y.time.comp (Polynomial.X + PB.envelope X.time) + PB.overhead X.time Y.time
  time_le n k := by
    have h := PB.timeOf_compose_le (X.wit n) (Y.wit n) k
    have hx := X.time_le n k
    have henv := PB.envelope_le n (X.time_le n) k
    have hy : (PB.timeOf (Y.wit n)).eval ((PB.envelope (PB.timeOf (X.wit n))).eval k) ≤
        Y.time.eval (n + k + (PB.envelope X.time).eval (n + k)) :=
      (Y.time_le n _).trans (Polynomial.eval_le_eval (by omega))
    have hov := PB.overhead_le n (X.time_le n) (Y.time_le n) k
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X]
    omega
  desc := X.desc + Y.desc
  desc_le n := by
    have h := PB.descSize_compose_le (X.wit n) (Y.wit n)
    have := X.desc_le n
    have := Y.desc_le n
    simp only [Polynomial.eval_add]
    omega

@[simp] theorem wit_comp (X : M.FamRealizer PB a b f) (Y : M.FamRealizer PB b c g) (n : ℕ) :
    (X.comp Y).wit n = Q.compose (X.wit n) (Y.wit n) :=
  rfl

@[simp] theorem time_comp (X : M.FamRealizer PB a b f) (Y : M.FamRealizer PB b c g) :
    (X.comp Y).time =
      X.time + Y.time.comp (Polynomial.X + PB.envelope X.time) + PB.overhead X.time Y.time :=
  rfl

@[simp] theorem desc_comp (X : M.FamRealizer PB a b f) (Y : M.FamRealizer PB b c g) :
    (X.comp Y).desc = X.desc + Y.desc :=
  rfl

end FamRealizer

/-- The finite-table (advice) primitive: any function out of a finite domain with a faithful
input representation has a realizer with linear canonical time and a table-sized description. -/
structure FiniteTables [Q.HasComposition] (PB : M.PolynomialBackend)
    (FaithfulIn : ∀ {A : Type u}, C.Str A → Prop) where
  /-- The table realizer. -/
  table : ∀ {A B : Type u} [Fintype A] (a : C.Str A), FaithfulIn a →
    ∀ (b : C.Str B) (f : A → B), Q.Realizer a b f
  /-- Description size of a table, from a cardinality bound and pointwise size bounds. -/
  descSize_table_le : ∀ {A B : Type u} [Fintype A] (a : C.Str A) (ha : FaithfulIn a)
    (b : C.Str B) (f : A → B) {K La Lb : ℕ}, Fintype.card A ≤ K → (∀ x, Q.size a x ≤ La) →
    (∀ x, Q.size b (f x) ≤ Lb) → M.descSize (table a ha b f) ≤ K * (La + 1 + Lb) + 1
  /-- Canonical time of a table lookup, from a pointwise output-size bound. -/
  time_table_le : ∀ {A B : Type u} [Fintype A] (a : C.Str A) (ha : FaithfulIn a)
    (b : C.Str B) (f : A → B) {Lb : ℕ}, (∀ x, Q.size b (f x) ≤ Lb) →
    ∀ k, (PB.timeOf (table a ha b f)).eval k ≤ k + Lb + 1

namespace FamRealizer

variable {M} [Q.HasComposition] {PB : M.PolynomialBackend}
  {FaithfulIn : ∀ {A : Type u}, C.Str A → Prop}

/-- The finite-table family, for input families of polynomially bounded cardinality and size.
Exposed so that its projection law holds by reflexivity downstream. -/
@[expose] noncomputable def ofFintype (T : M.FiniteTables PB FaithfulIn) {D E : ℕ → Type u}
    [∀ n, Fintype (D n)]
    (a : ∀ n, C.Str (D n)) (ha : ∀ n, FaithfulIn (a n)) (b : ∀ n, C.Str (E n))
    (f : ∀ n, D n → E n)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Fintype.card (D n) ≤ cardIn.eval n)
    (lenIn : Polynomial ℕ) (hlenIn : ∀ n x, Q.size (a n) x ≤ lenIn.eval n)
    (lenOut : Polynomial ℕ) (hlenOut : ∀ n x, Q.size (b n) (f n x) ≤ lenOut.eval n) :
    M.FamRealizer PB a b f where
  wit n := T.table (a n) (ha n) (b n) (f n)
  time := Polynomial.X + lenOut + .C 1
  time_le n k := by
    have h := T.time_table_le (a n) (ha n) (b n) (f n) (hlenOut n) k
    have : lenOut.eval n ≤ lenOut.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  desc := cardIn * (lenIn + .C 1 + lenOut) + .C 1
  desc_le n := by
    refine (T.descSize_table_le (a n) (ha n) (b n) (f n) (hcard n) (hlenIn n)
      (hlenOut n)).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact le_rfl

@[simp] theorem wit_ofFintype (T : M.FiniteTables PB FaithfulIn) {D E : ℕ → Type u}
    [∀ n, Fintype (D n)]
    (a : ∀ n, C.Str (D n)) (ha : ∀ n, FaithfulIn (a n)) (b : ∀ n, C.Str (E n))
    (f : ∀ n, D n → E n)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Fintype.card (D n) ≤ cardIn.eval n)
    (lenIn : Polynomial ℕ) (hlenIn : ∀ n x, Q.size (a n) x ≤ lenIn.eval n)
    (lenOut : Polynomial ℕ) (hlenOut : ∀ n x, Q.size (b n) (f n x) ≤ lenOut.eval n) (n : ℕ) :
    (ofFintype T a ha b f cardIn hcard lenIn hlenIn lenOut hlenOut).wit n =
      T.table (a n) (ha n) (b n) (f n) :=
  rfl

end FamRealizer

/-- **No uniform realizer family for the diagonal predicate family.** The counting separation
says some Boolean predicate family has no eventual polynomial description bound; a `FamRealizer`
supplies such a bound at *every* parameter through `FamRealizer.mem_realizableLE`, so none can
exist. This is the form the separation takes for a consumer that works with families rather than
with `RealizableLE` directly. -/
theorem exists_not_famRealizer [Q.HasComposition] (PB : M.PolynomialBackend) {D E : ℕ → Type u}
    [∀ n, Fintype (D n)] (a : ∀ n, C.Str (D n)) (b : ∀ n, C.Str (E n))
    (ι : ∀ n, Bool → E n) (hι : ∀ n, Function.Injective (ι n)) (hb : ∀ n, Faithful (b n))
    (ht_count : ∀ᶠ n in atTop,
      Fintype.card (M.Desc (a n) (b n) (2 ^ (n / 4))) < 2 ^ Fintype.card (D n)) :
    ∃ f : (n : ℕ) → D n → Bool,
      IsEmpty (M.FamRealizer PB a b (fun n ↦ ι n ∘ f n)) := by
  obtain ⟨f, hf⟩ := M.exists_not_realizableLE_poly_of_card_lt a b ι hι hb ht_count
  exact ⟨f, ⟨fun X ↦ hf ⟨X.desc, .of_forall fun n ↦ X.mem_realizableLE n⟩⟩⟩

end DescriptionMeasure

end PFunctor.QuantitativeStepClass
