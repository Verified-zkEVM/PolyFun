/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/

module

public import ComplexityBackends.CslibSingleTape.BitEncoding
public import ToCslib.Algebra.PolynomialGrowth
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.FinEnum

/-!
# Counting Polynomial-Size Turing Machines

This module supplies the machine-theoretic half of the counting separation for the single-tape
backend: canonical `d`-state machines, state relabeling, determinism of runs, and the bound on how
many canonical machines exist at a threshold size. The generic half, description measures with a
finite cover, the diagonal argument, and the separation itself, lives in
`PolyFun.Realizability.Quantitative.Counting`; `ComplexityBackends.CslibSingleTape.Description`
instantiates it for this backend.

* **Canonical `d`-state machines** (`Cslib.Turing.SingleTapeTM.TMTable`): a transition table
  `Fin d → Option Bool → Stmt Bool × Option (Fin d)` together with an initial state.
  These are a `Fintype` with an explicit, provable cardinality
  (`card_tmTable`, bounded by `Cslib.Turing.SingleTapeTM.B`), and `reify` packages one back
  into a `SingleTapeTM Bool`. The `Fintype`/`DecidableEq` instances for the underlying
  `Turing.Dir` and `SingleTapeTM.Stmt Bool` are supplied here.
* **State normalization** (`exists_tmTable_of_card_le`): any
  `SingleTapeTM Bool` with at most `d` states computes the same string function as
  `reify` of some `TMTable d`.
* **Determinism** (`Outputs_unique`, `PolyTimeComputable.outputs`): a halting run's output is
  unique, and a polynomial-time witness outputs its function on every input.
* **Counting** (`card_bitVec_fun`, `B_le`, `eventually_count_lt`): there are `2 ^ (2 ^ n)`
  predicates on `BitVec n`, and the squared machine count at the threshold size `2 ^ (n / 4)`
  stays below it eventually. Polynomial growth against that threshold is
  `Polynomial.eventually_eval_le_two_pow_div_four` in `ToCslib.Algebra.PolynomialGrowth`.
-/

public section

open Filter Asymptotics

namespace Cslib.Turing.SingleTapeTM

/-! ## Finiteness of statements and directions -/

/-- A `SingleTapeTM.Stmt` is a pair of an optional write symbol and an optional move. -/
def stmtProdEquiv : SingleTapeTM.Stmt Bool ≃ (Option Bool × Option Turing.Dir) where
  toFun s := (s.symbol, s.movement)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeDirToCslib : Fintype Turing.Dir :=
  ⟨{Turing.Dir.left, Turing.Dir.right}, fun d => by cases d <;> decide⟩

instance instDecidableEqStmtBoolToCslib : DecidableEq (SingleTapeTM.Stmt Bool) :=
  fun _ _ => decidable_of_iff _ stmtProdEquiv.injective.eq_iff

noncomputable instance instFintypeStmtBoolToCslib : Fintype (SingleTapeTM.Stmt Bool) :=
  Fintype.ofEquiv _ stmtProdEquiv.symm

theorem card_dir : Fintype.card Turing.Dir = 2 := by decide

theorem card_stmt : Fintype.card (SingleTapeTM.Stmt Bool) = 9 := by
  rw [Fintype.card_congr stmtProdEquiv]; decide

/-! ## Canonical `d`-state machines -/

/-- A canonical `d`-state single-tape machine over `Bool`: a transition table on states
`Fin d` together with an initial state. Every machine with at most `d` states computes,
after relabeling, the same function as `reify` of one of these (`exists_tmTable_of_card_le`),
so `TMTable d` is the finite index of `d`-state machines used for counting. -/
abbrev TMTable (d : ℕ) : Type :=
  (Fin d → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin d)) × Fin d

noncomputable instance (d : ℕ) : Fintype (TMTable d) := inferInstance

instance (d : ℕ) : DecidableEq (TMTable d) := inferInstance

/-- The number of canonical `d`-state machines, in closed form. `card_tmTable` proves this
is the exact cardinality, not an over-count. -/
def B (d : ℕ) : ℕ := (9 * (d + 1)) ^ (3 * d) * d

/-- The exact number of canonical `d`-state machines: each of the `d` states maps each of
the `3` head symbols (`Option Bool`) to one of the `9 * (d + 1)` statement/next-state
pairs, and there are `d` choices of initial state. -/
theorem card_tmTable (d : ℕ) : Fintype.card (TMTable d) = B d := by
  simp only [B, TMTable, Fintype.card_prod, Fintype.card_fun, card_stmt,
    Fintype.card_option, Fintype.card_fin, Fintype.card_bool, ← pow_mul]

theorem card_tmTable_le (d : ℕ) : Fintype.card (TMTable d) ≤ B d :=
  (card_tmTable d).le

/-- Package a canonical table back into a `SingleTapeTM Bool` on state space `Fin d`. -/
def reify {d : ℕ} (t : TMTable d) : SingleTapeTM Bool where
  State := Fin d
  q₀ := t.2
  tr := t.1

/-! ## State-relabeling normalization construction

The machinery discharging `exists_tmTable_of_card_le`: relabel the finite state space of a
machine `tm` through `Fintype.equivFin`, embed `Fin (card tm.State)` into `Fin d` along the
cardinality inequality (`embFin`), and transport the transition function on the image
(`normTr`), sending every spare state (those outside the image, detected by `decFin`) to a
fixed halting transition. Configurations transport along `normCfg`, single steps correspond
(`step_normCfg`), and this lifts through `ReflTransGen` in both directions
(`normCfg_reflTransGen`, `reflTransGen_normCfg_reverse`), giving the `Outputs` equivalence. -/

section Normalize

/-- Embed a finite type into `Fin d` (with `card ≤ d`) via its `Fintype.equivFin` labeling. -/
noncomputable def embFin {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) (s : α) :
    Fin d :=
  (Fintype.equivFin α s).castLE hd

/-- The partial inverse of `embFin`: recover the state whose label is `i`, or `none` for
spare indices `i` with no preimage. -/
noncomputable def decFin {α : Type*} [Fintype α] {d : ℕ} (i : Fin d) : Option α :=
  if hi : (i : ℕ) < Fintype.card α then some ((Fintype.equivFin α).symm ⟨i, hi⟩) else none

/-- `decFin` inverts `embFin` on the image. -/
lemma decFin_embFin {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) (s : α) :
    (decFin (embFin hd s) : Option α) = some s := by
  have hlt : ((embFin hd s : Fin d) : ℕ) < Fintype.card α := by
    simp only [embFin, Fin.val_castLE]; exact (Fintype.equivFin α s).isLt
  simp only [decFin, dite_eq_left hlt]
  congr 1
  apply (Fintype.equivFin α).symm_apply_eq.mpr
  apply Fin.ext
  simp [embFin, Fin.val_castLE]

/-- `embFin` is injective. -/
lemma embFin_injective {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) :
    Function.Injective (embFin hd) := fun _ _ hab =>
  (Fintype.equivFin α).injective (Fin.castLE_injective hd hab)

variable {d : ℕ} (tm : SingleTapeTM Bool) (emb : tm.State → Fin d)
  (dec : Fin d → Option tm.State)

/-- Transition table transporting `tm`'s transitions along `emb`; spare states (those with
`dec i = none`) are given a fixed halting transition. -/
noncomputable def normTr : Fin d → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin d) :=
  fun i b =>
    match dec i with
    | some s => ((tm.tr s b).1, (tm.tr s b).2.map emb)
    | none => (default, none)

/-- The canonical `d`-state table normalizing `tm` onto `Fin d` along `emb`/`dec`. -/
noncomputable def normTable : TMTable d := (normTr tm emb dec, emb tm.q₀)

/-- Transport a configuration of `tm` to the reified normalized machine. -/
noncomputable def normCfg (c : tm.Cfg) : (reify (normTable tm emb dec)).Cfg :=
  ⟨c.state.map emb, c.BiTape⟩

variable {tm emb dec}

/-- The reified normalized machine's step transports `tm`'s step along `normCfg`, provided
`dec` inverts `emb` on the image. -/
lemma step_normCfg (hdec : ∀ s, dec (emb s) = some s) (c : tm.Cfg) :
    (reify (normTable tm emb dec)).step (normCfg tm emb dec c)
      = (tm.step c).map (normCfg tm emb dec) := by
  obtain ⟨st, tp⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hdq : dec (emb q) = some q := hdec q
    rcases htr : tm.tr q tp.head with ⟨⟨wr, dir⟩, q''⟩
    simp only [step, normCfg, reify, normTable, normTr, Option.map_some, hdq, htr]
    rfl

/-- `normCfg` is injective when `emb` is. -/
lemma normCfg_injective (hemb : Function.Injective emb) :
    Function.Injective (normCfg tm emb dec) := by
  rintro ⟨s1, t1⟩ ⟨s2, t2⟩ h
  simp only [normCfg, Cfg.mk.injEq] at h
  obtain ⟨hs, ht⟩ := h
  have hss : s1 = s2 := Option.map_injective hemb hs
  subst hss; subst ht; rfl

/-- A run of `tm` maps forward to a run of the normalized machine. -/
lemma normCfg_reflTransGen (hdec : ∀ s, dec (emb s) = some s) {c c' : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation c c') :
    Relation.ReflTransGen (reify (normTable tm emb dec)).TransitionRelation
      (normCfg tm emb dec c) (normCfg tm emb dec c') := by
  have hstep : ∀ a b, tm.TransitionRelation a b →
      (reify (normTable tm emb dec)).TransitionRelation
        (normCfg tm emb dec a) (normCfg tm emb dec b) := by
    intro a b hab
    have hs := step_normCfg hdec a
    rw [show tm.step a = some b from hab, Option.map_some] at hs
    exact hs
  exact Relation.ReflTransGen.lift (normCfg tm emb dec) hstep c c' h

/-- A run of the normalized machine from an image configuration stays in the image and maps
back to a run of `tm`. -/
lemma reflTransGen_normCfg_reverse (hdec : ∀ s, dec (emb s) = some s) {c : tm.Cfg}
    {c' : (reify (normTable tm emb dec)).Cfg}
    (h : Relation.ReflTransGen (reify (normTable tm emb dec)).TransitionRelation
      (normCfg tm emb dec c) c') :
    ∃ c₂, c' = normCfg tm emb dec c₂ ∧ Relation.ReflTransGen tm.TransitionRelation c c₂ := by
  induction h with
  | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
  | @tail b e hab hbc ih =>
    obtain ⟨c₂, rfl, hrun⟩ := ih
    have hs := step_normCfg hdec c₂
    rw [show (reify (normTable tm emb dec)).step (normCfg tm emb dec c₂) = some e from hbc] at hs
    obtain ⟨c₃, hstep, hc3⟩ := Option.map_eq_some_iff.mp hs.symm
    exact ⟨c₃, hc3.symm, hrun.tail hstep⟩

end Normalize

/-! ## Determinism of machine runs

Supporting facts for `exists_realizableLE_covering`: a single-tape machine
is deterministic (its `step` is a function), so the output list of a halting run is
unique. This lets the covering predicate attached to a table pair be read off by an
unbounded-search-free choice construction and still agree with any witness predicate. -/

section Determinism

/-- In a relation that is a partial function (deterministic), two irreducible points
reachable from a common source coincide. -/
theorem _root_.Relation.ReflTransGen.unique_of_deterministic
    {α : Type*} {R : α → α → Prop}
    (hdet : ∀ {a b c : α}, R a b → R a c → b = c)
    {a b c : α} (hb : Relation.ReflTransGen R a b) (hc : Relation.ReflTransGen R a c)
    (hbf : ∀ y, ¬ R b y) (hcf : ∀ y, ¬ R c y) : b = c := by
  induction hb using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rcases hc.cases_head with h | ⟨y, hy, _⟩
      · exact h
      · exact absurd hy (hbf y)
  | head h' _ ih =>
      rename_i a' _
      rcases hc.cases_head with h | ⟨y, hy, hyc⟩
      · exact absurd (h ▸ h') (hcf a')
      · rw [hdet h' hy] at ih; exact ih hyc

/-- Distinct input lists give distinct initial/halting tapes: `BiTape.mk₁` is injective. -/
theorem _root_.Cslib.Turing.BiTape.mk₁_injective {Symbol : Type} :
    Function.Injective (Cslib.Turing.BiTape.mk₁ : List Symbol → Cslib.Turing.BiTape Symbol) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t => simp [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.nil] at h
  | cons a s =>
    cases l₂ with
    | nil => simp [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.nil] at h
    | cons b t =>
      simp only [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.mk.injEq, Option.some.injEq] at h
      obtain ⟨hab, -, hst⟩ := h
      have : (s.map some) = (t.map some) := by
        have := congrArg Cslib.Turing.StackTape.toList hst
        simpa [Cslib.Turing.StackTape.mapSome] using this
      have hst' : s = t := List.map_injective_iff.mpr (Option.some_injective _) this
      rw [hab, hst']

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A halting configuration is irreducible: no transition leaves the halting state. -/
theorem not_transitionRelation_haltCfg (tm : SingleTapeTM Symbol) (l : List Symbol)
    (y : tm.Cfg) : ¬ tm.TransitionRelation (tm.haltCfg l) y := by
  intro hy
  simp only [TransitionRelation, haltCfg, step] at hy
  exact absurd hy (by simp)

/-- The output list of a halting machine run is unique: the machine is deterministic. -/
theorem Outputs_unique (tm : SingleTapeTM Symbol) {l l₁ l₂ : List Symbol}
    (h1 : tm.Outputs l l₁) (h2 : tm.Outputs l l₂) : l₁ = l₂ := by
  have hcfg : tm.haltCfg l₁ = tm.haltCfg l₂ := by
    refine Relation.ReflTransGen.unique_of_deterministic (R := tm.TransitionRelation)
      (fun {a b c} hab hac => ?_) h1 h2 (not_transitionRelation_haltCfg tm l₁)
      (not_transitionRelation_haltCfg tm l₂)
    rw [TransitionRelation] at hab hac
    rw [hab] at hac
    exact Option.some.inj hac
  have := congrArg Cfg.BiTape hcfg
  simp only [haltCfg] at this
  exact Cslib.Turing.BiTape.mk₁_injective this

/-- A polynomial-time machine halts with the correct output on every input. -/
theorem PolyTimeComputable.outputs {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) (a : List Symbol) : h.tm.Outputs a (f a) := by
  obtain ⟨m, _, hm⟩ := h.outputsFunInTime a
  exact hm.reflTransGen

end Determinism

/-! ## State normalization -/

/-- Every `SingleTapeTM Bool` with at most `d` states has the same `Outputs` relation as
`reify` of some `TMTable d` — the state space is relabeled to `Fin d` along
`Fintype.equivFin`. It is the machine-theoretic input to
`exists_realizableLE_covering`. -/
theorem exists_tmTable_of_card_le (tm : SingleTapeTM Bool)
    {d : ℕ} (hd : Fintype.card tm.State ≤ d) :
    ∃ t : TMTable d, ∀ l l', (reify t).Outputs l l' ↔ tm.Outputs l l' := by
  refine ⟨normTable tm (embFin hd) (decFin (α := tm.State)), fun l l' => ?_⟩
  have hdec : ∀ s, decFin (α := tm.State) (embFin hd s) = some s := decFin_embFin hd
  have hemb : Function.Injective (embFin (α := tm.State) hd) := embFin_injective hd
  have hinit : normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.initCfg l)
      = (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).initCfg l := rfl
  have hhalt : normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.haltCfg l')
      = (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).haltCfg l' := rfl
  constructor
  · intro hout
    have hout' : Relation.ReflTransGen
        (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).TransitionRelation
        (normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.initCfg l))
        ((reify (normTable tm (embFin hd) (decFin (α := tm.State)))).haltCfg l') := by
      rw [hinit]; exact hout
    obtain ⟨c₂, hc₂, hrun⟩ := reflTransGen_normCfg_reverse hdec hout'
    rw [← hhalt] at hc₂
    have hcfg : tm.haltCfg l' = c₂ := normCfg_injective hemb hc₂
    rw [← hcfg] at hrun
    exact hrun
  · intro hout
    have hmap := normCfg_reflTransGen hdec hout
    rw [hinit, hhalt] at hmap
    exact hmap

end Cslib.Turing.SingleTapeTM

namespace ComplexityBackends.CslibSingleTape

open Cslib.Turing.SingleTapeTM

/-! ## Cardinality of the predicate space -/

/-- There are exactly `2 ^ (2 ^ n)` predicates `BitVec n → Bool`. -/
theorem card_bitVec_fun (n : ℕ) : Fintype.card (BitVec n → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_bool, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- A crude closed-form bound on the machine count: for `9 * (d + 1) ≤ 2 ^ d` and `d ≥ 1`,
`B d ≤ 2 ^ (4 * d ^ 2)`. Uses `9 * (d + 1) ≤ 2 ^ d` on the statement/next-state base and
`d ≤ 2 ^ d` on the initial-state factor. -/
theorem B_le (d : ℕ) (hd : 9 * (d + 1) ≤ 2 ^ d) (hd1 : 1 ≤ d) :
    B d ≤ 2 ^ (4 * d ^ 2) := by
  calc B d = (9 * (d + 1)) ^ (3 * d) * d := by rw [B]
    _ ≤ (2 ^ d) ^ (3 * d) * 2 ^ d :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.le_of_lt d.lt_two_pow_self)
    _ = 2 ^ (3 * d ^ 2) * 2 ^ d := by rw [← pow_mul]; ring_nf
    _ = 2 ^ (3 * d ^ 2 + d) := by rw [← pow_add]
    _ ≤ 2 ^ (4 * d ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hd1])

/-- **The machine count at the threshold size `2 ^ (n / 4)` stays below the predicate count
`2 ^ (2 ^ n)` eventually.** The count at size `d = 2 ^ (n / 4)` is at most `2 ^ (4 * d ^ 2)`
(`B_le`, whose hypothesis `9 * (d + 1) ≤ 2 ^ d` holds cofinitely as `d → ∞`), and its
exponent `4 * d ^ 2 = 2 ^ (2 + n / 4 * 2)` is eventually below `2 ^ n`. -/
theorem eventually_count_lt :
    ∀ᶠ n in atTop, B (2 ^ (n / 4)) < 2 ^ (2 ^ n) := by
  have htwo : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self).le) tendsto_id
  have htend : Tendsto (fun n : ℕ => 2 ^ (n / 4)) atTop atTop :=
    htwo.comp (Nat.tendsto_div_const_atTop (by norm_num))
  filter_upwards [htend.eventually (Nat.eventually_const_mul_pow_le_two_pow 9 1),
    eventually_ge_atTop 8] with n ha hn
  rw [pow_one] at ha
  refine lt_of_le_of_lt (B_le _ ha Nat.one_le_two_pow) ?_
  apply Nat.pow_lt_pow_right (by norm_num)
  calc 4 * (2 ^ (n / 4)) ^ 2
      = 2 ^ (2 + n / 4 * 2) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
    _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)

end ComplexityBackends.CslibSingleTape
