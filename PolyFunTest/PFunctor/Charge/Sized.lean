/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import PolyFun.PFunctor.Free.Cost.Sized.Growth

/-!
# Size-indexed cost contracts

Checks for `PolyFun.PFunctor.Free.Cost.Sized` and `PolyFun.PFunctor.Free.Cost.Sized.Growth`:

* A Horner evaluation makes one call per coefficient, so it meets the envelope `n` in the number
  of coefficients, a polynomial, also counted per kind in `Fin 2 → ℕ`.
* An exhaustive search over `2 ^ n` candidates makes one call per candidate. It has no polynomial
  envelope, but with its sizes capped at `N` it meets the fixed budget `2 ^ N`, and so a constant
  polynomial. Under the cap, it still does not meet a named envelope such as `(n + 1) ^ 2`.
* The same search done in the uncharged view meets the zero envelope.
* A program that returns the answer of its call has no output-size envelope over every answer.
  Over the answers of its answering function, it returns `0`, also after composition.
* A countdown that makes `n` calls on input `n` runs after a call that returns its answer. Both
  parts have polynomial cost, and the composite does not, over every answer. So `PolyCost.comp`
  needs its output hypothesis. Over the answers of the answering functions, the composite costs
  `1`, and `PolyCostUnder.comp` gives its polynomial cost.
* Over the answers of the answering functions, a search that rejects every candidate, and a
  countdown after a call answered with `2 ^ n`, have no polynomial cost. So `PolyCostUnder.comp`
  also needs its output hypothesis.
* Polynomial contracts chain through three list doublings.
* Every function whose input type lies in the universe of its result type has a measured program
  with polynomial cost under every size measure (`ofFun`). So the existential statement is no
  evidence of efficiency.
-/

public section

open PFunctor PFunctor.FreeM PFunctor.FreeM.MeasuredProgram Cslib

namespace PolyFunTest.ChargeSized

/-! ## Horner evaluation: one call per coefficient -/

/-- Fold the coefficients, one multiply-add call `(acc, c) ↦ acc * x + c` each. -/
def horner : List ℕ → ℕ → FreeM ⟨ℕ × ℕ, fun _ => ℕ⟩ ℕ
  | [], acc => pure acc
  | c :: cs, acc => FreeM.liftBind (acc, c) fun acc' => horner cs acc'

/-- Horner evaluation of a coefficient list at a point. -/
def hornerProgram : MeasuredProgram (List ℕ × ℕ) ℕ ℕ where
  View := List ℕ × ℕ
  view := id
  Op := ℕ × ℕ
  spec _ _ := ℕ
  program v := horner v.1 0
  answer v o := o.1 * v.2 + o.2
  cost _ := 1

theorem charge_horner (cs : List ℕ) (acc : ℕ) (p : Path (horner cs acc)) :
    Path.charge (fun _ => 1) (horner cs acc) p = cs.length := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    rcases p with ⟨b, p⟩
    change 1 + Path.charge _ (horner cs b) p = _
    rw [ih, List.length_cons, Nat.add_comm]

theorem output_horner (x : ℕ) (cs : List ℕ) (acc : ℕ) :
    output (horner cs acc) (Path.ofHandler (fun o : ℕ × ℕ => o.1 * x + o.2) _) =
      cs.foldl (fun acc c => acc * x + c) acc := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem hornerProgram_realizes :
    hornerProgram.Realizes fun i => i.1.foldl (fun acc c => acc * i.2 + c) 0 := fun i => by
  rw [run_eq_output]
  exact (output_horner i.2 i.1 0).symm

/-- One call per coefficient: the envelope is the identity in the number of coefficients. -/
theorem hornerProgram_costWithin : hornerProgram.CostWithin (fun i => i.1.length) id :=
  fun i p => (charge_horner i.1 0 p).le

theorem hornerProgram_polyCost : hornerProgram.PolyCost fun i => i.1.length :=
  polyCost_iff.2 ⟨id, ⟨1, .of_forall fun n => (pow_one n).ge⟩, hornerProgram_costWithin⟩

/-! ## Exhaustive search: one call per candidate -/

/-- Test the candidates in turn and return the first accepted one. -/
def firstAccepted : List ℕ → FreeM ⟨ℕ, fun _ => Bool⟩ (Option ℕ)
  | [] => pure none
  | a :: as => FreeM.liftBind a fun b => bif b then pure (some a) else firstAccepted as

theorem charge_firstAccepted_le (l : List ℕ) (p : Path (firstAccepted l)) :
    Path.charge (fun _ => 1) (firstAccepted l) p ≤ l.length := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    rcases p with ⟨b, p⟩
    cases b
    · exact (Nat.add_comm _ _).trans_le (Nat.add_le_add_right (ih p) 1)
    · exact Nat.le_add_left _ _

/-- The path rejecting every candidate tests all of them. -/
theorem exists_charge_firstAccepted_eq (l : List ℕ) :
    ∃ p : Path (firstAccepted l), Path.charge (fun _ => 1) (firstAccepted l) p = l.length := by
  induction l with
  | nil => exact ⟨⟨⟩, rfl⟩
  | cons a as ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨⟨false, p⟩, ?_⟩
    change 1 + Path.charge _ (firstAccepted as) p = _
    rw [hp, List.length_cons, Nat.add_comm]

theorem output_firstAccepted (accept : ℕ → Bool) (l : List ℕ) :
    output (firstAccepted l) (Path.ofHandler accept _) = l.find? accept := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    change output (bif accept a then pure (some a) else firstAccepted as) (Path.ofHandler accept _)
      = _
    rw [List.find?_cons]
    cases accept a
    · exact ih
    · rfl

/-- Search the `2 ^ len v` candidates of a view, one call per candidate. -/
def searchOn (V : Type) (len : V → ℕ) (accept : V → ℕ → Bool) : MeasuredProgram V (Option ℕ) ℕ where
  View := V
  view := id
  Op := ℕ
  spec _ _ := Bool
  program v := firstAccepted (List.range (2 ^ len v))
  answer := accept
  cost _ := 1

theorem searchOn_realizes (V : Type) (len : V → ℕ) (accept : V → ℕ → Bool) :
    (searchOn V len accept).Realizes fun v => (List.range (2 ^ len v)).find? (accept v) :=
  fun v => by
    rw [run_eq_output]
    exact (output_firstAccepted (accept v) _).symm

/-- The search over all sizes. -/
abbrev search (accept : ℕ → ℕ → Bool) : MeasuredProgram ℕ (Option ℕ) ℕ :=
  searchOn ℕ id accept

/-- The search over sizes at most `N`. -/
abbrev cappedSearch (N : ℕ) (accept : ℕ → ℕ → Bool) :
    MeasuredProgram {n : ℕ // n ≤ N} (Option ℕ) ℕ :=
  searchOn {n : ℕ // n ≤ N} Subtype.val fun v => accept v.1

/-- **Capped sizes make a fixed budget available.** -/
theorem cappedSearch_costAtMost (N : ℕ) (accept : ℕ → ℕ → Bool) :
    (cappedSearch N accept).CostAtMost (2 ^ N) := fun v p =>
  (charge_firstAccepted_le _ p).trans <| by
    rw [List.length_range]
    exact Nat.pow_le_pow_right (by norm_num) v.2

/-- So the polynomial contract holds too, with a constant polynomial. -/
example (N : ℕ) (accept : ℕ → ℕ → Bool) :
    (cappedSearch N accept).PolyCost Subtype.val :=
  .of_costAtMost (cappedSearch_costAtMost N accept) _

/-- **The negative control.** Over all sizes, no polynomial envelope holds. -/
theorem search_not_polyCost (accept : ℕ → ℕ → Bool) : ¬ (search accept).PolyCost id := fun h =>
  not_polynomiallyBounded_two_pow <| h.polynomiallyBounded_of_le_charge fun n => by
    obtain ⟨p, hp⟩ := exists_charge_firstAccepted_eq (List.range (2 ^ n))
    exact ⟨n, le_rfl, p, (List.length_range ..).symm.trans hp.symm |>.le⟩

/-- **A named envelope is informative under the cap.** At size `6`, the search makes `64` calls
on its rejecting path, more than `(6 + 1) ^ 2`. -/
theorem cappedSearch_not_costWithin_sq (N : ℕ) (hN : 6 ≤ N) (accept : ℕ → ℕ → Bool) :
    ¬ (cappedSearch N accept).CostWithin Subtype.val fun n => (n + 1) ^ 2 := fun h => by
  obtain ⟨p, hp⟩ := exists_charge_firstAccepted_eq (List.range (2 ^ 6))
  have := hp.symm.trans_le (h ⟨6, hN⟩ p)
  rw [List.length_range] at this
  norm_num at this

/-! ## Per input, not per view -/

/-- Restricting the inputs of the full search keeps its views, so no uniform budget holds. -/
theorem search_contramap_not_costAtMost (N : ℕ) (accept : ℕ → ℕ → Bool) :
    ¬ ((search accept).contramap (Subtype.val : {n : ℕ // n ≤ N} → ℕ)).CostAtMost (2 ^ N) :=
  fun h => by
    obtain ⟨p, hp⟩ := exists_charge_firstAccepted_eq (List.range (2 ^ (N + 1)))
    have := hp.symm.trans_le (h (N + 1) p)
    rw [List.length_range, Nat.pow_le_pow_iff_right (by norm_num)] at this
    omega

/-- The per-input contract sees the restriction. -/
example (N : ℕ) (accept : ℕ → ℕ → Bool) :
    ((search accept).contramap (Subtype.val : {n : ℕ // n ≤ N} → ℕ)).CostWithin Subtype.val
      fun _ => 2 ^ N := fun i p =>
  (charge_firstAccepted_le _ p).trans <| by
    rw [List.length_range]
    exact Nat.pow_le_pow_right (by norm_num) i.2

/-! ## Families -/

/-- The search family indexed by a parameter, with the parameter as the size. -/
abbrev searchFamily (accept : ℕ → ℕ → Bool) (κ : ℕ) : MeasuredProgram Unit (Option ℕ) ℕ :=
  searchOn Unit (fun _ => κ) fun _ => accept κ

/-- Over finitely many parameters, the family has polynomial cost. -/
example (accept : ℕ → ℕ → Bool) :
    FamilyPolyCost (fun κ : Fin 29 => searchFamily accept κ) fun κ _ => κ :=
  .of_finite (B := fun κ : Fin 29 => 2 ^ (κ : ℕ)) (fun _ _ p =>
    (charge_firstAccepted_le _ p).trans (List.length_range ..).le) _

/-- Over all parameters, it does not. -/
example (accept : ℕ → ℕ → Bool) :
    ¬ FamilyPolyCost (searchFamily accept) fun κ _ => κ := fun h =>
  not_polynomiallyBounded_two_pow <| h.polynomiallyBounded_of_le_charge fun n => by
    obtain ⟨p, hp⟩ := exists_charge_firstAccepted_eq (List.range (2 ^ n))
    exact ⟨n, (), le_rfl, p, (List.length_range ..).symm.trans hp.symm |>.le⟩

/-! ## The uncharged view -/

/-- The same search, done in the uncharged view. -/
def viewSearch (accept : ℕ → ℕ → Bool) : MeasuredProgram ℕ (Option ℕ) ℕ :=
  MeasuredProgram.ofFun fun n => (List.range (2 ^ n)).find? (accept n)

/-- It computes what `search` computes, within the zero envelope: the sized contract bounds the
calls of a named program, not the work of its view. -/
example (accept : ℕ → ℕ → Bool) :
    (viewSearch accept).Realizes (fun n => (List.range (2 ^ n)).find? (accept n)) ∧
      (search accept).Realizes (fun n => (List.range (2 ^ n)).find? (accept n)) ∧
      (viewSearch accept).CostWithin id (fun _ => 0) ∧ (viewSearch accept).PolyCost id ∧
      ¬ (search accept).PolyCost id :=
  ⟨realizes_ofFun _, searchOn_realizes ℕ id accept, costWithin_ofFun _ _,
    .of_costAtMost (costAtMost_ofFun _) _, search_not_polyCost accept⟩

/-! ## Per-kind counts -/

/-- Count each Horner step as one multiplication and one addition. -/
def perKind : ℕ →+ (Fin 2 → ℕ) :=
  AddMonoidHom.pi fun _ => AddMonoidHom.id ℕ

/-- Horner evaluation priced in `Fin 2 → ℕ`, one count per kind. -/
abbrev hornerByKind : MeasuredProgram (List ℕ × ℕ) ℕ (Fin 2 → ℕ) :=
  hornerProgram.mapCost perKind

theorem hornerByKind_costWithin :
    hornerByKind.CostWithin (fun i => i.1.length) (perKind ∘ id) :=
  hornerProgram_costWithin.mapCost perKind fun _ _ h _ => h

/-- The multiplications alone have polynomial cost. -/
example : (hornerByKind.mapCost fun c => c 0).PolyCost fun i => i.1.length :=
  ⟨Polynomial.X, (costWithin_pi_iff.1 hornerByKind_costWithin 0).mono fun _ => by
    simp [perKind]⟩

/-- The two counts together stay within the sum of the per-kind envelopes. -/
example : (hornerByKind.mapCost fun c => ∑ k, c k).CostWithin (fun i => i.1.length)
    fun n => ∑ _k : Fin 2, n :=
  costWithin_finsetSum Finset.univ fun k _ => costWithin_pi_iff.1 hornerByKind_costWithin k

/-! ## Allowed answers -/

/-- Return the answer of one call. -/
def echo : MeasuredProgram Unit ℕ ℕ where
  View := Unit
  view := id
  Op := Unit
  spec _ _ := ℕ
  program _ := FreeM.liftBind () fun n => pure n
  answer _ _ := 0
  cost _ := 1

/-- Over every answer, the result has no size envelope. -/
example (e : ℕ → ℕ) : ¬ echo.OutputWithin (fun _ => 0) id e := fun h => by
  have := h () ⟨e 0 + 1, ⟨⟩⟩
  change e 0 + 1 ≤ e 0 at this
  omega

/-- Over the answers of `answer`, the result is `0`. -/
theorem echo_outputWithinUnder :
    echo.OutputWithinUnder echo.Answered (fun _ => 0) id fun _ => 0 := by
  rintro _ ⟨⟨b, hb⟩, ⟨⟩⟩
  exact Nat.le_of_eq hb

/-- The restricted output contract is a bound on the run. -/
example : echo.OutputWithinUnder echo.Answered (fun _ => 0) id fun _ => 0 :=
  outputWithinUnder_answered_iff.2 fun _ => le_rfl

/-- The restricted cost contract is a bound on the charge of the run's path. -/
example : echo.CostWithinUnder echo.Answered (fun _ => 0) fun _ => 1 :=
  costWithinUnder_answered_iff.2 fun _ => le_rfl

/-- A restriction that admits no answer leaves no completed path through a call, so the contract
holds at the envelope `0`. -/
example : echo.CostWithinUnder (fun _ _ _ => False) (fun _ => 0) fun _ => 0 := by
  rintro _ ⟨⟨_, h⟩, ⟨⟩⟩
  exact h.elim

/-- The echo of any input. -/
abbrev echoAfter : MeasuredProgram ℕ ℕ ℕ :=
  echo.contramap fun _ => ()

/-- Composed over the answers of the parts, which are the answers of the composite, it still
returns `0`. -/
example : (echoAfter.comp echo).OutputWithinUnder (echoAfter.comp echo).Answered (fun _ => 0) id
    ((fun _ => 0) ∘ fun _ => 0) := by
  rw [answered_comp]
  exact OutputWithinUnder.comp (fun _ => echo_outputWithinUnder ()) monotone_const
    echo_outputWithinUnder

/-! ## Composition over the run -/

/-- One call, returning its answer. The answering function answers `0`. -/
abbrev echoN : MeasuredProgram ℕ ℕ ℕ where
  View := ℕ
  view := id
  Op := Unit
  spec _ _ := ℕ
  program _ := FreeM.liftBind () fun n => pure n
  answer _ _ := 0
  cost _ := 1

/-- `n` calls. -/
def ticks : ℕ → FreeM ⟨Unit, fun _ => Unit⟩ Unit
  | 0 => pure ()
  | n + 1 => FreeM.liftBind () fun _ => ticks n

/-- `n` calls on input `n`. -/
abbrev countdown : MeasuredProgram ℕ Unit ℕ where
  View := ℕ
  view := id
  Op := Unit
  spec _ _ := Unit
  program v := ticks v
  answer _ _ := ()
  cost _ := 1

theorem charge_ticks (n : ℕ) (p : Path (ticks n)) :
    Path.charge (fun _ => 1) (ticks n) p = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b, p⟩
    change 1 + Path.charge _ (ticks n) p = _
    rw [ih, Nat.add_comm]

theorem countdown_polyCost : countdown.PolyCost id :=
  ⟨Polynomial.X, fun i p => by simp [countdown, charge_ticks i p]⟩

theorem echoN_polyCost : echoN.PolyCost id :=
  ⟨Polynomial.C 1, fun i ⟨b, ⟨⟩⟩ => by simp [echoN]; rfl⟩

/-- Over every answer, the inner program has no polynomial output bound. -/
theorem echoN_not_polyOutput : ¬ echoN.PolyOutput id id := by
  rintro ⟨q, hq⟩
  have := hq 0 ⟨q.eval 0 + 1, ⟨⟩⟩
  change q.eval 0 + 1 ≤ q.eval 0 at this
  omega

/-- Over every answer, the composite has no polynomial cost: the inner call can return any `n`,
and the outer program then makes `n` calls. -/
theorem comp_not_polyCost : ¬ (countdown.comp echoN).PolyCost id := by
  rintro ⟨q, hq⟩
  let N : ℕ := q.eval 0
  let choose : (a : (countdown.comp echoN).Op) → CompSpec countdown echoN (0 : ℕ) a
    | .inl _ => (N : ℕ)
    | .inr _ => ()
  have key : ∀ n (p : Path ((ticks n).mapLens (outerLens countdown echoN (0 : ℕ) n))),
      Path.charge (countdown.comp echoN).cost _ p = n := fun n p =>
    (Path.charge_pullMapLens (outerLens countdown echoN (0 : ℕ) n) (ticks n) p).trans
      (charge_ticks n _)
  have h := hq (0 : ℕ) (Path.ofHandler choose ((countdown.comp echoN).program (0 : ℕ)))
  have e : Path.charge (countdown.comp echoN).cost ((countdown.comp echoN).program (0 : ℕ))
      (Path.ofHandler choose ((countdown.comp echoN).program (0 : ℕ))) = 1 + N :=
    congrArg (1 + ·) (key N _)
  have : 1 + N ≤ N := e.symm.trans_le h
  omega

/-- **`PolyCost.comp` needs its output hypothesis.** Without it, polynomial-cost parts would give
a polynomial-cost composite. -/
example : ¬ ∀ (outer : MeasuredProgram ℕ Unit ℕ) (inner : MeasuredProgram ℕ ℕ ℕ),
    outer.PolyCost id → inner.PolyCost id → (outer.comp inner).PolyCost id := fun h =>
  comp_not_polyCost (h _ _ countdown_polyCost echoN_polyCost)

theorem countdown_costWithinUnder : countdown.CostWithinUnder countdown.Answered id id :=
  .of_costWithin (fun i p => (charge_ticks i p).le) _

theorem echoN_costWithinUnder : echoN.CostWithinUnder echoN.Answered id fun _ => 1 :=
  costWithinUnder_answered_iff.2 fun _ => le_rfl

theorem echoN_outputWithinUnder : echoN.OutputWithinUnder echoN.Answered id id fun _ => 0 :=
  outputWithinUnder_answered_iff.2 fun _ => le_rfl

/-- Over the answers of the answering functions, the composite costs `1`, by sized composition
along `CompAllows`. -/
theorem comp_costWithinUnder :
    (countdown.comp echoN).CostWithinUnder (countdown.comp echoN).Answered id fun _ => 1 := by
  rw [answered_comp]
  exact CostWithinUnder.comp countdown_costWithinUnder monotone_id echoN_costWithinUnder
    echoN_outputWithinUnder

/-- The same bound, read off the run. -/
example : (countdown.comp echoN).CostWithinUnder (countdown.comp echoN).Answered id fun _ => 1 :=
  costWithinUnder_answered_iff.2 fun _ => le_rfl

/-- Over the answers of the answering functions, the composite has polynomial cost. -/
theorem comp_polyCostUnder :
    (countdown.comp echoN).PolyCostUnder (countdown.comp echoN).Answered id := by
  rw [answered_comp]
  exact PolyCostUnder.comp (.of_polyCost countdown_polyCost _) (.of_polyCost echoN_polyCost _)
    ⟨0, echoN_outputWithinUnder.mono fun _ => Nat.zero_le _⟩

/-- The constant envelope `1` is an envelope of polynomial growth. -/
example : (countdown.comp echoN).PolyCostUnder (countdown.comp echoN).Answered id :=
  polyCostUnder_iff.2 ⟨fun _ => 1, (polynomiallyBounded_eval (Polynomial.C 1)).mono
    (.of_forall fun _ => by simp), comp_costWithinUnder⟩

/-- The restriction to every answer gives back the unrestricted contract, which fails. -/
example : ¬ (countdown.comp echoN).PolyCostUnder (fun _ _ _ => True) id := fun h =>
  comp_not_polyCost (polyCostUnder_true_iff.1 h)

/-- Admitting fewer answers keeps the contract. -/
example : (countdown.comp echoN).CostWithinUnder (fun _ _ _ => False) id fun _ => 1 :=
  comp_costWithinUnder.mono_allows fun _ _ _ h => h.elim

/-! ## Refuting contracts over allowed answers -/

theorem charge_ofHandler_firstAccepted_false (l : List ℕ) :
    Path.charge (fun _ => 1) (firstAccepted l) (Path.ofHandler (fun _ => false) _) = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    change 1 + Path.charge _ (firstAccepted as) (Path.ofHandler (fun _ => false) _) = _
    rw [ih, List.length_cons, Nat.add_comm]

/-- A search whose answering function rejects every candidate runs through all `2 ^ n` of them,
so it has no polynomial cost over the answers of its answering function. -/
theorem search_false_not_polyCostUnder :
    ¬ (search fun _ _ => false).PolyCostUnder (search fun _ _ => false).Answered id := fun h =>
  not_polynomiallyBounded_two_pow <| h.polynomiallyBounded_of_le_charge_answered fun n =>
    ⟨n, le_rfl, by
      change _ ≤ Path.charge (fun _ => 1) (firstAccepted _) (Path.ofHandler (fun _ => false) _)
      rw [charge_ofHandler_firstAccepted_false, List.length_range]
      rfl⟩

/-- One call, whose answering function answers `2 ^ n` on input `n`. -/
abbrev blowup : MeasuredProgram ℕ ℕ ℕ where
  View := ℕ
  view := id
  Op := Unit
  spec _ _ := ℕ
  program _ := FreeM.liftBind () fun n => pure n
  answer v _ := 2 ^ v
  cost _ := 1

theorem blowup_polyCost : blowup.PolyCost id :=
  ⟨Polynomial.C 1, fun i ⟨b, ⟨⟩⟩ => by simp [blowup]; rfl⟩

/-- After `blowup`, the countdown makes `2 ^ n` calls on the run, so the composite has no
polynomial cost over the answers of the answering functions. -/
theorem comp_blowup_not_polyCostUnder :
    ¬ (countdown.comp blowup).PolyCostUnder (countdown.comp blowup).Answered id := fun h =>
  not_polynomiallyBounded_two_pow <| h.polynomiallyBounded_of_le_charge_answered fun n => by
    have key : ∀ m (p : Path ((ticks m).mapLens (outerLens countdown blowup n m))),
        Path.charge (countdown.comp blowup).cost _ p = m := fun m p =>
      (Path.charge_pullMapLens (outerLens countdown blowup n m) (ticks m) p).trans
        (charge_ticks m _)
    have e : Path.charge (countdown.comp blowup).cost ((countdown.comp blowup).program n)
        (Path.ofHandler ((countdown.comp blowup).answer n) ((countdown.comp blowup).program n)) =
          1 + 2 ^ n :=
      congrArg (1 + ·) (key _ _)
    exact ⟨n, le_rfl, e ▸ Nat.le_add_left _ _⟩

/-- **`PolyCostUnder.comp` needs its output hypothesis, also over `Answered`.** -/
example : ¬ ∀ (outer : MeasuredProgram ℕ Unit ℕ) (inner : MeasuredProgram ℕ ℕ ℕ),
    outer.PolyCostUnder outer.Answered id → inner.PolyCostUnder inner.Answered id →
      (outer.comp inner).PolyCostUnder (outer.comp inner).Answered id := fun h =>
  comp_blowup_not_polyCostUnder
    (h _ _ (.of_polyCost countdown_polyCost _) (.of_polyCost blowup_polyCost _))

/-! ## Chaining polynomial contracts -/

/-- Copy each element, one call per element. -/
def dupLoop : List ℕ → List ℕ → FreeM ⟨ℕ, fun _ => ℕ⟩ (List ℕ)
  | [], acc => pure acc
  | a :: as, acc => FreeM.liftBind a fun b => dupLoop as (b :: a :: acc)

/-- Double a list, one call per element. -/
def dup : MeasuredProgram (List ℕ) (List ℕ) ℕ where
  View := List ℕ
  view := id
  Op := ℕ
  spec _ _ := ℕ
  program v := dupLoop v []
  answer _ a := a
  cost _ := 1

theorem dupLoop_path (as acc : List ℕ) (p : Path (dupLoop as acc)) :
    Path.charge (fun _ => 1) (dupLoop as acc) p = as.length ∧
      (output (dupLoop as acc) p).length = 2 * as.length + acc.length := by
  induction as generalizing acc with
  | nil => exact ⟨rfl, by simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]; rfl⟩
  | cons a as ih =>
    rcases p with ⟨b, p⟩
    obtain ⟨h₁, h₂⟩ := ih _ p
    refine ⟨?_, ?_⟩
    · change 1 + Path.charge _ (dupLoop as _) p = _
      rw [h₁, List.length_cons, Nat.add_comm]
    · change (output (dupLoop as _) p).length = _
      rw [h₂]
      simp only [List.length_cons]
      omega

theorem dup_polyCost : dup.PolyCost List.length :=
  ⟨Polynomial.X, fun i p => (dupLoop_path i [] p).1.trans_le (by simp)⟩

theorem dup_polyOutput : dup.PolyOutput List.length List.length :=
  ⟨2 * Polynomial.X, fun i p => (dupLoop_path i [] p).2.trans_le (by simp)⟩

/-- Three doublings: the contracts chain through the output-size envelopes. -/
example : (dup.comp (dup.comp dup)).PolyCost List.length :=
  dup_polyCost.comp (dup_polyCost.comp dup_polyCost dup_polyOutput)
    (dup_polyOutput.comp dup_polyOutput)

/-! ## Existential contracts -/

/-- Every function has a measured program with polynomial cost, within the zero envelope, under
every size measure: the existential statement is no evidence of efficiency. -/
example {Input Result : Type} (f : Input → Result) (size : Input → ℕ) :
    ∃ M : MeasuredProgram Input Result ℕ, M.Realizes f ∧ M.PolyCost size ∧
      M.CostWithin size fun _ => 0 :=
  ⟨ofFun f, realizes_ofFun f, .of_costAtMost (costAtMost_ofFun f) size, costWithin_ofFun f size⟩

end PolyFunTest.ChargeSized
