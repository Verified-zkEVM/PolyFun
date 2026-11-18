/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.MoveTranslation
public import Mathlib.Data.FinEnum
public import ToCslib.Order.Finpartition
import Mathlib.Data.Fintype.Card

/-!
# The fewest hints that translate every move

A partition of the states describes the information in a hint. Its blocks receive their names
as states are inserted, so renaming blocks never creates a second partition. The search checks
partitions in increasing order of block count and constructs a decoder on each successful block.
-/

public section

namespace PolyFunExamples.Bargaining.Replay

/-- A successful search supplies a hint and its decoder, together with the lower bound against
every competing alphabet. A failed search identifies one state and move with no translation. -/
inductive HintResult {T B C O : Type} (mode : Mode) (board : Board T B C O) where
  /-- A valid translation with a lower bound on the alphabet size of every translation. -/
  | optimal (k : Nat) (hint : T → Fin k) (decode : Fin k → B → C)
      (valid : Valid mode board hint decode)
      (minimal : ∀ j (h : T → Fin j) (d : Fin j → B → C), Valid mode board h d → k ≤ j)
  /-- A source move that has no compatible target move even when the state is known. -/
  | impossible (t : T) (b : B) (reject : ∀ c, ¬ Compatible mode board t b c)

/-- The optimum, when every move can be translated. -/
@[expose] def HintResult.size? {T B C O : Type} {mode : Mode} {board : Board T B C O} :
    HintResult mode board → Option Nat
  | .optimal k .. => some k
  | .impossible .. => none

variable {T B C O : Type}

/-- Certify the search result from a decoder and a matching lower bound on every decoder's
alphabet. The proof applies even when enumerating the board's partitions is impractical. -/
theorem HintResult.size?_of_bounds {mode : Mode} {board : Board T B C O}
    (result : HintResult mode board) {k : Nat} {h : T → Fin k} {d : Fin k → B → C}
    (valid : Valid mode board h d)
    (lower : ∀ j (h' : T → Fin j) (d' : Fin j → B → C), Valid mode board h' d' → k ≤ j) :
    result.size? = some k := by
  cases result with
  | optimal j h' d' valid' minimal =>
    exact congrArg some (Nat.le_antisymm (minimal k h d valid) (lower j h' d' valid'))
  | impossible t b reject => exact (reject _ (valid t b)).elim

/-- The optimum is absent exactly when one state and source move have no compatible target. -/
theorem HintResult.size?_eq_none_iff {mode : Mode} {board : Board T B C O}
    (result : HintResult mode board) :
    result.size? = none ↔ ∃ t b, ∀ c, ¬ Compatible mode board t b c := by
  cases result with
  | optimal k h d valid _ =>
    refine ⟨by simp [HintResult.size?], ?_⟩
    rintro ⟨t, b, reject⟩
    exact (reject _ (valid t b)).elim
  | impossible t b reject => exact ⟨fun _ => ⟨t, b, reject⟩, fun _ => rfl⟩

/-- When there are no hidden states, the empty alphabet supplies the optimal hint. -/
theorem HintResult.size?_of_isEmpty [IsEmpty T] {mode : Mode} {board : Board T B C O}
    (result : HintResult mode board) : result.size? = some 0 := by
  cases result with
  | optimal k h d hd minimal =>
    have hk := minimal 0 isEmptyElim (fun s => s.elim0) (fun t => isEmptyElim t)
    simp [HintResult.size?, Nat.eq_zero_of_le_zero hk]
  | impossible t => exact (isEmptyElim t : False).elim

namespace MinimumHint

/-- A decoder certified on the occupied blocks of its canonical partition. -/
structure Scheme [FinEnum T] (mode : Mode) (board : Board T B C O) (k : Nat) where
  /-- States in a common block send the same hint. -/
  part : Finpartition.Code (FinEnum.card T) k
  /-- Target move to use for each block and source move. -/
  decode : Fin k → B → C
  /-- The target move is compatible in every state that sends its block's hint. -/
  valid : Valid mode board (fun t => part.signal (FinEnum.equiv t)) decode

/-- A decoder using arbitrary hint names induces one on at most as many occupied blocks. -/
theorem factor_valid [FinEnum T] (mode : Mode) (board : Board T B C O)
    {j : Nat} (h : T → Fin j) (d : Fin j → B → C) (hd : Valid mode board h d) :
    ∃ k ≤ j, Nonempty (Scheme mode board k) := by
  obtain ⟨k, p, e, he⟩ := Finpartition.Code.factors (fun i => h (FinEnum.equiv.symm i))
  refine ⟨k, by simpa using Fintype.card_le_of_injective e e.injective, ⟨p, fun i => d (e i), ?_⟩⟩
  intro t b
  simpa [he] using hd t b

/-- Check a fixed hint with the specified enumerations of states and moves. -/
@[expose] def searchHints [FinEnum T] [FinEnum B] [FinEnum C] [DecidableEq O] {H : Type}
    [DecidableEq H] (mode : Mode) (board : Board T B C O) (h : T → H) :=
  search mode board h (FinEnum.toList T) (FinEnum.toList B) (FinEnum.toList C)
    FinEnum.mem_toList FinEnum.mem_toList FinEnum.mem_toList

/-- Return a decoder or rule out every partition on the list. -/
@[expose] def checkPartitions [FinEnum T] [FinEnum B] [FinEnum C] [DecidableEq O]
    (mode : Mode) (board : Board T B C O) {k : Nat} :
    (parts : List (Finpartition.Code (FinEnum.card T) k)) →
    PSum (Scheme mode board k) (∀ w : Scheme mode board k, w.part ∈ parts → False)
  | [] => .inr (by simp)
  | p :: rest =>
    match searchHints mode board (fun t => p.signal (FinEnum.equiv t)) with
    | .success d hd => .inl ⟨p, d, hd⟩
    | .failure obstruction =>
      match checkPartitions mode board rest with
      | .inl w => .inl w
      | .inr exclude => .inr (by
        rintro ⟨q, d, hd⟩ hmem
        rcases List.mem_cons.mp hmem with heq | hrest
        · change q = p at heq
          subst q
          exact obstruction.not_valid d hd
        · exact exclude ⟨q, d, hd⟩ hrest)

/-- A search below a bound either finds a least witness or excludes every size below it. -/
inductive Prefix (F : Nat → Type) (bound : Nat) where
  /-- A witness at a size no larger than that of any other witness. -/
  | optimal (k : Nat) (w : F k) (least : ∀ j, F j → k ≤ j)
  /-- Every size strictly below the search bound has been ruled out. -/
  | none (exclude : ∀ j, j < bound → F j → False)

/-- Search block counts strictly below the given bound in increasing order. -/
@[expose] def below [FinEnum T] [FinEnum B] [FinEnum C] [DecidableEq O]
    (mode : Mode) (board : Board T B C O) : (bound : Nat) → Prefix (Scheme mode board) bound
  | 0 => .none (by simp)
  | bound + 1 =>
    match below mode board bound with
    | .optimal k w least => .optimal k w least
    | .none exclude =>
      match checkPartitions mode board (Finpartition.Code.all (FinEnum.card T) bound) with
      | .inl w => .optimal bound w (fun j v => Nat.le_of_not_gt (fun hj => exclude j hj v))
      | .inr excluded => .none (by
        intro j hj v
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
        · exact exclude j hlt v
        · exact excluded v (Finpartition.Code.mem_all v.part))

end MinimumHint

open MinimumHint

/-- Find the fewest distinct hints. First try a hint that reveals the state. Its failure
identifies a state and move with no translation. Its decoder supplies an upper bound for
the search through partitions with fewer blocks. -/
@[expose] def minimumHint [FinEnum T] [FinEnum B] [FinEnum C] [DecidableEq O]
    (mode : Mode) (board : Board T B C O) : HintResult mode board :=
  match searchHints mode board (FinEnum.equiv : T ≃ Fin (FinEnum.card T)) with
  | .failure obstruction => .impossible obstruction.hintState obstruction.move (by
      intro c
      have heq := FinEnum.equiv.injective (obstruction.hint_eq c)
      simpa [heq] using obstruction.incompatible c)
  | .success fullDecode fullValid =>
    match below mode board (FinEnum.card T) with
    | .optimal k w least =>
      .optimal k (fun t => w.part.signal (FinEnum.equiv t)) w.decode w.valid (by
        intro j h d hd
        obtain ⟨i, hi, ⟨v⟩⟩ := factor_valid mode board h d hd
        exact (least i v).trans hi)
    | .none exclude => .optimal (FinEnum.card T) FinEnum.equiv fullDecode fullValid (by
        intro j h d hd
        obtain ⟨i, hi, ⟨v⟩⟩ := factor_valid mode board h d hd
        exact Nat.le_of_not_gt fun hj => exclude i (lt_of_le_of_lt hi hj) v)

end PolyFunExamples.Bargaining.Replay
