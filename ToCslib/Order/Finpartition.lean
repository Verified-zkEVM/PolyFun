/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Enumerating finite partitions by their number of parts

Insert the next element into one of the occupied parts or start a fresh part. This gives one
code for each partition of `Fin n` into `k` parts. The public enumeration returns Mathlib
finpartitions and has length the Stirling number of the second kind.
-/

public section

namespace Finpartition

/-- Insert each element into an existing block or put it in the unique new block. -/
inductive Code : Nat → Nat → Type where
  /-- The empty set has no blocks. -/
  | empty : Code 0 0
  /-- Give the new element the name of an existing block. -/
  | join {n k : Nat} : Code n k → Fin k → Code (n + 1) k
  /-- Reserve a new block for the new element. -/
  | fresh {n k : Nat} : Code n k → Code (n + 1) (k + 1)

namespace Code

/-- The element inserted last is indexed by zero. A fresh block is likewise indexed by zero. -/
@[expose] def signal {n k : Nat} : Code n k → Fin n → Fin k
  | .empty => Fin.elim0
  | .join p i => Fin.cons i p.signal
  | .fresh p => Fin.cons 0 (fun t => (p.signal t).succ)

/-- Every name in a canonical partition corresponds to an occupied block. -/
theorem surjective_signal {n k : Nat} (p : Code n k) : Function.Surjective p.signal := by
  induction p with
  | empty => exact fun j => j.elim0
  | join p i ih =>
    intro j
    obtain ⟨t, ht⟩ := ih j
    exact ⟨t.succ, by simpa [signal] using ht⟩
  | fresh p ih =>
    intro j
    cases j using Fin.cases with
    | zero => exact ⟨0, by simp [signal]⟩
    | succ j =>
      obtain ⟨t, ht⟩ := ih j
      exact ⟨t.succ, by simp [signal, ht]⟩

/-- At a fixed block count, equality of the induced partitions implies equality of their codes.
The block names therefore create no duplicates in a search. -/
theorem eq_of_same_fibers {n k : Nat} (p q : Code n k)
    (hf : ∀ s t, p.signal s = p.signal t ↔ q.signal s = q.signal t) : p = q := by
  induction p with
  | empty => cases q; rfl
  | join p i ih =>
    obtain ⟨s, hs⟩ := p.surjective_signal i
    cases q with
    | join q j =>
      have pq := ih q (fun s t => by simpa [signal] using hf s.succ t.succ)
      subst q
      have he := (hf 0 s.succ).1 (by simp [signal, hs])
      have hji : j = i := by simpa [signal, hs] using he
      rw [hji]
    | fresh q =>
      have he := (hf 0 s.succ).1 (by simp [signal, hs])
      simp [signal] at he
      exact (Fin.succ_ne_zero _ he.symm).elim
  | fresh p ih =>
    cases q with
    | join q j =>
      obtain ⟨s, hs⟩ := q.surjective_signal j
      have he := (hf 0 s.succ).2 (by simp [signal, hs])
      simp [signal] at he
      exact (Fin.succ_ne_zero _ he.symm).elim
    | fresh q =>
      exact congrArg fresh (ih q (fun s t => by simpa [signal] using hf s.succ t.succ))

/-- Enumerate all partitions of `n` elements with exactly `k` occupied blocks. -/
@[expose] def all : (n k : Nat) → List (Code n k)
  | 0, 0 => [.empty]
  | 0, _ + 1 => []
  | _ + 1, 0 => []
  | n + 1, k + 1 =>
    ((all n (k + 1)).flatMap fun p => (List.finRange (k + 1)).map (.join p)) ++
      (all n k).map .fresh

/-- Every partition appears in the enumeration for its block count. -/
theorem mem_all {n k : Nat} (p : Code n k) : p ∈ all n k := by
  induction p with
  | empty => simp [all]
  | @join n k p i ih =>
    cases k with
    | zero => exact i.elim0
    | succ k => simp [all, List.mem_flatMap, ih]
  | fresh p ih => simp [all, ih]

/-- Searching one block count tests each canonical partition once. -/
theorem nodup_all (n k : Nat) : (all n k).Nodup := by
  induction n generalizing k with
  | zero => cases k <;> simp [all]
  | succ n ih =>
    cases k with
    | zero => simp [all]
    | succ k =>
      rw [all, List.nodup_append, List.nodup_flatMap]
      refine ⟨⟨fun p _ => List.Nodup.map (fun i j hij => (join.inj hij).2) (List.nodup_finRange _),
        (ih _).imp (fun {p q} hpq => ?_)⟩, List.Nodup.map (fun _ _ => fresh.inj) (ih _), ?_⟩
      · apply List.disjoint_left.mpr
        rintro _ hm hn
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
        obtain ⟨j, _, eq⟩ := List.mem_map.mp hn
        exact hpq (join.inj eq).1.symm
      · intro x hx y hy
        obtain ⟨p, _, hx⟩ := List.mem_flatMap.mp hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
        exact fun h => by cases h

/-- An arbitrary assignment of labels factors through one of the canonical partitions by
an injection of occupied blocks into the original label type. -/
theorem factors {n j : Nat} (h : Fin n → Fin j) :
    ∃ k, ∃ p : Code n k, ∃ e : Fin k ↪ Fin j, ∀ t, e (p.signal t) = h t := by
  induction n with
  | zero =>
    exact ⟨0, .empty, ⟨Fin.elim0, fun x => x.elim0⟩, fun t => t.elim0⟩
  | succ n ih =>
    obtain ⟨k, p, e, he⟩ := ih (fun t => h t.succ)
    by_cases hx : h 0 ∈ Set.range e
    · obtain ⟨i, hi⟩ := hx
      refine ⟨k, p.join i, e, ?_⟩
      exact Fin.cases (by simpa [signal]) (fun t => by simpa [signal] using he t)
    · let f : Fin (k + 1) ↪ Fin j :=
        ⟨Fin.cons (h 0) e, Fin.cons_injective_of_injective hx e.injective⟩
      refine ⟨k + 1, p.fresh, f, ?_⟩
      exact Fin.cases (by simp [signal, f]) (fun t => by simpa [signal, f] using he t)

/-- Number of canonical codes, grouped by the number of occupied blocks. -/
theorem length_all (n k : Nat) : (all n k).length = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [all, Nat.stirlingSecond]
  | succ n ih =>
    cases k with
    | zero => simp [all, Nat.stirlingSecond]
    | succ k =>
      simp [all, List.length_flatMap, Nat.stirlingSecond_succ_succ, ← ih, Nat.mul_comm]

/-- Interpret an enumerated code as the finpartition of its signal fibers. -/
@[expose] def toFinpartition {n k : Nat} (p : Code n k) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  @Finpartition.ofSetoid _ _ _ (Setoid.ker p.signal) (fun i j => decEq (p.signal i) (p.signal j))

/-- Membership in a code's part is equality of the two signal values. -/
theorem mem_part_iff {n k : Nat} (p : Code n k) (i j : Fin n) :
    i ∈ p.toFinpartition.part j ↔ p.signal i = p.signal j := by
  exact (@Finpartition.mem_part_ofSetoid_iff_rel _ _ j _ (Setoid.ker p.signal)
    (fun a b => decEq (p.signal a) (p.signal b)) i).trans eq_comm

/-- Distinct canonical codes at a fixed block count give distinct finpartitions. -/
theorem toFinpartition_injective {n k : Nat} :
    Function.Injective (toFinpartition (n := n) (k := k)) := by
  intro p q hp
  apply eq_of_same_fibers
  intro a b
  rw [← mem_part_iff, ← mem_part_iff, hp]

/-- The number of parts equals the block count carried by a code. -/
theorem card_parts {n k : Nat} (p : Code n k) : p.toFinpartition.parts.card = k := by
  classical
  let rep (i : Fin k) := (p.surjective_signal i).choose
  have hrep (i) : p.signal (rep i) = i := (p.surjective_signal i).choose_spec
  let block (i : Fin k) : p.toFinpartition.parts :=
    ⟨p.toFinpartition.part (rep i), p.toFinpartition.part_mem.mpr (Finset.mem_univ _)⟩
  have eqpart (i j : Fin n) :
      p.toFinpartition.part i = p.toFinpartition.part j ↔ p.signal i = p.signal j :=
    (p.toFinpartition.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _)).symm.trans
      (p.mem_part_iff _ _)
  have inj : Function.Injective block := by
    intro i j h
    simpa [hrep] using (eqpart (rep i) (rep j)).1 (congrArg Subtype.val h)
  have surj : Function.Surjective block := by
    rintro ⟨s, hs⟩
    obtain ⟨x, _, hx⟩ := p.toFinpartition.part_surjOn hs
    refine ⟨p.signal x, Subtype.ext ?_⟩
    exact ((eqpart _ _).2 (hrep _)).trans hx
  simpa using (Fintype.card_congr (Equiv.ofBijective block ⟨inj, surj⟩)).symm

/-- Every finpartition has a code with as many labels as occupied parts. -/
theorem exists_toFinpartition {n : Nat} (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∃ p : Code n P.parts.card, p.toFinpartition = P := by
  classical
  let names := Fintype.equivFin P.parts
  let block (i : Fin n) : P.parts := ⟨P.part i, P.part_mem.mpr (Finset.mem_univ _)⟩
  obtain ⟨k, p, e, he⟩ := factors (fun i => names (block i))
  have part_eq (i : Fin n) : p.toFinpartition.part i = P.part i := by
    ext j
    rw [p.mem_part_iff, P.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _)]
    calc
      p.signal j = p.signal i ↔ e (p.signal j) = e (p.signal i) := e.injective.eq_iff.symm
      _ ↔ names (block j) = names (block i) := by rw [he, he]
      _ ↔ block j = block i := names.injective.eq_iff
      _ ↔ P.part j = P.part i := Subtype.ext_iff
  have eq : p.toFinpartition = P := by
    apply Finpartition.ext
    ext s
    constructor
    · intro hs
      obtain ⟨i, _, rfl⟩ := p.toFinpartition.part_surjOn hs
      rw [part_eq]
      exact P.part_mem.mpr (Finset.mem_univ _)
    · intro hs
      obtain ⟨i, _, rfl⟩ := P.part_surjOn hs
      rw [← part_eq]
      exact p.toFinpartition.part_mem.mpr (Finset.mem_univ _)
  have hk : k = P.parts.card := p.card_parts.symm.trans (congrArg (fun Q => Q.parts.card) eq)
  subst k
  exact ⟨p, eq⟩

end Code

/-- Enumerate the standard finpartitions of `Fin n` into exactly `k` occupied parts. -/
@[expose] def allWithCard (n k : Nat) : List (Finpartition (Finset.univ : Finset (Fin n))) :=
  (Code.all n k).map Code.toFinpartition

/-- The enumeration contains exactly the partitions with the specified number of parts. -/
theorem mem_allWithCard_iff {n k : Nat} (P : Finpartition (Finset.univ : Finset (Fin n))) :
    P ∈ allWithCard n k ↔ P.parts.card = k := by
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    exact p.card_parts
  · rintro rfl
    obtain ⟨p, hp⟩ := Code.exists_toFinpartition P
    exact List.mem_map.mpr ⟨p, p.mem_all, hp⟩

/-- Each enumerated finpartition appears once. -/
theorem nodup_allWithCard (n k : Nat) : (allWithCard n k).Nodup :=
  (Code.nodup_all n k).map Code.toFinpartition_injective

/-- The number of finpartitions of `Fin n` into `k` nonempty parts is a Stirling number. -/
theorem length_allWithCard (n k : Nat) : (allWithCard n k).length = Nat.stirlingSecond n k := by
  simpa [allWithCard] using Code.length_all n k

/-- The subtype of standard finpartitions with `k` parts has cardinality `stirlingSecond n k`. -/
theorem card_subtype_card_parts (n k : Nat) :
    Fintype.card {P : Finpartition (Finset.univ : Finset (Fin n)) // P.parts.card = k} =
      Nat.stirlingSecond n k := by
  calc
    _ = (allWithCard n k).toFinset.card :=
      Fintype.card_of_finset' (p := { P | P.parts.card = k }) _ (fun P => by
        simpa using (mem_allWithCard_iff (k := k) P))
    _ = _ := (List.toFinset_card_of_nodup (nodup_allWithCard n k)).trans (length_allWithCard n k)

end Finpartition
