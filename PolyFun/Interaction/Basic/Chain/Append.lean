/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Chain

/-!
# Dependent concatenation of finite interaction chains

This file composes two `TypeTree.Chain` values when the suffix chain may
depend on the complete path through the prefix. The construction preserves the
round boundary carried by `Chain`: a chain of `m` rounds followed by a chain of
`n` rounds produces a chain of `m + n` rounds.

`Chain.then` is the chain-level counterpart of `PFunctor.FreeM.append`.
`toTypeTree_then` states that flattening commutes with concatenation. The API
includes raw and flattened unit laws, a path equivalence with inverse split/join
operations, `liftThen` for dependent output families, and `strategyCompThen`
for strategies crossing the boundary. `toTypeTree_then_assoc` gives the typed
three-stage reassociation law and exposes the unavoidable `Nat.add_assoc`
transport between the two chain indices.

Raw `Chain`-level associativity is intentionally not the public contract:
it would identify continuation functions through the intensional details of
round-count and path transports. `Chain` is a finite-approximant presentation,
while `toTypeTree` is its operational interpretation; consumers therefore use
the stable operational equality `toTypeTree_then_assoc`.
-/

universe u

namespace Interaction
namespace TypeTree
namespace Chain

/-- Transport a chain across an equality of its round count. -/
def castRounds {m n : Nat} (h : m = n) (c : Chain m) : Chain n :=
  h ▸ c

@[simp]
theorem castRounds_rfl {m : Nat} (c : Chain m) : castRounds rfl c = c :=
  rfl

@[simp]
theorem castRounds_symm {m n : Nat} (h : m = n) (c : Chain m) :
    castRounds h.symm (castRounds h c) = c := by
  subst n
  rfl

theorem castRounds_trans {m n p : Nat} (h : m = n) (h' : n = p)
    (c : Chain m) :
    castRounds h' (castRounds h c) = castRounds (h.trans h') c := by
  subst n
  subst p
  rfl

/-- Transporting the round count does not change the flattened type tree. -/
@[simp]
theorem toTypeTree_castRounds {m n : Nat} (h : m = n) (c : Chain m) :
    toTypeTree n (castRounds h c) = toTypeTree m c := by
  subst n
  rfl

/-- Append a path-dependent `n`-round suffix to an `m`-round prefix chain. -/
def «then» : {m n : Nat} → (c : Chain m) →
    (Path (toTypeTree m c) → Chain n) → Chain (m + n)
  | 0, n, _, k => castRounds (Nat.zero_add n).symm (k ⟨⟩)
  | m + 1, n, ⟨tree, cont⟩, k =>
      castRounds (Nat.succ_add m n).symm
        ⟨tree, fun path =>
          Chain.then (cont path) (fun tail =>
            k (appendPath m ⟨tree, cont⟩ path tail))⟩

/-- Flattening a concatenated chain is dependent type-tree append. -/
theorem toTypeTree_then : {m n : Nat} → (c : Chain m) →
    (k : Path (toTypeTree m c) → Chain n) →
    toTypeTree (m + n) (Chain.then c k) =
      (toTypeTree m c).append (fun path => toTypeTree n (k path))
  | 0, n, ⟨⟩, k => by
      simp only [Chain.then, toTypeTree_castRounds, toTypeTree_zero]
      change toTypeTree n (k ⟨⟩) =
        (fun path => toTypeTree n (k path)) ⟨⟩
      rfl
  | m + 1, n, ⟨tree, cont⟩, k => by
      simp only [Chain.then, toTypeTree_castRounds, toTypeTree,
        TypeTree.substMonoid_mult_toFunA]
      rw [PFunctor.FreeM.Path.append_tree_assoc]
      congr 1
      funext path
      rw [toTypeTree_then]
      rfl

/-! ## Unit laws -/

/-- An empty prefix is a left unit for `Chain.then` already at the
round-indexed presentation level. -/
@[simp]
theorem then_zero_left {n : Nat} (c : Chain 0)
    (k : Path (toTypeTree 0 c) → Chain n) :
    castRounds (Nat.zero_add n) (Chain.then c k) = k ⟨⟩ := by
  cases c
  exact castRounds_symm (Nat.zero_add n).symm (k ⟨⟩)

/-- An empty suffix is a right unit for `Chain.then` already at the
round-indexed presentation level. -/
@[simp]
theorem then_zero_right : {m : Nat} → (c : Chain m) →
    (k : Path (toTypeTree m c) → Chain 0) →
    Chain.then c k = c
  | 0, ⟨⟩, k => by cases k ⟨⟩; rfl
  | m + 1, ⟨tree, cont⟩, k => by
      simp only [Chain.then, castRounds]
      congr 1
      funext path
      exact then_zero_right (cont path) (fun tail =>
        k (appendPath m ⟨tree, cont⟩ path tail))

/-- An empty prefix is a left unit for `Chain.then` after flattening. -/
@[simp]
theorem toTypeTree_then_zero_left {n : Nat} (c : Chain 0)
    (k : Path (toTypeTree 0 c) → Chain n) :
    toTypeTree (0 + n) (Chain.then c k) = toTypeTree n (k ⟨⟩) := by
  rw [toTypeTree_then]
  rfl

/-- An empty suffix is a right unit for `Chain.then` after flattening. -/
theorem toTypeTree_then_zero_right {m : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain 0) :
    toTypeTree m (Chain.then c k) = toTypeTree m c := by
  rw [then_zero_right]

/-! ## Paths across the concatenation boundary -/

/-- Paths through a concatenated chain are equivalently a prefix path followed
by a path through the selected suffix chain. -/
def thenPathEquiv {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n) :
    Path (toTypeTree (m + n) (Chain.then c k)) ≃
      (path : Path (toTypeTree m c)) × Path (toTypeTree n (k path)) :=
  (Equiv.cast (congrArg Path (toTypeTree_then c k))).trans
    { toFun := PFunctor.FreeM.Path.split (toTypeTree m c)
        (fun path => toTypeTree n (k path))
      invFun := fun ⟨path, suffix⟩ =>
        PFunctor.FreeM.Path.append (toTypeTree m c)
          (fun path => toTypeTree n (k path)) path suffix
      left_inv := PFunctor.FreeM.Path.append_split _ _
      right_inv := by
        rintro ⟨path, suffix⟩
        exact PFunctor.FreeM.Path.split_append (toTypeTree m c)
          (fun path => toTypeTree n (k path)) path suffix }

/-- Split a path through `c.then k` at the prefix/suffix boundary. -/
def splitThenPath {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n) :
    Path (toTypeTree (m + n) (Chain.then c k)) →
      (path : Path (toTypeTree m c)) × Path (toTypeTree n (k path)) :=
  thenPathEquiv c k

/-- Join a prefix path and selected suffix path into a path through `c.then k`. -/
def appendThenPath {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (path : Path (toTypeTree m c)) (suffix : Path (toTypeTree n (k path))) :
    Path (toTypeTree (m + n) (Chain.then c k)) :=
  (thenPathEquiv c k).symm ⟨path, suffix⟩

@[simp, grind =]
theorem splitThenPath_appendThenPath {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (path : Path (toTypeTree m c)) (suffix : Path (toTypeTree n (k path))) :
    splitThenPath c k (appendThenPath c k path suffix) = ⟨path, suffix⟩ :=
  (thenPathEquiv c k).apply_symm_apply ⟨path, suffix⟩

@[simp, grind =]
theorem appendThenPath_splitThenPath {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (path : Path (toTypeTree (m + n) (Chain.then c k))) :
    appendThenPath c k (splitThenPath c k path).1
      (splitThenPath c k path).2 = path :=
  (thenPathEquiv c k).symm_apply_apply path

/-- `appendThenPath` is the ordinary appended-tree path, transported back
along `toTypeTree_then`. -/
theorem appendThenPath_eq_cast_append {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (path : Path (toTypeTree m c)) (suffix : Path (toTypeTree n (k path))) :
    appendThenPath c k path suffix =
      Equiv.cast (congrArg Path (toTypeTree_then c k)).symm
        (PFunctor.FreeM.Path.append (toTypeTree m c)
          (fun path => toTypeTree n (k path)) path suffix) :=
  rfl

/-! ## Dependent output families and strategies -/

/-- Lift a family indexed separately by a prefix path and its selected suffix
path to a family on paths through the concatenated chain. This is the
chain-boundary counterpart of `PFunctor.FreeM.Path.liftAppend`. -/
def liftThen {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (Family : (path : Path (toTypeTree m c)) →
      Path (toTypeTree n (k path)) → Type u)
    (combined : Path (toTypeTree (m + n) (Chain.then c k))) : Type u :=
  let pieces := splitThenPath c k combined
  Family pieces.1 pieces.2

/-- `liftThen` computes to the original family on a joined boundary path. -/
@[simp]
theorem liftThen_appendThenPath {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (Family : (path : Path (toTypeTree m c)) →
      Path (toTypeTree n (k path)) → Type u)
    (path : Path (toTypeTree m c)) (suffix : Path (toTypeTree n (k path))) :
    liftThen c k Family (appendThenPath c k path suffix) = Family path suffix := by
  unfold liftThen
  rw [splitThenPath_appendThenPath]

/-- After transporting a concatenated-chain path along `toTypeTree_then`,
`liftThen` is exactly the generic appended-tree family `Path.liftAppend`. -/
theorem liftThen_eq_liftAppend_cast {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (Family : (path : Path (toTypeTree m c)) →
      Path (toTypeTree n (k path)) → Type u)
    (combined : Path (toTypeTree (m + n) (Chain.then c k))) :
    liftThen c k Family combined =
      PFunctor.FreeM.Path.liftAppend (toTypeTree m c)
        (fun path => toTypeTree n (k path)) Family
        (Equiv.cast (congrArg Path (toTypeTree_then c k)) combined) := by
  exact (PFunctor.FreeM.Path.liftAppend_split (toTypeTree m c)
    (fun path => toTypeTree n (k path)) Family
    (Equiv.cast (congrArg Path (toTypeTree_then c k)) combined)).symm

/-- The intrinsic `Chain.outputFamily` of a concatenation agrees with the
output family of the suffix selected by the recovered prefix path. -/
theorem outputFamily_then
    (Family : {rounds : Nat} → Chain rounds → Type u)
    {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (combined : Path (toTypeTree (m + n) (Chain.then c k))) :
    outputFamily Family (m + n) (Chain.then c k) combined =
      outputFamily Family n (k (splitThenPath c k combined).1)
        (splitThenPath c k combined).2 := by
  rw [outputFamily_eq_terminal, outputFamily_eq_terminal]

/-- Compose strategies across a `Chain.then` boundary. The output family is
indexed by the prefix/suffix path pair and exposed on the concatenated chain
through `liftThen`. -/
def strategyCompThen {monad : Type u → Type u} [Monad monad]
    {m n : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    {Mid : Path (toTypeTree m c) → Type u}
    {Family : (path : Path (toTypeTree m c)) →
      Path (toTypeTree n (k path)) → Type u}
    (prefixStrategy : Strategy.Plain monad (toTypeTree m c) Mid)
    (suffixStrategy : (path : Path (toTypeTree m c)) → Mid path →
      monad (Strategy.Plain monad (toTypeTree n (k path)) (Family path))) :
    monad (Strategy.Plain monad
      (toTypeTree (m + n) (Chain.then c k)) (liftThen c k Family)) := by
  let hSpec := toTypeTree_then c k
  let composed := Strategy.comp (toTypeTree m c)
    (fun path => toTypeTree n (k path)) prefixStrategy suffixStrategy
  exact (fun strategy =>
    Strategy.castSpec hSpec.symm
      (fun combined => (liftThen_eq_liftAppend_cast c k Family combined).symm)
      strategy) <$> composed

/-! ## Three-stage coherence -/

/-- Reassociate the round-count index of a three-stage chain. -/
def reassoc {m n p : Nat} (c : Chain ((m + n) + p)) :
    Chain (m + (n + p)) :=
  castRounds (Nat.add_assoc m n p) c

/-- Reassociating the round-count index does not change the flattened tree. -/
@[simp]
theorem toTypeTree_reassoc {m n p : Nat} (c : Chain ((m + n) + p)) :
    toTypeTree (m + (n + p)) (reassoc c) = toTypeTree ((m + n) + p) c :=
  toTypeTree_castRounds (Nat.add_assoc m n p) c

/-- Rewrite the prefix tree of a dependent append across an equality, with
the continuation path transported in the opposite direction. -/
private theorem append_cast_prefix {s t : TypeTree} (h : s = t)
    (k : Path s → TypeTree) :
    s.append k =
      t.append (fun path => k (Equiv.cast (congrArg Path h).symm path)) := by
  subst t
  rfl

/-- Operational associativity of dependent chain concatenation. The two chain
presentations have propositionally equal round counts; after `reassoc`, their
flattened type trees agree. The third stage on the right is reindexed by the
joined prefix and middle paths. -/
theorem toTypeTree_then_assoc {m n p : Nat} (c : Chain m)
    (k : Path (toTypeTree m c) → Chain n)
    (l : Path (toTypeTree (m + n) (Chain.then c k)) → Chain p) :
    toTypeTree (m + (n + p))
        (reassoc (Chain.then (Chain.then c k) l)) =
      toTypeTree (m + (n + p))
        (Chain.then c (fun path =>
          Chain.then (k path) (fun suffix =>
            l (appendThenPath c k path suffix)))) := by
  rw [toTypeTree_reassoc, toTypeTree_then]
  calc
    (toTypeTree (m + n) (Chain.then c k)).append
          (fun path => toTypeTree p (l path)) =
        ((toTypeTree m c).append (fun path => toTypeTree n (k path))).append
          (fun path => toTypeTree p
            (l (Equiv.cast (congrArg Path (toTypeTree_then c k)).symm path))) :=
      append_cast_prefix (toTypeTree_then c k) _
    _ = (toTypeTree m c).append (fun path =>
          (toTypeTree n (k path)).append (fun suffix =>
            toTypeTree p
              (l (Equiv.cast (congrArg Path (toTypeTree_then c k)).symm
                (PFunctor.FreeM.Path.append (toTypeTree m c)
                  (fun path => toTypeTree n (k path)) path suffix))))) :=
      PFunctor.FreeM.Path.append_tree_assoc _ _ _
    _ = toTypeTree (m + (n + p))
          (Chain.then c (fun path =>
            Chain.then (k path) (fun suffix =>
              l (appendThenPath c k path suffix)))) := by
      symm
      calc
        toTypeTree (m + (n + p))
              (Chain.then c (fun path =>
                Chain.then (k path) (fun suffix =>
                  l (appendThenPath c k path suffix)))) =
            (toTypeTree m c).append (fun path =>
              toTypeTree (n + p)
                (Chain.then (k path) (fun suffix =>
                  l (appendThenPath c k path suffix)))) :=
          toTypeTree_then c _
        _ = (toTypeTree m c).append (fun path =>
              (toTypeTree n (k path)).append (fun suffix =>
                toTypeTree p (l (appendThenPath c k path suffix)))) := by
          congr 1
          funext path
          exact toTypeTree_then (k path) _
        _ = (toTypeTree m c).append (fun path =>
              (toTypeTree n (k path)).append (fun suffix =>
                toTypeTree p
                  (l (Equiv.cast (congrArg Path (toTypeTree_then c k)).symm
                    (PFunctor.FreeM.Path.append (toTypeTree m c)
                      (fun path => toTypeTree n (k path)) path suffix))))) := by
          rfl

end Chain
end TypeTree
end Interaction
