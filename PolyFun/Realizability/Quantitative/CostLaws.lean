/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Closure

/-!
# Cost laws for structural backend code

`PolyFun.Realizability.Quantitative.Closure` supplies executable structural code (`HasProd`,
`HasSum`, `HasOption`, `IsDistributive`) but no law bounding its work. This file adds:

* the cost-law mixins `HasCompositionCost`, `HasProdCost`, `HasSumCost`, `HasOptionCost` and
  `IsDistributiveCost`. Each bounds the *own* work of a structural primitive, excluding the work of
  the code it wraps, by a monotone function of the encoded size of the data the primitive touches:
  its input, the intermediate value of a composition, or the shared input that pairing duplicates.
  Size laws bound the encodings of pairs, injections and `some` by their components plus a
  constant;
* `structOverhead`, the sum of the mixins' work envelopes, a single monotone function used to
  state carry costs compactly;
* derived cost bounds for `HasProd.withInput`, `HasProd.pairRight`, `HasProd.pairLeft`,
  `IsDistributive.elimContext`, the option strength `HasOption.strength`, and the carry
  combinators `exchange`, `rotate`, `carryReadout`, `carryReadoutWith` and `carryUpdate`.

The laws are *additive*: wrapped black-box code is charged exactly its own cost. This holds for
backends whose combinators cost a size-dependent amount on top of their parts, such as RAM-style
models or first-order cost semantics. It fails for the single-tape backend of
`ComplexityBackends`, whose `composeOverhead` evaluates the second machine's time polynomial at an
inflated input size, so structural code composed before black-box code is not additive there.
-/

@[expose] public section

universe u v w

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-! ## Cost-law mixins -/

/-- Work laws for identity code and for the connection overhead of composition.

`composeOverhead_le` charges the connection by the size of the intermediate value, so composed
code costs its parts plus a function of what is passed between them. -/
class HasCompositionCost [Q.HasCategory] where
  /-- Envelope for identity work and composition glue, as a function of an encoded size. -/
  overhead : ℕ → ℕ
  /-- The envelope is monotone. -/
  monotone_overhead : Monotone overhead
  /-- Identity code costs at most the envelope at its input size. -/
  cost_identity_le : ∀ {A : Type u} (a : C.Str A) (x : A),
    Q.cost (Q.identity a) x ≤ overhead (Q.size a x)
  /-- Composition glue costs at most the envelope at the intermediate size. -/
  composeOverhead_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} (rf : Q.Realizer a b f) (rg : Q.Realizer b d g) (x : A),
    Q.composeOverhead rf rg x ≤ overhead (Q.size b (f x))

/-- Size and work laws for product code: projections cost the envelope at the pair's size, and
pairing costs its two parts plus the envelope at the size of the shared, duplicated input. -/
class HasProdCost [P : C.HasProd] [QP : Q.HasProd] where
  /-- Constant size overhead of the pinned pair encoding. -/
  sizeOverhead : ℕ
  /-- A pair is encoded within its components plus the constant overhead. -/
  size_prod_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (x : A) (y : B),
    Q.size (P.prod a b) (x, y) ≤ Q.size a x + Q.size b y + sizeOverhead
  /-- Work envelope of the product primitives. -/
  overhead : ℕ → ℕ
  /-- The envelope is monotone. -/
  monotone_overhead : Monotone overhead
  /-- The first projection costs at most the envelope at the pair's size. -/
  cost_fst_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (z : A × B),
    Q.cost (QP.fst a b) z ≤ overhead (Q.size (P.prod a b) z)
  /-- The second projection costs at most the envelope at the pair's size. -/
  cost_snd_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (z : A × B),
    Q.cost (QP.snd a b) z ≤ overhead (Q.size (P.prod a b) z)
  /-- Pairing costs its parts plus the envelope at the shared input's size. -/
  cost_pair_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D} (rf : Q.Realizer a b f) (rg : Q.Realizer a d g) (x : A),
    Q.cost (QP.pair rf rg) x ≤ Q.cost rf x + Q.cost rg x + overhead (Q.size a x)

/-- Size and work laws for sum code. Injections neither shrink nor grow a payload by more than a
constant; case analysis costs the selected branch plus the envelope at the scrutinee's size. -/
class HasSumCost [S : C.HasSum] [QS : Q.HasSum] where
  /-- Constant size overhead of the pinned tag. -/
  sizeOverhead : ℕ
  /-- A left injection grows its payload by at most the tag overhead. -/
  size_inl_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (x : A),
    Q.size (S.sum a b) (Sum.inl x) ≤ Q.size a x + sizeOverhead
  /-- A right injection grows its payload by at most the tag overhead. -/
  size_inr_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (y : B),
    Q.size (S.sum a b) (Sum.inr y) ≤ Q.size b y + sizeOverhead
  /-- A left injection does not shrink its payload. -/
  le_size_inl : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (x : A),
    Q.size a x ≤ Q.size (S.sum a b) (Sum.inl x)
  /-- A right injection does not shrink its payload. -/
  le_size_inr : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (y : B),
    Q.size b y ≤ Q.size (S.sum a b) (Sum.inr y)
  /-- Work envelope of the sum primitives. -/
  overhead : ℕ → ℕ
  /-- The envelope is monotone. -/
  monotone_overhead : Monotone overhead
  /-- A left injection costs at most the envelope at its payload's size. -/
  cost_inl_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (x : A),
    Q.cost (QS.inl a b) x ≤ overhead (Q.size a x)
  /-- A right injection costs at most the envelope at its payload's size. -/
  cost_inr_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (y : B),
    Q.cost (QS.inr a b) y ≤ overhead (Q.size b y)
  /-- Case analysis costs the selected branch plus the envelope at the scrutinee's size. -/
  cost_elim_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D} (rf : Q.Realizer a d f) (rg : Q.Realizer b d g) (z : A ⊕ B),
    Q.cost (QS.elim rf rg) z ≤
      Sum.elim (Q.cost rf) (Q.cost rg) z + overhead (Q.size (S.sum a b) z)

/-- Size and work laws for the optional-value code that product-state machines use. -/
class HasOptionCost [P : C.HasProd] [O : C.HasOption] [QO : Q.HasOption] where
  /-- Constant size overhead of the pinned option tag. -/
  sizeOverhead : ℕ
  /-- A present value grows its payload by at most the tag overhead. -/
  size_some_le : ∀ {A : Type u} (a : C.Str A) (x : A),
    Q.size (O.option a) (some x) ≤ Q.size a x + sizeOverhead
  /-- Work envelope of the option primitives. -/
  overhead : ℕ → ℕ
  /-- The envelope is monotone. -/
  monotone_overhead : Monotone overhead
  /-- Wrapping a present value costs at most the envelope at its payload's size. -/
  cost_some_le : ∀ {A : Type u} (a : C.Str A) (x : A),
    Q.cost (QO.some a) x ≤ overhead (Q.size a x)
  /-- A contextual bind costs its continuation on a present value plus the envelope at the
  input's size. -/
  cost_bindContext_le : ∀ {A B E : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {k : A × E → Option B} (code : Q.Realizer (P.prod a e) (O.option b) k)
    (z : Option A × E),
    Q.cost (QO.bindContext code) z ≤
      z.1.elim 0 (fun x ↦ Q.cost code (x, z.2)) + overhead (Q.size (P.prod (O.option a) e) z)

/-- Work law for executable distributivity. -/
class IsDistributiveCost [P : C.HasProd] [S : C.HasSum] [QD : Q.IsDistributive] where
  /-- Work envelope of the distributivity primitive. -/
  overhead : ℕ → ℕ
  /-- The envelope is monotone. -/
  monotone_overhead : Monotone overhead
  /-- Distribution costs at most the envelope at its input's size. -/
  cost_distribute_le : ∀ {A B E : Type u} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    (z : (A ⊕ B) × E),
    Q.cost (QD.distribute a b e) z ≤ overhead (Q.size (P.prod (S.sum a b) e) z)

/-! ## The combined structural envelope -/

section Envelope

variable [Q.HasCategory] [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
  [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost] [OC : Q.HasOptionCost]
  [DC : Q.IsDistributiveCost]

/-- The sum of all structural work envelopes: one monotone function bounding the own work of
every structural primitive at a given encoded size. -/
def structOverhead (n : ℕ) : ℕ :=
  CC.overhead n + PC.overhead n + SC.overhead n + OC.overhead n + DC.overhead n

theorem monotone_structOverhead : Monotone (structOverhead Q) := by
  intro m n h
  unfold structOverhead
  have := CC.monotone_overhead h
  have := PC.monotone_overhead h
  have := SC.monotone_overhead h
  have := OC.monotone_overhead h
  have := DC.monotone_overhead h
  omega

theorem composition_overhead_le {m n : ℕ} (h : m ≤ n) : CC.overhead m ≤ structOverhead Q n := by
  have := CC.monotone_overhead h
  unfold structOverhead; omega

theorem prod_overhead_le {m n : ℕ} (h : m ≤ n) : PC.overhead m ≤ structOverhead Q n := by
  have := PC.monotone_overhead h
  unfold structOverhead; omega

theorem sum_overhead_le {m n : ℕ} (h : m ≤ n) : SC.overhead m ≤ structOverhead Q n := by
  have := SC.monotone_overhead h
  unfold structOverhead; omega

theorem option_overhead_le {m n : ℕ} (h : m ≤ n) : OC.overhead m ≤ structOverhead Q n := by
  have := OC.monotone_overhead h
  unfold structOverhead; omega

theorem distributive_overhead_le {m n : ℕ} (h : m ≤ n) :
    DC.overhead m ≤ structOverhead Q n := by
  have := DC.monotone_overhead h
  unfold structOverhead; omega

end Envelope

/-! ## Derived cost bounds -/

section Derived

variable [Q.HasCategory] [CC : Q.HasCompositionCost] [P : C.HasProd] [QP : Q.HasProd]
  [PC : Q.HasProdCost]

/-- Retaining an input costs the wrapped code plus identity and pairing at the input's size. -/
theorem cost_withInput_le {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (x : A) :
    Q.cost (HasProd.withInput Q QP code) x ≤
      Q.cost code x + CC.overhead (Q.size a x) + PC.overhead (Q.size a x) := by
  have hpair := PC.cost_pair_le code (Q.identity a) x
  have hid := CC.cost_identity_le a x
  change Q.cost (QP.pair code (Q.identity a)) x ≤ _
  omega

/-- Running code on the first component while carrying the second costs the code plus two
projections and one pairing at the pair's size, and composition glue at the first component's
size. -/
theorem cost_pairRight_le {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} (code : Q.Realizer a b f) (x : A) (y : D) :
    Q.cost (HasProd.pairRight Q QP (d := d) code) (x, y) ≤
      Q.cost code x + 3 * PC.overhead (Q.size (P.prod a d) (x, y)) +
        CC.overhead (Q.size a x) := by
  rw [HasProd.pairRight, Realizer.cost_castFunction]
  have hpair := PC.cost_pair_le (Q.compose (QP.fst a d) code) (QP.snd a d) (x, y)
  have hcomp := Q.cost_comp_le (QP.fst a d) code (x, y)
  have hglue := CC.composeOverhead_le (QP.fst a d) code (x, y)
  have hfst := PC.cost_fst_le a d (x, y)
  have hsnd := PC.cost_snd_le a d (x, y)
  change Q.cost (QP.fst a d) (x, y) + Q.cost code x + Q.composeOverhead (QP.fst a d) code (x, y)
    ≥ Q.cost (Q.compose (QP.fst a d) code) (x, y) at hcomp
  change CC.overhead (Q.size a x) ≥ Q.composeOverhead (QP.fst a d) code (x, y) at hglue
  omega

/-- Running code on the second component while carrying the first: the mirror of
`cost_pairRight_le`. -/
theorem cost_pairLeft_le {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} (code : Q.Realizer a b f) (y : D) (x : A) :
    Q.cost (HasProd.pairLeft Q QP (d := d) code) (y, x) ≤
      Q.cost code x + 3 * PC.overhead (Q.size (P.prod d a) (y, x)) +
        CC.overhead (Q.size a x) := by
  rw [HasProd.pairLeft, Realizer.cost_castFunction]
  have hpair := PC.cost_pair_le (QP.fst d a) (Q.compose (QP.snd d a) code) (y, x)
  have hcomp := Q.cost_comp_le (QP.snd d a) code (y, x)
  have hglue := CC.composeOverhead_le (QP.snd d a) code (y, x)
  have hfst := PC.cost_fst_le d a (y, x)
  have hsnd := PC.cost_snd_le d a (y, x)
  change Q.cost (QP.snd d a) (y, x) + Q.cost code x + Q.composeOverhead (QP.snd d a) code (y, x)
    ≥ Q.cost (Q.compose (QP.snd d a) code) (y, x) at hcomp
  change CC.overhead (Q.size a x) ≥ Q.composeOverhead (QP.snd d a) code (y, x) at hglue
  omega

variable [S : C.HasSum] [QS : Q.HasSum] [SC : Q.HasSumCost] [QD : Q.IsDistributive]
  [DC : Q.IsDistributiveCost]

omit QP PC in
/-- Case analysis in a context, left branch: the branch code plus distribution, case analysis and
glue, each at the size of the distributed scrutinee. -/
theorem cost_elimContext_inl_le {A B E D : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {d : C.Str D} {f : A × E → D} {g : B × E → D}
    (left : Q.Realizer (P.prod a e) d f) (right : Q.Realizer (P.prod b e) d g) (x : A) (y : E) :
    Q.cost (IsDistributive.elimContext Q QD left right) (Sum.inl x, y) ≤
      Q.cost left (x, y) + DC.overhead (Q.size (P.prod (S.sum a b) e) (Sum.inl x, y)) +
        SC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inl (x, y))) +
        CC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inl (x, y))) := by
  rw [IsDistributive.elimContext, Realizer.cost_castFunction]
  have hcomp := Q.cost_comp_le (QD.distribute a b e) (QS.elim left right) (Sum.inl x, y)
  have hglue := CC.composeOverhead_le (QD.distribute a b e) (QS.elim left right) (Sum.inl x, y)
  have hdist := DC.cost_distribute_le a b e (Sum.inl x, y)
  have helim := SC.cost_elim_le left right (Sum.inl (x, y))
  change Q.cost (QD.distribute a b e) (Sum.inl x, y) + Q.cost (QS.elim left right) (Sum.inl (x, y))
    + Q.composeOverhead (QD.distribute a b e) (QS.elim left right) (Sum.inl x, y)
    ≥ Q.cost (Q.compose (QD.distribute a b e) (QS.elim left right)) (Sum.inl x, y) at hcomp
  change CC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inl (x, y))) ≥
    Q.composeOverhead (QD.distribute a b e) (QS.elim left right) (Sum.inl x, y) at hglue
  simp only [Sum.elim_inl] at helim
  omega

omit QP PC in
/-- Case analysis in a context, right branch. -/
theorem cost_elimContext_inr_le {A B E D : Type u} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    {d : C.Str D} {f : A × E → D} {g : B × E → D}
    (left : Q.Realizer (P.prod a e) d f) (right : Q.Realizer (P.prod b e) d g) (x : B) (y : E) :
    Q.cost (IsDistributive.elimContext Q QD left right) (Sum.inr x, y) ≤
      Q.cost right (x, y) + DC.overhead (Q.size (P.prod (S.sum a b) e) (Sum.inr x, y)) +
        SC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inr (x, y))) +
        CC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inr (x, y))) := by
  rw [IsDistributive.elimContext, Realizer.cost_castFunction]
  have hcomp := Q.cost_comp_le (QD.distribute a b e) (QS.elim left right) (Sum.inr x, y)
  have hglue := CC.composeOverhead_le (QD.distribute a b e) (QS.elim left right) (Sum.inr x, y)
  have hdist := DC.cost_distribute_le a b e (Sum.inr x, y)
  have helim := SC.cost_elim_le left right (Sum.inr (x, y))
  change Q.cost (QD.distribute a b e) (Sum.inr x, y) + Q.cost (QS.elim left right) (Sum.inr (x, y))
    + Q.composeOverhead (QD.distribute a b e) (QS.elim left right) (Sum.inr x, y)
    ≥ Q.cost (Q.compose (QD.distribute a b e) (QS.elim left right)) (Sum.inr x, y) at hcomp
  change CC.overhead (Q.size (S.sum (P.prod a e) (P.prod b e)) (Sum.inr (x, y))) ≥
    Q.composeOverhead (QD.distribute a b e) (QS.elim left right) (Sum.inr x, y) at hglue
  simp only [Sum.elim_inr] at helim
  omega

end Derived

section Strength

variable [P : C.HasProd] [O : C.HasOption] [QO : Q.HasOption] [OC : Q.HasOptionCost]

/-- The option strength on a present value costs `some` at the payload pair's size plus the
contextual bind at the input's size. -/
theorem cost_strength_some_le {A E : Type u} (a : C.Str A) (e : C.Str E) (x : A) (y : E) :
    Q.cost (HasOption.strength Q QO a e) (some x, y) ≤
      OC.overhead (Q.size (P.prod a e) (x, y)) +
        OC.overhead (Q.size (P.prod (O.option a) e) (some x, y)) := by
  rw [HasOption.strength, Realizer.cost_castFunction]
  have hbind := OC.cost_bindContext_le (QO.some (P.prod a e)) (some x, y)
  have hsome := OC.cost_some_le (P.prod a e) (x, y)
  simp only [Option.elim_some] at hbind
  omega

end Strength

/-! ## Cost bounds for the carry combinators -/

section Carry

variable [Q.HasCategory] [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
  [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost] [OC : Q.HasOptionCost]
  [DC : Q.IsDistributiveCost]

omit [S : C.HasSum] [O : C.HasOption] [QS : Q.HasSum] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [SC : Q.HasSumCost] [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost] in
/-- The rotation costs at most nine product primitives and glues. -/
theorem cost_rotate_le {A E I : Type u} (a : C.Str A) (e : C.Str E) (i : C.Str I)
    (x : A) (y : E) (j : I) :
    Q.cost (rotate Q a e i) ((x, y), j) ≤
      5 * PC.overhead (Q.size (P.prod (P.prod a e) i) ((x, y), j)) +
        2 * PC.overhead (Q.size (P.prod a e) (x, y)) +
        2 * CC.overhead (Q.size (P.prod a e) (x, y)) := by
  unfold rotate
  have hout := PC.cost_pair_le
    (QP.pair (QP.snd (P.prod a e) i) (Q.compose (QP.fst (P.prod a e) i) (QP.snd a e)))
    (Q.compose (QP.fst (P.prod a e) i) (QP.fst a e)) ((x, y), j)
  have hin := PC.cost_pair_le (QP.snd (P.prod a e) i)
    (Q.compose (QP.fst (P.prod a e) i) (QP.snd a e)) ((x, y), j)
  have hc1 := Q.cost_comp_le (QP.fst (P.prod a e) i) (QP.snd a e) ((x, y), j)
  have hc2 := Q.cost_comp_le (QP.fst (P.prod a e) i) (QP.fst a e) ((x, y), j)
  have hg1 := CC.composeOverhead_le (QP.fst (P.prod a e) i) (QP.snd a e) ((x, y), j)
  have hg2 := CC.composeOverhead_le (QP.fst (P.prod a e) i) (QP.fst a e) ((x, y), j)
  have hf := PC.cost_fst_le (P.prod a e) i ((x, y), j)
  have hs := PC.cost_snd_le (P.prod a e) i ((x, y), j)
  have hf' := PC.cost_fst_le a e (x, y)
  have hs' := PC.cost_snd_le a e (x, y)
  dsimp only at hc1 hc2 hg1 hg2
  omega

omit [S : C.HasSum] [O : C.HasOption] [QS : Q.HasSum] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [SC : Q.HasSumCost] [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost] in
/-- The exchange costs at most nine product primitives and glues, at the sizes of its input and of
the inner pair. -/
theorem cost_exchange_le {A E I : Type u} (a : C.Str A) (e : C.Str E) (i : C.Str I)
    (x : A) (y : E) (j : I) :
    Q.cost (exchange Q a e i) ((x, y), j) ≤
      5 * PC.overhead (Q.size (P.prod (P.prod a e) i) ((x, y), j)) +
        2 * PC.overhead (Q.size (P.prod a e) (x, y)) +
        2 * CC.overhead (Q.size (P.prod a e) (x, y)) := by
  unfold exchange
  have hout := PC.cost_pair_le
    (QP.pair (Q.compose (QP.fst (P.prod a e) i) (QP.fst a e)) (QP.snd (P.prod a e) i))
    (Q.compose (QP.fst (P.prod a e) i) (QP.snd a e)) ((x, y), j)
  have hin := PC.cost_pair_le (Q.compose (QP.fst (P.prod a e) i) (QP.fst a e))
    (QP.snd (P.prod a e) i) ((x, y), j)
  have hc1 := Q.cost_comp_le (QP.fst (P.prod a e) i) (QP.fst a e) ((x, y), j)
  have hc2 := Q.cost_comp_le (QP.fst (P.prod a e) i) (QP.snd a e) ((x, y), j)
  have hg1 := CC.composeOverhead_le (QP.fst (P.prod a e) i) (QP.fst a e) ((x, y), j)
  have hg2 := CC.composeOverhead_le (QP.fst (P.prod a e) i) (QP.snd a e) ((x, y), j)
  have hf := PC.cost_fst_le (P.prod a e) i ((x, y), j)
  have hs := PC.cost_snd_le (P.prod a e) i ((x, y), j)
  have hf' := PC.cost_fst_le a e (x, y)
  have hs' := PC.cost_snd_le a e (x, y)
  dsimp only at hc1 hc2 hg1 hg2
  omega

/-- Attaching a carried value to a readout costs the wrapped code plus at most eleven structural
primitives, each charged the combined envelope at the input, readout and carried sizes. -/
theorem cost_carryReadout_le {A B D E : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (e : C.Str E) {f : A → B ⊕ D} (code : Q.Realizer a (S.sum b d) f) (x : A) (y : E) :
    Q.cost (carryReadout Q e code) (x, y) ≤ Q.cost code x +
      11 * structOverhead Q (Q.size a x + Q.size (S.sum b d) (f x) + Q.size e y +
        PC.sizeOverhead + SC.sizeOverhead) := by
  rw [carryReadout, Realizer.cost_castFunction]
  set N := Q.size a x + Q.size (S.sum b d) (f x) + Q.size e y + PC.sizeOverhead +
    SC.sizeOverhead with hN
  have hcomp := Q.cost_comp_le (HasProd.pairRight Q QP (d := e) code)
    (IsDistributive.elimContext Q QD (QS.inl (P.prod b e) d)
      (Q.compose (QP.fst d e) (QS.inr (P.prod b e) d))) (x, y)
  have hglue := CC.composeOverhead_le (HasProd.pairRight Q QP (d := e) code)
    (IsDistributive.elimContext Q QD (QS.inl (P.prod b e) d)
      (Q.compose (QP.fst d e) (QS.inr (P.prod b e) d))) (x, y)
  have hPR := cost_pairRight_le Q (d := e) code x y
  have hsxy := PC.size_prod_le a e x y
  have hsfy := PC.size_prod_le (S.sum b d) e (f x) y
  have h1 := prod_overhead_le Q (show Q.size (P.prod a e) (x, y) ≤ N by omega)
  have h2 := composition_overhead_le Q (show Q.size a x ≤ N by omega)
  have h3 := composition_overhead_le Q (show Q.size (P.prod (S.sum b d) e) (f x, y) ≤ N by omega)
  dsimp only at hcomp hglue
  rcases hfx : f x with v | q
  · rw [hfx] at hcomp hglue hsfy h3
    rw [hfx] at hN
    have hE := cost_elimContext_inl_le Q (QS.inl (P.prod b e) d)
      (Q.compose (QP.fst d e) (QS.inr (P.prod b e) d)) v y
    have hinl := SC.cost_inl_le (P.prod b e) d (v, y)
    have hv := SC.le_size_inl b d v
    have hvy := PC.size_prod_le b e v y
    have hdist := SC.size_inl_le (P.prod b e) (P.prod d e) (v, y)
    have h4 := distributive_overhead_le Q
      (show Q.size (P.prod (S.sum b d) e) (Sum.inl v, y) ≤ N by omega)
    have h5 := sum_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inl (v, y)) ≤ N by omega)
    have h6 := composition_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inl (v, y)) ≤ N by omega)
    have h7 := sum_overhead_le Q (show Q.size (P.prod b e) (v, y) ≤ N by omega)
    omega
  · rw [hfx] at hcomp hglue hsfy h3
    rw [hfx] at hN
    have hE := cost_elimContext_inr_le Q (QS.inl (P.prod b e) d)
      (Q.compose (QP.fst d e) (QS.inr (P.prod b e) d)) q y
    have hc := Q.cost_comp_le (QP.fst d e) (QS.inr (P.prod b e) d) (q, y)
    have hg := CC.composeOverhead_le (QP.fst d e) (QS.inr (P.prod b e) d) (q, y)
    have hfst := PC.cost_fst_le d e (q, y)
    have hinr := SC.cost_inr_le (P.prod b e) d q
    have hq := SC.le_size_inr b d q
    have hqy := PC.size_prod_le d e q y
    have hdist := SC.size_inr_le (P.prod b e) (P.prod d e) (q, y)
    dsimp only at hc hg
    have h4 := distributive_overhead_le Q
      (show Q.size (P.prod (S.sum b d) e) (Sum.inr q, y) ≤ N by omega)
    have h5 := sum_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inr (q, y)) ≤ N by omega)
    have h6 := composition_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inr (q, y)) ≤ N by omega)
    have h7 := prod_overhead_le Q (show Q.size (P.prod d e) (q, y) ≤ N by omega)
    have h8 := sum_overhead_le Q (show Q.size d q ≤ N by omega)
    have h9 := composition_overhead_le Q (show Q.size d q ≤ N by omega)
    omega

/-- Stepping a partial transition while carrying a value costs the wrapped code plus at most
seventeen structural primitives, each charged the combined envelope at a size bounded by the
source and target states, the carried value and the index. -/
theorem cost_carryUpdate_le {A I E : Type u} {a : C.Str A} {i : C.Str I} (e : C.Str E)
    {g : A × I → Option A} (code : Q.Realizer (P.prod a i) (O.option a) g)
    (x : A) (y : E) (j : I) {x' : A} (hg : g (x, j) = some x') :
    Q.cost (carryUpdate Q e code) ((x, y), j) ≤ Q.cost code (x, j) +
      17 * structOverhead Q (Q.size a x + Q.size a x' + Q.size e y + Q.size i j +
        2 * PC.sizeOverhead + OC.sizeOverhead) := by
  rw [carryUpdate, Realizer.cost_castFunction]
  set N := Q.size a x + Q.size a x' + Q.size e y + Q.size i j + 2 * PC.sizeOverhead +
    OC.sizeOverhead with hN
  have hcomp := Q.cost_comp_le (exchange Q a e i)
    (Q.compose (HasProd.pairRight Q QP (d := e) code) (HasOption.strength Q QO a e)) ((x, y), j)
  have hglue := CC.composeOverhead_le (exchange Q a e i)
    (Q.compose (HasProd.pairRight Q QP (d := e) code) (HasOption.strength Q QO a e)) ((x, y), j)
  have hcomp' := Q.cost_comp_le (HasProd.pairRight Q QP (d := e) code)
    (HasOption.strength Q QO a e) ((x, j), y)
  have hglue' := CC.composeOverhead_le (HasProd.pairRight Q QP (d := e) code)
    (HasOption.strength Q QO a e) ((x, j), y)
  dsimp only at hcomp hglue hcomp' hglue'
  rw [hg] at hcomp' hglue'
  have hex := cost_exchange_le Q a e i x y j
  have hPR := cost_pairRight_le Q (d := e) code (x, j) y
  have hst := cost_strength_some_le Q a e x' y
  have hsxy := PC.size_prod_le a e x y
  have hsz := PC.size_prod_le (P.prod a e) i (x, y) j
  have hsxj := PC.size_prod_le a i x j
  have hsw := PC.size_prod_le (P.prod a i) e (x, j) y
  have hso := PC.size_prod_le (O.option a) e (some x') y
  have hsome := OC.size_some_le a x'
  have hsx'y := PC.size_prod_le a e x' y
  have h1 := prod_overhead_le Q (show Q.size (P.prod (P.prod a e) i) ((x, y), j) ≤ N by omega)
  have h2 := prod_overhead_le Q (show Q.size (P.prod a e) (x, y) ≤ N by omega)
  have h3 := composition_overhead_le Q (show Q.size (P.prod a e) (x, y) ≤ N by omega)
  have h4 := composition_overhead_le Q
    (show Q.size (P.prod (P.prod a i) e) ((x, j), y) ≤ N by omega)
  have h5 := prod_overhead_le Q (show Q.size (P.prod (P.prod a i) e) ((x, j), y) ≤ N by omega)
  have h6 := composition_overhead_le Q (show Q.size (P.prod a i) (x, j) ≤ N by omega)
  have h7 := option_overhead_le Q (show Q.size (P.prod a e) (x', y) ≤ N by omega)
  have h8 := option_overhead_le Q
    (show Q.size (P.prod (O.option a) e) (some x', y) ≤ N by omega)
  have h9 := composition_overhead_le Q
    (show Q.size (P.prod (O.option a) e) (some x', y) ≤ N by omega)
  omega

/-- Attaching a carried value and post-processing the other summand costs the readout code, the
post-processing code on the branch taken, and at most ten structural primitives, each charged the
combined envelope at the input, readout, carried and output sizes. -/
theorem cost_carryReadoutWith_le {A B D D' E : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {d' : C.Str D'} {e : C.Str E} {f : A → B ⊕ D} {g : D × E → D'}
    (code : Q.Realizer a (S.sum b d) f) (right : Q.Realizer (P.prod d e) d' g) (x : A) (y : E) :
    Q.cost (carryReadoutWith Q code right) (x, y) ≤ Q.cost code x +
      (f x).elim (fun _ ↦ 0) (fun q ↦ Q.cost right (q, y)) +
      10 * structOverhead Q (Q.size a x + Q.size (S.sum b d) (f x) + Q.size e y +
        Q.size (S.sum (P.prod b e) d')
          (Sum.elim (fun value ↦ Sum.inl (value, y)) (fun q ↦ Sum.inr (g (q, y))) (f x)) +
        PC.sizeOverhead + SC.sizeOverhead) := by
  rw [carryReadoutWith, Realizer.cost_castFunction]
  set N := Q.size a x + Q.size (S.sum b d) (f x) + Q.size e y +
    Q.size (S.sum (P.prod b e) d')
      (Sum.elim (fun value ↦ Sum.inl (value, y)) (fun q ↦ Sum.inr (g (q, y))) (f x)) +
    PC.sizeOverhead + SC.sizeOverhead with hN
  have hcomp := Q.cost_comp_le (HasProd.pairRight Q QP (d := e) code)
    (IsDistributive.elimContext Q QD (QS.inl (P.prod b e) d')
      (Q.compose right (QS.inr (P.prod b e) d'))) (x, y)
  have hglue := CC.composeOverhead_le (HasProd.pairRight Q QP (d := e) code)
    (IsDistributive.elimContext Q QD (QS.inl (P.prod b e) d')
      (Q.compose right (QS.inr (P.prod b e) d'))) (x, y)
  have hPR := cost_pairRight_le Q (d := e) code x y
  have hsxy := PC.size_prod_le a e x y
  have hsfy := PC.size_prod_le (S.sum b d) e (f x) y
  have h1 := prod_overhead_le Q (show Q.size (P.prod a e) (x, y) ≤ N by omega)
  have h2 := composition_overhead_le Q (show Q.size a x ≤ N by omega)
  have h3 := composition_overhead_le Q (show Q.size (P.prod (S.sum b d) e) (f x, y) ≤ N by omega)
  dsimp only at hcomp hglue
  rcases hfx : f x with v | q
  · rw [hfx] at hcomp hglue hsfy h3
    rw [hfx] at hN
    simp only [Sum.elim_inl] at hN ⊢
    have hE := cost_elimContext_inl_le Q (QS.inl (P.prod b e) d')
      (Q.compose right (QS.inr (P.prod b e) d')) v y
    have hinl := SC.cost_inl_le (P.prod b e) d' (v, y)
    have hout := SC.le_size_inl (P.prod b e) d' (v, y)
    have hdist := SC.size_inl_le (P.prod b e) (P.prod d e) (v, y)
    have h4 := distributive_overhead_le Q
      (show Q.size (P.prod (S.sum b d) e) (Sum.inl v, y) ≤ N by omega)
    have h5 := sum_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inl (v, y)) ≤ N by omega)
    have h6 := composition_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inl (v, y)) ≤ N by omega)
    have h7 := sum_overhead_le Q (show Q.size (P.prod b e) (v, y) ≤ N by omega)
    omega
  · rw [hfx] at hcomp hglue hsfy h3
    rw [hfx] at hN
    simp only [Sum.elim_inr] at hN ⊢
    have hE := cost_elimContext_inr_le Q (QS.inl (P.prod b e) d')
      (Q.compose right (QS.inr (P.prod b e) d')) q y
    have hc := Q.cost_comp_le right (QS.inr (P.prod b e) d') (q, y)
    have hg := CC.composeOverhead_le right (QS.inr (P.prod b e) d') (q, y)
    have hinr := SC.cost_inr_le (P.prod b e) d' (g (q, y))
    have hq := SC.le_size_inr b d q
    have hqy := PC.size_prod_le d e q y
    have hdist := SC.size_inr_le (P.prod b e) (P.prod d e) (q, y)
    have hout := SC.le_size_inr (P.prod b e) d' (g (q, y))
    have h4 := distributive_overhead_le Q
      (show Q.size (P.prod (S.sum b d) e) (Sum.inr q, y) ≤ N by omega)
    have h5 := sum_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inr (q, y)) ≤ N by omega)
    have h6 := composition_overhead_le Q
      (show Q.size (S.sum (P.prod b e) (P.prod d e)) (Sum.inr (q, y)) ≤ N by omega)
    have h8 := sum_overhead_le Q (show Q.size d' (g (q, y)) ≤ N by omega)
    have h9 := composition_overhead_le Q (show Q.size d' (g (q, y)) ≤ N by omega)
    omega

end Carry

end PFunctor.QuantitativeStepClass
