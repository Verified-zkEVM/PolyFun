/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Parallel

/-!
# Parallel composition of free polynomial programs

`FreeM.parallel` executes two free programs in lockstep.  If only one program
is currently requesting an operation, it emits the corresponding one-sided
operation of `P ∥ Q`; if both request operations, it emits a joint operation.
This is the operational construction called `bothProg` in Aberlé's paper.

This module owns only the display-independent operational layer.  Displayed
lifts live in `PolyFun.PFunctor.Display.Parallel.Free`.

The structural lens operation is symmetric monoidal, and `FreeM.parallel`
respects its unit, symmetry, and associativity maps.  However, lockstep
parallelization is not bifunctorial for arbitrary Kleisli handlers:
interpreting a component can erase an operation and thereby change which
later operations synchronize.  Consequently this module deliberately does
not state an unrestricted interchange theorem between `Handler.parallel` and
`Handler.comp`; `PolyFunTest.PFunctor.Parallel` records a concrete
counterexample.  Such an interchange law needs an additional scheduling or
commutativity discipline.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uA₄ uA₅ uA₆ uB uE uV uG

namespace PFunctor

namespace Lens

/-- Bifunctorial action of parallel sum on polynomial lenses. -/
def parallelSumMap
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (left : Lens P R) (right : Lens Q V) : Lens (P ∥ Q) (R ∥ V) where
  toFunA
    | .left a => .left (left.toFunA a)
    | .right b => .right (right.toFunA b)
    | .both a b => .both (left.toFunA a) (right.toFunA b)
  toFunB operation answer := match operation with
    | .left a => left.toFunB a answer
    | .right b => right.toFunB b answer
    | .both a b => (left.toFunB a answer.1, right.toFunB b answer.2)

@[simp] theorem parallelSumMap_toFunA_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (left : Lens P R) (right : Lens Q V) (a : P.A) :
    (parallelSumMap left right).toFunA (.left a) =
      .left (left.toFunA a) := rfl

@[simp] theorem parallelSumMap_toFunA_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (left : Lens P R) (right : Lens Q V) (b : Q.A) :
    (parallelSumMap left right).toFunA (.right b) =
      .right (right.toFunA b) := rfl

@[simp] theorem parallelSumMap_toFunA_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (left : Lens P R) (right : Lens Q V) (a : P.A) (b : Q.A) :
    (parallelSumMap left right).toFunA (.both a b) =
      .both (left.toFunA a) (right.toFunA b) := rfl

@[simp] theorem parallelSumMap_id
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    parallelSumMap (Lens.id P) (Lens.id Q) = Lens.id (P ∥ Q) := by
  ext operation answer
  · cases operation <;> rfl
  · cases operation <;> rfl

theorem parallelSumMap_comp
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {W : PFunctor.{uA₅, uB}} {X : PFunctor.{uA₆, uB}}
    (secondLeft : Lens R W) (secondRight : Lens V X)
    (firstLeft : Lens P R) (firstRight : Lens Q V) :
    parallelSumMap secondLeft secondRight ∘ₗ
        parallelSumMap firstLeft firstRight =
      parallelSumMap (secondLeft ∘ₗ firstLeft)
        (secondRight ∘ₗ firstRight) := by
  ext operation answer
  · cases operation <;> rfl
  · cases operation <;> rfl

/-- Embed the left interface into its one-or-both parallel sum. -/
def parallelSumLeft (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens P (P ∥ Q) where
  toFunA := .left
  toFunB := fun _ => id

/-- Embed the right interface into its one-or-both parallel sum. -/
def parallelSumRight (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens Q (P ∥ Q) where
  toFunA := .right
  toFunB := fun _ => id

@[simp]
theorem parallelSumLeft_toFunA
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (parallelSumLeft P Q).toFunA a = .left a :=
  rfl

@[simp]
theorem parallelSumLeft_toFunB
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (a : P.A) (answer : (P ∥ Q).B (.left a)) :
    (parallelSumLeft P Q).toFunB a answer = answer :=
  rfl

@[simp]
theorem parallelSumRight_toFunA
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (b : Q.A) :
    (parallelSumRight P Q).toFunA b = .right b :=
  rfl

@[simp]
theorem parallelSumRight_toFunB
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (b : Q.A) (answer : (P ∥ Q).B (.right b)) :
    (parallelSumRight P Q).toFunB b answer = answer :=
  rfl

/-! ## Symmetric-monoidal structural lenses -/

/-- Right unitor for parallel sum, viewed as a lens. -/
def parallelSumZero (P : PFunctor.{uA₁, uB}) :
    Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P :=
  (PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.parallelSumZero P)).toLens

/-- Left unitor for parallel sum, viewed as a lens. -/
def zeroParallelSum (P : PFunctor.{uA₁, uB}) :
    Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P :=
  (PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.zeroParallelSum P)).toLens

/-- Braiding for parallel sum, viewed as a lens. -/
def parallelSumComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Lens (P ∥ Q) (Q ∥ P) :=
  (PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.parallelSumComm P Q)).toLens

/-- Associator for parallel sum, viewed as a lens. -/
def parallelSumAssoc
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (R : PFunctor.{uA₃, uB}) : Lens ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R)) :=
  (PFunctor.Equiv.toLensEquiv
    (PFunctor.Equiv.parallelSumAssoc P Q R)).toLens

@[simp] theorem parallelSumComm_involutive
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    parallelSumComm Q P ∘ₗ parallelSumComm P Q = Lens.id (P ∥ Q) := by
  ext operation answer
  · cases operation <;> rfl
  · cases operation <;> rfl

theorem parallelSumComm_natural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (left : Lens P R) (right : Lens Q V) :
    parallelSumComm R V ∘ₗ parallelSumMap left right =
      parallelSumMap right left ∘ₗ parallelSumComm P Q := by
  ext operation answer
  · cases operation <;> rfl
  · cases operation <;> rfl

/-- Naturality of the right unitor. -/
theorem parallelSumZero_natural
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    (map : Lens P R) :
    (parallelSumZero R :
        Lens (R ∥ (0 : PFunctor.{uA₄, uB})) R) ∘ₗ
        parallelSumMap map (Lens.id (0 : PFunctor.{uA₄, uB})) =
      map ∘ₗ
        (parallelSumZero P :
          Lens (P ∥ (0 : PFunctor.{uA₄, uB})) P) := by
  ext operation answer
  · cases operation with
    | left operation => rfl
    | right operation => exact PEmpty.elim operation
    | both leftOperation rightOperation => exact PEmpty.elim rightOperation
  · cases operation with
    | left operation => rfl
    | right operation => exact PEmpty.elim operation
    | both leftOperation rightOperation => exact PEmpty.elim rightOperation

/-- Naturality of the left unitor. -/
theorem zeroParallelSum_natural
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    (map : Lens P R) :
    (zeroParallelSum R :
        Lens ((0 : PFunctor.{uA₄, uB}) ∥ R) R) ∘ₗ
        parallelSumMap (Lens.id (0 : PFunctor.{uA₄, uB})) map =
      map ∘ₗ
        (zeroParallelSum P :
          Lens ((0 : PFunctor.{uA₄, uB}) ∥ P) P) := by
  ext operation answer
  · cases operation with
    | left operation => exact PEmpty.elim operation
    | right operation => rfl
    | both leftOperation rightOperation => exact PEmpty.elim leftOperation
  · cases operation with
    | left operation => exact PEmpty.elim operation
    | right operation => rfl
    | both leftOperation rightOperation => exact PEmpty.elim leftOperation

theorem parallelSumAssoc_natural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    {P' : PFunctor.{uA₄, uB}} {Q' : PFunctor.{uA₅, uB}}
    {R' : PFunctor.{uA₆, uB}}
    (left : Lens P P') (middle : Lens Q Q') (right : Lens R R') :
    parallelSumAssoc P' Q' R' ∘ₗ
        parallelSumMap (parallelSumMap left middle) right =
      parallelSumMap left (parallelSumMap middle right) ∘ₗ
        parallelSumAssoc P Q R := by
  ext operation answer
  · cases operation with
    | left operation => cases operation <;> rfl
    | right operation => rfl
    | both operation rightOperation => cases operation <;> rfl
  · cases operation with
    | left operation => cases operation <;> rfl
    | right operation => rfl
    | both operation rightOperation => cases operation <;> rfl

/-- Mac Lane's pentagon for the explicit parallel-sum associator. -/
theorem parallelSumAssoc_pentagon
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (R : PFunctor.{uA₃, uB}) (V : PFunctor.{uA₄, uB}) :
    parallelSumMap (Lens.id P) (parallelSumAssoc Q R V) ∘ₗ
        (parallelSumAssoc P (Q ∥ R) V ∘ₗ
          parallelSumMap (parallelSumAssoc P Q R) (Lens.id V)) =
      parallelSumAssoc P Q (R ∥ V) ∘ₗ
        parallelSumAssoc (P ∥ Q) R V := by
  ext operation answer
  all_goals
    cases operation with
    | left pqr =>
        cases pqr with
        | left pq => cases pq <;> rfl
        | right r => rfl
        | both pq r => cases pq <;> rfl
    | right v => rfl
    | both pqr v =>
        cases pqr with
        | left pq => cases pq <;> rfl
        | right r => rfl
        | both pq r => cases pq <;> rfl

/-- The braiding and associator satisfy the symmetric-monoidal hexagon.  The
opposite hexagon follows from this equation and braiding involutivity. -/
theorem parallelSum_hexagon
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
    (R : PFunctor.{uA₃, uB}) :
    parallelSumAssoc Q R P ∘ₗ
        (parallelSumComm P (Q ∥ R) ∘ₗ parallelSumAssoc P Q R) =
      parallelSumMap (Lens.id Q) (parallelSumComm P R) ∘ₗ
        (parallelSumAssoc Q P R ∘ₗ
          parallelSumMap (parallelSumComm P Q) (Lens.id R)) := by
  ext operation answer
  all_goals
    cases operation with
    | left operation => cases operation <;> rfl
    | right operation => rfl
    | both operation rightOperation => cases operation <;> rfl

/-- Triangle coherence for the explicit unitors and associator. -/
theorem parallelSum_triangle
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    parallelSumMap
        (parallelSumZero P :
          Lens (P ∥ (0 : PFunctor.{uA₄, uB})) P)
        (Lens.id Q) =
      parallelSumMap (Lens.id P)
          (zeroParallelSum Q :
            Lens ((0 : PFunctor.{uA₄, uB}) ∥ Q) Q) ∘ₗ
        parallelSumAssoc P (0 : PFunctor.{uA₄, uB}) Q := by
  ext operation answer
  all_goals
    cases operation with
    | left pz =>
        cases pz with
        | left p => rfl
        | right z => exact PEmpty.elim z
        | both p z => exact PEmpty.elim z
    | right q => rfl
    | both pz q =>
        cases pz with
        | left p => rfl
        | right z => exact PEmpty.elim z
        | both p z => exact PEmpty.elim z

end Lens

namespace FreeM

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {E : Type uE} {F : Type uV}

/-- Regard a left program as a program over the parallel interface. -/
def left (program : FreeM P E) : FreeM (P ∥ Q) E :=
  program.mapLens (Lens.parallelSumLeft P Q)

/-- Regard a right program as a program over the parallel interface. -/
def right (program : FreeM Q E) : FreeM (P ∥ Q) E :=
  program.mapLens (Lens.parallelSumRight P Q)

@[simp]
theorem left_pure (value : E) :
    left (Q := Q) (pure value : FreeM P E) = pure value :=
  rfl

@[simp]
theorem left_liftBind (a : P.A) (next : P.B a → FreeM P E) :
    left (Q := Q) ((FreeM.lift a).bind next) =
      @FreeM.liftBind (P ∥ Q) E (ParallelChoice.left a)
        (fun answer => left (Q := Q) (next answer)) :=
  rfl

@[simp]
theorem right_pure (value : E) :
    right (P := P) (pure value : FreeM Q E) = pure value :=
  rfl

@[simp]
theorem right_liftBind (b : Q.A) (next : Q.B b → FreeM Q E) :
    right (P := P) ((FreeM.lift b).bind next) =
      @FreeM.liftBind (P ∥ Q) E (ParallelChoice.right b)
        (fun answer => right (P := P) (next answer)) :=
  rfl

/-- Continue parallel execution after the left program has returned.  The
remaining right operations are embedded one-sidedly. -/
def parallelAfterLeftReturn (x : E) :
    FreeM Q F → FreeM (P ∥ Q) (E × F)
  | .pure y => .pure (x, y)
  | .liftBind b next =>
      .liftBind (.right b) fun answer =>
        parallelAfterLeftReturn x (next answer)

/-- Execute two free programs in parallel, emitting a one-sided operation
when only one side is blocked and a joint operation when both are blocked. -/
def parallel : FreeM P E → FreeM Q F → FreeM (P ∥ Q) (E × F)
  | .pure x, rightProgram => parallelAfterLeftReturn x rightProgram
  | .liftBind a next, rightProgram =>
      match rightProgram with
      | .pure y =>
          .liftBind (.left a) fun answer => parallel (next answer) (.pure y)
      | .liftBind b nextQ =>
          .liftBind (.both a b) fun answer =>
            parallel (next answer.1) (nextQ answer.2)

@[simp]
theorem parallel_pure_pure (x : E) (y : F) :
    parallel (P := P) (Q := Q) (pure x) (pure y) = pure (x, y) :=
  rfl

@[simp]
theorem parallel_liftBind_pure
    (a : P.A) (next : P.B a → FreeM P E) (y : F) :
    parallel (Q := Q) ((FreeM.lift a).bind next) (pure y) =
      .liftBind (.left a) fun answer => parallel (Q := Q) (next answer) (.pure y) :=
  rfl

@[simp]
theorem parallel_pure_liftBind
    (x : E) (b : Q.A) (next : Q.B b → FreeM Q F) :
    parallel (P := P) (pure x) ((FreeM.lift b).bind next) =
      .liftBind (.right b) fun answer => parallel (P := P) (.pure x) (next answer) :=
  rfl

@[simp]
theorem parallel_liftBind_liftBind
    (a : P.A) (nextP : P.B a → FreeM P E)
    (b : Q.A) (nextQ : Q.B b → FreeM Q F) :
    parallel ((FreeM.lift a).bind nextP) ((FreeM.lift b).bind nextQ) =
      .liftBind (.both a b) fun answer =>
        parallel (nextP answer.1) (nextQ answer.2) :=
  rfl

/-! ## Symmetric-monoidal program laws -/

/-- Swapping the interface and result components commutes with lockstep
parallel execution. -/
theorem parallel_comm
    (leftProgram : FreeM P E) (rightProgram : FreeM Q F) :
    FreeM.map (fun result => (result.2, result.1))
        ((FreeM.parallel leftProgram rightProgram).mapLens
          (Lens.parallelSumComm P Q)) =
      FreeM.parallel rightProgram leftProgram := by
  induction leftProgram generalizing rightProgram with
  | pure leftValue =>
      induction rightProgram with
      | pure rightValue => rfl
      | lift_bind operation next ih =>
          exact congrArg
            (@FreeM.liftBind (Q ∥ P) (F × E) (.left operation)) (funext ih)
  | lift_bind operation next ih =>
      cases rightProgram with
      | pure rightValue =>
          exact congrArg
            (@FreeM.liftBind (Q ∥ P) (F × E) (.right operation))
            (funext fun answer => ih answer (.pure rightValue))
      | liftBind rightOperation rightNext =>
          exact congrArg
            (@FreeM.liftBind (Q ∥ P) (F × E)
              (.both rightOperation operation))
            (funext fun answer =>
              ih answer.2 (rightNext answer.1))

/-- The zero interface with its unique pure program is the right unit for
parallel execution. -/
theorem parallel_pureUnit_right (program : FreeM P E) :
    FreeM.map Prod.fst
        ((FreeM.parallel program (FreeM.pure PUnit.unit :
            FreeM (0 : PFunctor.{uA₂, uB}) PUnit)).mapLens
          (Lens.parallelSumZero P)) =
      program := by
  induction program with
  | pure value => rfl
  | lift_bind operation next ih =>
      exact congrArg (FreeM.liftBind operation) (funext ih)

/-- The zero interface with its unique pure program is the left unit for
parallel execution. -/
theorem parallel_pureUnit_left (program : FreeM P E) :
    FreeM.map Prod.snd
        ((FreeM.parallel
            (FreeM.pure PUnit.unit : FreeM (0 : PFunctor.{uA₂, uB}) PUnit)
            program).mapLens (Lens.zeroParallelSum P)) =
      program := by
  induction program with
  | pure value => rfl
  | lift_bind operation next ih =>
      exact congrArg (FreeM.liftBind operation) (funext ih)

/-- Reassociating the interface and result products commutes with lockstep
parallel execution. -/
theorem parallel_assoc
    {R : PFunctor.{uA₃, uB}} {G : Type uG}
    (leftProgram : FreeM P E) (middleProgram : FreeM Q F)
    (rightProgram : FreeM R G) :
    FreeM.map (fun result => (result.1.1, (result.1.2, result.2)))
        ((FreeM.parallel (FreeM.parallel leftProgram middleProgram)
            rightProgram).mapLens (Lens.parallelSumAssoc P Q R)) =
      FreeM.parallel leftProgram
        (FreeM.parallel middleProgram rightProgram) := by
  induction leftProgram generalizing middleProgram rightProgram with
  | pure leftValue =>
      induction middleProgram generalizing rightProgram with
      | pure middleValue =>
          induction rightProgram with
          | pure rightValue => rfl
          | lift_bind operation next ih =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.right (.right operation))) (funext ih)
      | lift_bind operation next ih =>
          cases rightProgram with
          | pure rightValue =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.right (.left operation)))
                (funext fun answer => ih answer (.pure rightValue))
          | liftBind rightOperation rightNext =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.right (.both operation rightOperation)))
                (funext fun answer =>
                  ih answer.1 (rightNext answer.2))
  | lift_bind operation next ih =>
      cases middleProgram with
      | pure middleValue =>
          cases rightProgram with
          | pure rightValue =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.left operation))
                (funext fun answer =>
                  ih answer (.pure middleValue) (.pure rightValue))
          | liftBind rightOperation rightNext =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.both operation (.right rightOperation)))
                (funext fun answer =>
                  ih answer.1 (.pure middleValue) (rightNext answer.2))
      | liftBind middleOperation middleNext =>
          cases rightProgram with
          | pure rightValue =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.both operation (.left middleOperation)))
                (funext fun answer =>
                  ih answer.1 (middleNext answer.2) (.pure rightValue))
          | liftBind rightOperation rightNext =>
              exact congrArg
                (@FreeM.liftBind (P ∥ (Q ∥ R)) (E × (F × G))
                  (.both operation (.both middleOperation rightOperation)))
                (funext fun answer =>
                  ih answer.1 (middleNext answer.2.1)
                    (rightNext answer.2.2))

end FreeM

namespace Handler

/-- Combine two free handlers pointwise over one-or-both interfaces. -/
def parallel
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) :
    Handler (FreeM (R ∥ V)) (P ∥ Q)
  | .left a => FreeM.left (Q := V) (leftHandler a)
  | .right b => FreeM.right (P := R) (rightHandler b)
  | .both a b => FreeM.parallel (leftHandler a) (rightHandler b)

@[simp]
theorem parallel_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) (a : P.A) :
    parallel leftHandler rightHandler (.left a) =
      FreeM.left (Q := V) (leftHandler a) :=
  rfl

@[simp]
theorem parallel_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) (b : Q.A) :
    parallel leftHandler rightHandler (.right b) =
      FreeM.right (P := R) (rightHandler b) :=
  rfl

@[simp]
theorem parallel_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) (a : P.A) (b : Q.A) :
    parallel leftHandler rightHandler (.both a b) =
      FreeM.parallel (leftHandler a) (rightHandler b) :=
  rfl

end Handler

namespace FreeM

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {E F : Type uB}

/-! ## Naturality under free-handler interpretation -/

theorem left_liftM
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (program : FreeM P E) (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) :
    (FreeM.left (Q := Q) program).liftM
        (Handler.parallel leftHandler rightHandler) =
      FreeM.left (Q := V) (program.liftM leftHandler) := by
  induction program with
  | pure _ => rfl
  | lift_bind operation next ih =>
      change
        FreeM.bind (FreeM.left (Q := V) (leftHandler operation))
            (fun answer =>
              (FreeM.left (Q := Q) (next answer)).liftM
                (Handler.parallel leftHandler rightHandler)) =
          FreeM.left (Q := V)
            (FreeM.bind (leftHandler operation)
              (fun answer => (next answer).liftM leftHandler))
      simp only [left, FreeM.mapLens_bind]
      congr
      funext answer
      exact ih answer

theorem right_liftM
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (program : FreeM Q E) (leftHandler : Handler (FreeM R) P)
    (rightHandler : Handler (FreeM V) Q) :
    (FreeM.right (P := P) program).liftM
        (Handler.parallel leftHandler rightHandler) =
      FreeM.right (P := R) (program.liftM rightHandler) := by
  induction program with
  | pure _ => rfl
  | lift_bind operation next ih =>
      change
        FreeM.bind (FreeM.right (P := R) (rightHandler operation))
            (fun answer =>
              (FreeM.right (P := P) (next answer)).liftM
                (Handler.parallel leftHandler rightHandler)) =
          FreeM.right (P := R)
            (FreeM.bind (rightHandler operation)
              (fun answer => (next answer).liftM rightHandler))
      simp only [right, FreeM.mapLens_bind]
      congr
      funext answer
      exact ih answer

end FreeM

namespace Handler

@[simp] theorem parallel_id
    (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    parallel (Handler.id P) (Handler.id Q) = Handler.id (P ∥ Q) := by
  funext operation
  cases operation <;> rfl


end Handler

end PFunctor
