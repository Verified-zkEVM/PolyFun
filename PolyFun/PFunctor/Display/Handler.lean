/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Free

/-!
# Displayed handlers between polynomial interfaces

This file supplies the display-level counterpart of a free-monad handler. If

```text
f : (a : P.A) → FreeM Q (P.B a)
```

implements every operation of `P` as a `Q`-program, then
`Display.Handler S T f` implements every displayed position of `S` as
displayed data over that program, using the target display `T`.

This is the intrinsic PolyFun form of the paper's dependent-polynomial
morphism. It is named after the existing `FreeM.liftM` handler API rather than
introducing a paper-specific arrow alias. `Display.liftM` is its free extension,
and `Handler.comp` is displayed Kleisli composition.
-/

@[expose] public section

universe uA uA' uA'' uA''' uB uB' uC uD uC' uD' uC'' uD'' uC''' uD''' uF uG

namespace PFunctor
namespace Display

variable {P : PFunctor.{uA, uB}}

/-- A displayed implementation of a free-monad handler.

The source and target response universes are independent. In composition,
only the source and intermediate interfaces must share a response universe;
the final target remains independent. -/
abbrev Handler
    {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : (a : P.A) → FreeM Q (P.B a)) :=
  (a : P.A) → (c : S.position a) →
    FreeM.Displayed (T.toDisplayedAlgebra (S.direction a c)) (f a)

/-- Extend a displayed handler recursively over a free source program. This
maps the base tree with `FreeM.liftM` and its displayed data in lockstep. -/
def liftM
    {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (f : (a : P.A) → FreeM Q (P.B a))
    (df : Handler S T f) :
    FreeM.Displayed (T.toDisplayedAlgebra F) (t.liftM f) :=
  match t, d with
  | .pure x, d => T.leaf F x d.down
  | .liftBind a rest, ⟨c, children⟩ =>
      T.bind (f a) (df a c) (fun b => (rest b).liftM f)
        (fun b e => S.liftM T (rest b) (children b e) f df)

@[simp]
theorem liftM_pure
    {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (x : E) (d : ULift.{max uC uB uD} (F x))
    (f : (a : P.A) → FreeM Q (P.B a)) (df : Handler S T f) :
    S.liftM T (pure x) d f df = T.leaf F x d.down :=
  rfl

@[simp]
theorem liftM_liftBind
    {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (a : P.A) (rest : P.B a → FreeM P E) (c : S.position a)
    (children : (b : P.B a) → S.direction a c b →
      FreeM.Displayed (S.toDisplayedAlgebra F) (rest b))
    (f : (a : P.A) → FreeM Q (P.B a)) (df : Handler S T f) :
    S.liftM T (FreeM.lift a >>= rest) ⟨c, children⟩ f df =
      T.bind (f a) (df a c) (fun b => (rest b).liftM f)
        (fun b e => S.liftM T (rest b) (children b e) f df) :=
  rfl

/-- Extending displayed handlers respects pointwise-compatible replacement of
the underlying handler. The transport is forced by the equality of the base
handlers. -/
theorem liftM_congr
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    {f g : (a : P.A) → FreeM Q (P.B a)}
    (h : f = g)
    (df : Handler S T f) (dg : Handler S T g)
    (hd : (a : P.A) → (c : S.position a) →
      T.transport (S.direction a c) (congrFun h a) (df a c) = dg a c) :
    T.transport F (congrArg (t.liftM ·) h) (S.liftM T t d f df) =
      S.liftM T t d g dg := by
  subst g
  have hdf : df = dg := by
    funext a c
    simpa using hd a c
  subst dg
  rfl

namespace Handler

/-- The identity displayed handler: retain every displayed position and pass
each displayed direction directly to the corresponding continuation. -/
def id (S : Display.{uA, uB, uC, uD} P) :
    Handler S S (fun a => FreeM.lift a) :=
  fun a c =>
    ⟨c, fun b d => S.leaf (S.direction a c) b d⟩

/-- Displayed Kleisli composition of handlers, in categorical order:
`second.comp first` first interprets by `first`, then by `second`.

The source and intermediate interfaces share a response universe because the
first handler returns a tree whose leaves are source responses and whose nodes
are intermediate operations. The final target's response universe remains
independent. -/
def comp
    {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {U : Display.{uA'', uB', uC'', uD''} R}
    {f : (a : P.A) → FreeM Q (P.B a)}
    {g : (a : Q.A) → FreeM R (Q.B a)}
    (second : Handler T U g) (first : Handler S T f) :
    Handler S U (fun a => (f a).liftM g) :=
  fun a c => T.liftM U (f a) (first a c) g second

@[simp]
theorem comp_apply
    {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {U : Display.{uA'', uB', uC'', uD''} R}
    {f : (a : P.A) → FreeM Q (P.B a)}
    {g : (a : Q.A) → FreeM R (Q.B a)}
    (second : Handler T U g) (first : Handler S T f)
    (a : P.A) (c : S.position a) :
    second.comp first a c = T.liftM U (f a) (first a c) g second :=
  rfl

end Handler

private theorem liftMIdEq {E : Type uB} :
    (t : FreeM P E) → t.liftM (fun a => FreeM.lift a) = t
  | .pure _ => rfl
  | .liftBind a rest =>
      congrArg (FreeM.liftBind a) (funext fun b => liftMIdEq (rest b))

/-- Extending the identity displayed handler is the identity on displayed
free trees, after transport along the corresponding base-tree identity law. -/
theorem liftM_id
    (S : Display.{uA, uB, uC, uD} P)
    {E : Type uB} {F : E → Type uF}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t) :
    S.transport F (FreeM.liftM_lift_eq_self t)
        (S.liftM S t d (fun a => FreeM.lift a) (Handler.id S)) = d := by
  induction t with
  | pure x =>
      cases d
      rfl
  | lift_bind a rest ih =>
      rcases d with ⟨c, children⟩
      simp only [FreeM.pure_bind] at children
      rw [S.transport_proof_irrel F
        (FreeM.liftM_lift_eq_self ((FreeM.lift a).bind rest))
        (liftMIdEq ((FreeM.lift a).bind rest))]
      change S.transport F (liftMIdEq (FreeM.liftBind a rest))
          ⟨c, fun b e =>
            S.liftM S (rest b) (children b e) (fun a => FreeM.lift a)
              (Handler.id S)⟩ = ⟨c, children⟩
      have htransport :
          S.transport F (liftMIdEq (FreeM.liftBind a rest))
              ⟨c, fun b e =>
                S.liftM S (rest b) (children b e) (fun a => FreeM.lift a)
                  (Handler.id S)⟩ =
            ⟨c, fun b e =>
              S.transport F (liftMIdEq (rest b))
                (S.liftM S (rest b) (children b e) (fun a => FreeM.lift a)
                  (Handler.id S))⟩ := by
        convert S.transport_liftBind F a
          (funext fun b => liftMIdEq (rest b)) c
          (fun b e =>
            S.liftM S (rest b) (children b e) (fun a => FreeM.lift a)
              (Handler.id S)) using 1
        all_goals simp [FreeM.liftBind_eq]
        all_goals congr
      rw [htransport]
      congr
      funext b e
      rw [S.transport_proof_irrel F (liftMIdEq (rest b))
        (FreeM.liftM_lift_eq_self (rest b))]
      exact ih b (children b e)

private theorem liftMBindEq
    {Q : PFunctor.{uA', uB'}}
    {E E' : Type uB}
    (f : (a : P.A) → FreeM Q (P.B a)) (g : E → FreeM P E') :
    (t : FreeM P E) →
      (t.bind g).liftM f = (t.liftM f).bind fun x => (g x).liftM f
  | .pure _ => rfl
  | .liftBind a rest =>
      (congrArg (FreeM.bind (f a))
        (funext fun b => liftMBindEq f g (rest b))).trans
      (FreeM.bind_assoc (f a) (fun b => (rest b).liftM f)
        (fun x => (g x).liftM f)).symm

/-- Displayed handler extension preserves displayed substitution, after
transport along the corresponding base-tree `FreeM.liftM_bind` law. -/
theorem liftM_bind
    {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {E E' : Type uB} {F : E → Type uF} {G : E' → Type uG}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (g : E → FreeM P E')
    (dg : (x : E) → F x → FreeM.Displayed (S.toDisplayedAlgebra G) (g x))
    (f : (a : P.A) → FreeM Q (P.B a))
    (df : Handler S T f) :
    T.transport G (FreeM.liftM_bind f t g)
        (S.liftM T (t.bind g) (S.bind t d g dg) f df) =
      T.bind (t.liftM f) (S.liftM T t d f df)
        (fun x => (g x).liftM f)
        (fun x dx => S.liftM T (g x) (dg x dx) f df) := by
  induction t with
  | pure x =>
      cases d
      rfl
  | lift_bind a rest ih =>
      rcases d with ⟨c, children⟩
      simp only [FreeM.pure_bind] at children
      rw [T.transport_proof_irrel G
        (FreeM.liftM_bind f ((FreeM.lift a).bind rest) g)
        (liftMBindEq f g ((FreeM.lift a).bind rest))]
      let k : P.B a → FreeM Q E := fun b => (rest b).liftM f
      let h : E → FreeM Q E' := fun x => (g x).liftM f
      let childEq : (fun b => ((rest b).bind g).liftM f) =
          (fun b => (k b).bind h) :=
        funext fun b => liftMBindEq f g (rest b)
      change T.transport G
          ((congrArg (FreeM.bind (f a)) childEq).trans
            (FreeM.bind_assoc (f a) k h).symm)
          (T.bind (f a) (df a c)
            (fun b => ((rest b).bind g).liftM f)
            (fun b e => S.liftM T ((rest b).bind g)
              (S.bind (rest b) (children b e) g dg) f df)) =
        T.bind ((f a).bind k)
          (T.bind (f a) (df a c) k
            (fun b e => S.liftM T (rest b) (children b e) f df)) h
          (fun x dx => S.liftM T (g x) (dg x dx) f df)
      have childTransport (b : P.B a) (e : S.direction a c b) :
          T.transport G (congrFun childEq b)
              (S.liftM T ((rest b).bind g)
                (S.bind (rest b) (children b e) g dg) f df) =
            T.bind (k b) (S.liftM T (rest b) (children b e) f df) h
              (fun x dx => S.liftM T (g x) (dg x dx) f df) := by
        rw [T.transport_proof_irrel G (congrFun childEq b)
          (FreeM.liftM_bind f (rest b) g)]
        exact ih b (children b e)
      calc
        _ = T.transport G (FreeM.bind_assoc (f a) k h).symm
              (T.transport G (congrArg (FreeM.bind (f a)) childEq)
                (T.bind (f a) (df a c)
                  (fun b => ((rest b).bind g).liftM f)
                  (fun b e => S.liftM T ((rest b).bind g)
                    (S.bind (rest b) (children b e) g dg) f df))) :=
          (T.transport_trans G (congrArg (FreeM.bind (f a)) childEq)
            (FreeM.bind_assoc (f a) k h).symm _).symm
        _ = T.transport G (FreeM.bind_assoc (f a) k h).symm
              (T.bind (f a) (df a c) (fun b => (k b).bind h)
                (fun b e => T.bind (k b)
                  (S.liftM T (rest b) (children b e) f df) h
                  (fun x dx => S.liftM T (g x) (dg x dx) f df))) := by
          apply congrArg (T.transport G (FreeM.bind_assoc (f a) k h).symm)
          rw [T.transport_bind]
          · change T.bind (f a) (df a c) (fun b => (k b).bind h)
                (fun b e => T.transport G (congrFun childEq b)
                  (S.liftM T ((rest b).bind g)
                    (S.bind (rest b) (children b e) g dg) f df)) =
              T.bind (f a) (df a c) (fun b => (k b).bind h)
                (fun b e => T.bind (k b)
                  (S.liftM T (rest b) (children b e) f df) h
                  (fun x dx => S.liftM T (g x) (dg x dx) f df))
            congr
            funext b e
            exact childTransport b e
          · exact childEq
        _ = _ := T.bind_assoc_symm (f a) (df a c) k
          (fun b e => S.liftM T (rest b) (children b e) f df) h
          (fun x dx => S.liftM T (g x) (dg x dx) f df)

private theorem liftMCompEq
    {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB'}}
    {E : Type uB}
    (first : (a : P.A) → FreeM Q (P.B a))
    (second : (a : Q.A) → FreeM R (Q.B a)) :
    (t : FreeM P E) →
      (t.liftM first).liftM second =
        t.liftM (fun a => (first a).liftM second)
  | .pure _ => rfl
  | .liftBind a rest =>
      (FreeM.liftM_bind second (first a) (fun b => (rest b).liftM first)).trans
      (congrArg (FreeM.bind ((first a).liftM second))
        (funext fun b => liftMCompEq first second (rest b)))

/-- Extending two displayed handlers in sequence agrees with extending their
displayed Kleisli composite, after transport along `FreeM.liftM_comp`. -/
theorem liftM_comp
    {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (U : Display.{uA'', uB', uC'', uD''} R)
    {E : Type uB} {F : E → Type uF}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedAlgebra F) t)
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first)
    (second : (a : Q.A) → FreeM R (Q.B a))
    (dsecond : Handler T U second) :
    U.transport F (FreeM.liftM_comp (P := P) (Q := Q) (R := R) t first second)
        (T.liftM U (t.liftM first) (S.liftM T t d first dfirst)
          second dsecond) =
      S.liftM U t d (fun a => (first a).liftM second)
        (dsecond.comp dfirst) := by
  induction t with
  | pure x =>
      cases d
      rfl
  | lift_bind a rest ih =>
      rcases d with ⟨c, children⟩
      simp only [FreeM.pure_bind] at children
      rw [U.transport_proof_irrel F
        (FreeM.liftM_comp ((FreeM.lift a).bind rest) first second)
        (liftMCompEq first second ((FreeM.lift a).bind rest))]
      let k : P.B a → FreeM Q E := fun b => (rest b).liftM first
      let childEq : (fun b => (k b).liftM second) =
          (fun b => (rest b).liftM fun a => (first a).liftM second) :=
        funext fun b => liftMCompEq first second (rest b)
      change U.transport F
          ((FreeM.liftM_bind second (first a) k).trans
            (congrArg (FreeM.bind ((first a).liftM second)) childEq))
          (T.liftM U ((first a).bind k)
            (T.bind (first a) (dfirst a c) k
              (fun b e => S.liftM T (rest b) (children b e) first dfirst))
            second dsecond) =
        U.bind ((first a).liftM second)
          (T.liftM U (first a) (dfirst a c) second dsecond)
          (fun b => (rest b).liftM fun a => (first a).liftM second)
          (fun b e => S.liftM U (rest b) (children b e)
            (fun a => (first a).liftM second) (dsecond.comp dfirst))
      have firstStep :
          U.transport F (FreeM.liftM_bind second (first a) k)
              (T.liftM U ((first a).bind k)
                (T.bind (first a) (dfirst a c) k
                  (fun b e => S.liftM T (rest b) (children b e) first dfirst))
                second dsecond) =
            U.bind ((first a).liftM second)
              (T.liftM U (first a) (dfirst a c) second dsecond)
              (fun b => (k b).liftM second)
              (fun b e => T.liftM U (k b)
                (S.liftM T (rest b) (children b e) first dfirst)
                second dsecond) :=
        T.liftM_bind U (first a) (dfirst a c) k
          (fun b e => S.liftM T (rest b) (children b e) first dfirst)
          second dsecond
      have childTransport (b : P.B a) (e : S.direction a c b) :
          U.transport F (congrFun childEq b)
              (T.liftM U (k b)
                (S.liftM T (rest b) (children b e) first dfirst)
                second dsecond) =
            S.liftM U (rest b) (children b e)
              (fun a => (first a).liftM second) (dsecond.comp dfirst) := by
        rw [U.transport_proof_irrel F (congrFun childEq b)
          (FreeM.liftM_comp (rest b) first second)]
        exact ih b (children b e)
      calc
        _ = U.transport F (congrArg (FreeM.bind ((first a).liftM second)) childEq)
              (U.transport F (FreeM.liftM_bind second (first a) k)
                (T.liftM U ((first a).bind k)
                  (T.bind (first a) (dfirst a c) k
                    (fun b e => S.liftM T (rest b) (children b e) first dfirst))
                  second dsecond)) :=
          (U.transport_trans F (FreeM.liftM_bind second (first a) k)
            (congrArg (FreeM.bind ((first a).liftM second)) childEq) _).symm
        _ = U.transport F (congrArg (FreeM.bind ((first a).liftM second)) childEq)
              (U.bind ((first a).liftM second)
                (T.liftM U (first a) (dfirst a c) second dsecond)
                (fun b => (k b).liftM second)
                (fun b e => T.liftM U (k b)
                  (S.liftM T (rest b) (children b e) first dfirst)
                  second dsecond)) := congrArg _ firstStep
        _ = _ := by
          rw [U.transport_bind]
          · congr
            funext b e
            exact childTransport b e
          · exact childEq

namespace Handler

/-- Left identity for displayed handler composition, stated pointwise with
the base handler's right-unit equality made explicit. -/
theorem id_comp_apply
    {Q : PFunctor.{uA', uB}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {f : (a : P.A) → FreeM Q (P.B a)}
    (first : Handler S T f) (a : P.A) (c : S.position a) :
    T.transport (S.direction a c) (FreeM.liftM_lift_eq_self (f a))
        ((Handler.id T).comp first a c) = first a c :=
  T.liftM_id (f a) (first a c)

/-- Right identity for displayed handler composition, stated pointwise with
the generator interpretation equality made explicit. -/
theorem comp_id_apply
    {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    {f : (a : P.A) → FreeM Q (P.B a)}
    (first : Handler S T f) (a : P.A) (c : S.position a) :
    T.transport (S.direction a c) (FreeM.liftM_lift f a)
        (first.comp (Handler.id S) a c) = first a c := by
  rw [T.transport_proof_irrel (S.direction a c) (FreeM.liftM_lift f a)
    (FreeM.bind_pure (f a))]
  exact T.bind_leaf (f a) (first a c)

/-- Associativity for displayed handler composition, stated pointwise with
the base free-monad composition equality made explicit. -/
theorem comp_assoc_apply
    {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB}}
    {V : PFunctor.{uA''', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {U : Display.{uA'', uB, uC'', uD''} R}
    {W : Display.{uA''', uB', uC''', uD'''} V}
    {f : (a : P.A) → FreeM Q (P.B a)}
    {g : (a : Q.A) → FreeM R (Q.B a)}
    {h : (a : R.A) → FreeM V (R.B a)}
    (first : Handler S T f) (second : Handler T U g)
    (third : Handler U W h) (a : P.A) (c : S.position a) :
    W.transport (S.direction a c)
        (FreeM.liftM_comp (P := Q) (Q := R) (R := V) (f a) g h)
        (third.comp (second.comp first) a c) =
      (third.comp second).comp first a c :=
  T.liftM_comp U W (f a) (first a c) g second h third

end Handler

end Display
end PFunctor
