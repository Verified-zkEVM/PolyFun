/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Control.Monad.HomTransport
public import ToCslib.Control.ForIn

/-!
# Canaries for loop transport and effect-free containers

The transport lemmas are instantiated at a concrete `pure`/`bind`-preserving function, and the
`Option` / `Vector` `PureForIn` instances are exercised through the generic container lemma.
-/

/-- Embedding `Id` into `Option` preserves `pure` and `bind`. -/
example (l : List Nat) (init : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    (pure (forIn l init f).run : Option Nat) = forIn l init fun a b => pure (f a b).run :=
  Cslib.map_listForIn (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) l init f

example (l : List Nat) (f : Nat → Id PUnit) :
    (pure (l.forM f).run : Option PUnit) = l.forM ((fun x => pure x.run) ∘ f) :=
  Cslib.map_listForM (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) l f

example (f : Nat → Nat → Id Nat) (init : Nat) (l : List Nat) :
    (pure (l.foldlM f init).run : Option Nat) = l.foldlM (fun s a => pure (f s a).run) init :=
  Cslib.map_listFoldlM (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) f init l

example (f : Nat → Id Nat) (l : List Nat) :
    (pure (l.mapM f).run : Option (List Nat)) = l.mapM ((fun x => pure x.run) ∘ f) :=
  Cslib.map_listMapM (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) f l

/-! ## Effect-free containers -/

example : Std.Internal.PureForIn Id (Option Nat) Nat := inferInstance
example : Std.Internal.PureForIn' Id (Option Nat) Nat := inferInstance
example : Std.Internal.PureForIn Id (Vector Nat 3) Nat := inferInstance
example : Std.Internal.PureForIn' Id (Vector Nat 3) Nat := inferInstance

example (o : Option Nat) : ForIn.toList o = o.toList := by simp
example (v : Vector Nat 3) : ForIn.toList v = v.toList := by simp

/-- The generic container lemma reaches `Option` through its new instance. -/
example (o : Option Nat) (init : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    (pure (forIn o init f).run : Option Nat) = forIn o init fun a b => pure (f a b).run :=
  Cslib.map_forIn_of_pureForIn (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) o init f

/-- … and `Vector` through its array. -/
example (v : Vector Nat 3) (init : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    (pure (forIn v init f).run : Option Nat) = forIn v init fun a b => pure (f a b).run :=
  Cslib.map_forIn_of_pureForIn (m := Id) (n := Option) (fun x => pure x.run) (fun _ => rfl) (fun _ _ => rfl) v init f
