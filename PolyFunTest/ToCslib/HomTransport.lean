/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.IsMonadHom.List
public import ToCslib.Control.Monad.HomTransport
public import ToCslib.Control.ForIn

/-!
# Canaries for loop transport and effect-free containers

The staged `forIn` transport lemmas and cslib's own `IsMonadHom.map_list*` family are
instantiated at one concrete monad morphism, and the `Option` / `Vector` `PureForIn` instances
are exercised through the generic container lemma.
-/

public section

namespace PolyFunTest.ToCslib.HomTransport

/-- Embedding `Id` into `Option` is a monad morphism. -/
theorem isMonadHom_idToOption :
    Cslib.IsMonadHom Id Option fun {α} (x : Id α) => (pure x.run : Option α) :=
  .mk' (fun _ => rfl) (fun _ _ => rfl)

/-- The staged `forIn` transport. -/
example (l : List Nat) (init : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    (pure (forIn l init f).run : Option Nat) = forIn l init fun a b => pure (f a b).run :=
  isMonadHom_idToOption.map_listForIn l init f

example (l : List Nat) (init : Nat) (f : (a : Nat) → a ∈ l → Nat → Id (ForInStep Nat)) :
    (pure (forIn' l init f).run : Option Nat) = forIn' l init fun a h b => pure (f a h b).run :=
  isMonadHom_idToOption.map_listForIn' l init f

/-- cslib's list transport, reached through the same morphism. -/
example (l : List Nat) (f : Nat → Id PUnit) :
    (pure (l.forM f).run : Option PUnit) = l.forM ((fun x => pure x.run) ∘ f) :=
  isMonadHom_idToOption.map_listForM l f

example (f : Nat → Nat → Id Nat) (init : Nat) (l : List Nat) :
    (pure (l.foldlM f init).run : Option Nat) = l.foldlM (fun s a => pure (f s a).run) init :=
  isMonadHom_idToOption.map_listFoldlM f init l

example (f : Nat → Id Nat) (l : List Nat) :
    (pure (l.mapM f).run : Option (List Nat)) = l.mapM ((fun x => pure x.run) ∘ f) :=
  isMonadHom_idToOption.map_listMapM f l

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
  isMonadHom_idToOption.map_forIn_of_pureForIn o init f

/-- … and `Vector` through its array. -/
example (v : Vector Nat 3) (init : Nat) (f : Nat → Nat → Id (ForInStep Nat)) :
    (pure (forIn v init f).run : Option Nat) = forIn v init fun a b => pure (f a b).run :=
  isMonadHom_idToOption.map_forIn_of_pureForIn v init f

/-- The membership-carrying container lemma, on `Option`. -/
example (o : Option Nat) (init : Nat) (f : (a : Nat) → a ∈ o → Nat → Id (ForInStep Nat)) :
    (pure (forIn' o init f).run : Option Nat) = forIn' o init fun a h b => pure (f a h b).run :=
  isMonadHom_idToOption.map_forIn'_of_pureForIn' o init f

end PolyFunTest.ToCslib.HomTransport
