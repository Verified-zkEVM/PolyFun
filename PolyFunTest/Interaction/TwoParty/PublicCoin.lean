/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.TwoParty.PublicCoin

/-! # Replay uses recorded challenges even when the sampler fails -/

public section

namespace Interaction.TwoParty.PublicCoinCounterpart.Test

abbrev spec : TypeTree := TypeTree.node Bool fun _ => TypeTree.done

abbrev roles : RoleDecoration spec := ⟨.receiver, fun _ => PUnit.unit⟩

abbrev Output (tr : PFunctor.FreeM.Path spec) : Type :=
  match tr.1 with | false => Bool | true => Nat

def counterpart : StrategyOver (counterpartSyntax Option) PUnit.unit spec roles Output :=
  (none, fun b => match b with | false => false | true => (7 : Nat))

example : replay counterpart ⟨true, ⟨⟩⟩ = some 7 := rfl

example : replay counterpart ⟨false, ⟨⟩⟩ = some false := rfl

example : toCounterpart counterpart = none := by
  rw [counterpart, toCounterpart_receiver]
  rfl

end Interaction.TwoParty.PublicCoinCounterpart.Test
