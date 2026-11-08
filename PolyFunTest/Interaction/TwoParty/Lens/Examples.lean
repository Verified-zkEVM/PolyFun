/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.PublicCoin
public import PolyFun.PFunctor.Free.Path.AppendAlong
public import PolyFun.PFunctor.Free.Replicate

/-!
# Runtime moves, shape paths, and replay

Challenge payloads remain in transcripts even when the lens erases them from shape.
These ordinary-import regressions also exercise dependent terminal outputs and path transports.
-/

@[expose] public section

namespace Interaction.TwoParty.Lens.Tests
open PFunctor
open FreeM (Path PathAlong projectPathAlong)

inductive Position where
  | message
  | challenge

/-- Messages branch, while challenges have just one shape branch. -/
abbrev protocolPoly : PFunctor := ⟨Position, fun
  | .message => Bool
  | .challenge => PUnit⟩

abbrev protocolLens : PFunctor.Lens protocolPoly rolePoly where
  toFunA
    | .message => (.sender, Bool)
    | .challenge => (.receiver, Bool)
  toFunB
    | .message => id
    | .challenge => fun _ => PUnit.unit

abbrev challengeTree : FreeM protocolPoly PUnit.{1} := .liftBind .challenge (fun _ => .pure ⟨⟩)

abbrev challengePath (b : Bool) : PathAlong protocolLens challengeTree := ⟨b, ⟨⟩⟩

example : projectPathAlong protocolLens challengeTree (challengePath false) =
    projectPathAlong protocolLens challengeTree (challengePath true) := rfl

example : challengePath false ≠ challengePath true := by
  intro h
  have : false = true := congrArg Sigma.fst h
  cases this

/-- The output type varies with the recorded challenge. -/
abbrev ChallengeOutput (tr : PathAlong protocolLens challengeTree) : Type :=
  match (show Bool from tr.1) with
  | true => Nat
  | false => Bool

abbrev challengeProver : Focal protocolLens Id challengeTree ChallengeOutput :=
  fun b => match b with
  | true => (7 : Nat)
  | false => false

abbrev challengeCounterpart (b : Bool) :
    Counterpart protocolLens Id challengeTree (fun _ => Bool) :=
  ⟨b, b⟩

example : run challengeTree challengeProver (challengeCounterpart true) =
    ⟨challengePath true, (7 : Nat), true⟩ := by
  rw [run_node]
  change (do
    let r ← run (l := protocolLens) (m := Id) (.pure PUnit.unit)
      (OutP := fun _ => Nat) (OutC := fun _ => Bool) (pure 7) (pure true)
    pure (⟨challengePath true, r.2⟩ :
      (tr : PathAlong protocolLens challengeTree) × ChallengeOutput tr × Bool)) = _
  simp only [FreeM.pure_eq_pure, run_done]
  rfl

/-- Replay follows a recorded challenge although its sampler has no result. -/
abbrev failingSampler : PublicCoinCounterpart protocolLens Option challengeTree (fun _ => Bool) :=
  (none, fun b => some b)

example : PublicCoinCounterpart.replay failingSampler (challengePath true) = some true := rfl

example : PublicCoinCounterpart.toCounterpart failingSampler = none := rfl

/-- A public message genuinely changes the suffix tree. -/
abbrev messageTree : FreeM protocolPoly PUnit.{1} := .liftBind .message (fun _ => .pure ⟨⟩)

abbrev suffix : Path messageTree → FreeM protocolPoly PUnit.{1}
  | ⟨false, _⟩ => .pure ⟨⟩
  | ⟨true, _⟩ => challengeTree

abbrev fullPath : PathAlong protocolLens (messageTree.append suffix) := ⟨true, true, ⟨⟩⟩

abbrev prefixPath : PathAlong protocolLens messageTree := ⟨true, ⟨⟩⟩

example : PathAlong.split protocolLens messageTree suffix fullPath =
    ⟨prefixPath, challengePath true⟩ := rfl

example : PathAlong.append protocolLens messageTree suffix prefixPath (challengePath true) =
    fullPath := rfl

/-- Separate lifted output families retain both payloads. -/
example : PathAlong.liftAppendProd protocolLens messageTree suffix
    (fun _ _ => Nat) (fun _ _ => Bool) fullPath
    (PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Nat × Bool)
      prefixPath (challengePath true) (9, true)) =
      (PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Nat)
        prefixPath (challengePath true) 9,
       PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Bool)
        prefixPath (challengePath true) true) :=
  rfl

example : PathAlong.liftAppendProdMk protocolLens messageTree suffix
    (fun _ _ => Nat) (fun _ _ => Bool) fullPath
    (PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Nat)
        prefixPath (challengePath true) 9,
     PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Bool)
        prefixPath (challengePath true) true) =
    PathAlong.packAppend protocolLens messageTree suffix (fun _ _ => Nat × Bool)
      prefixPath (challengePath true) (9, true) := rfl

example : PathAlong.replicateJoin protocolLens PUnit.unit challengeTree 0 Fin.elim0 =
    PUnit.unit := rfl

example : PathAlong.replicateSplit protocolLens PUnit.unit challengeTree 3
    (PathAlong.replicateJoin protocolLens PUnit.unit challengeTree 3
      (fun i => challengePath (i.val == 1))) 1 = challengePath true := by
  rw [PathAlong.replicateSplit_replicateJoin]
  rfl

end Interaction.TwoParty.Lens.Tests
