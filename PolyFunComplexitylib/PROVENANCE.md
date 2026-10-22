# complexitylib provenance

- Upstream: <https://github.com/cslib-community/complexitylib>
- Revision: `62bbf525e2d7edce00dc8b6c79a52040223c5bed` (`main`, 2026-10-22)
- Upstream toolchain at that revision: Lean `v4.36.0-rc1`
- cslib: `8a20ea3dd61a1ed03ec9b5936f8234b5b1dd32f6`, complexitylib's own pin
- Mathlib: `v4.36.0-rc1` (`625d8914199bc567cca9b91f90e8e5afafa5ae51`), through cslib

PolyFun is built at the same revisions, so no requirement overrides another and no dependency
source is patched. The whole `Complexity` library compiles at these pins.

complexitylib publishes no code tags and follows cslib `main`; pin a full commit and move it
together with PolyFun's cslib and Mathlib revisions.

## Ported material

`Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumElim` in `Backend/StepClass.lean` reproduces the
proof of complexitylib's private lemma `sumElim` in
`Complexity/Computability/Complexity/Problems/ThreeSAT.lean` (Samuel Schlesinger, Apache-2.0),
which is credited on the file's `Authors:` line. `sumElimCtx` adapts the same proof to a retained
context.
