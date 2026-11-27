# Handoff 2026-11-27: `complex-point-nonempty`

- Checked: `HodgeLadder/General/ComplexPoint.lean` (three lemmas, four light imports, no `Other` and no ladder module) and `HodgeLadder/Tests/ComplexPointNonempty.lean` (corollaries), both imported from `HodgeLadder.lean`; 10 declarations in the ledger, standard axioms only.
- Statement: `nonempty_complexPoint (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] : Nonempty (ComplexPoint X)`, as posted. General form `nonempty_complexPoint_of_locallyOfFiniteType` under `[Nonempty X.left] [LocallyOfFiniteType X.hom]`, sharp by `nonempty_complexPoint_iff` and `Tests.not_nonempty_complexPoint_empty`.
- Route: `LocallyOfFiniteType.jacobsonSpace`, then `nonempty_inter_closedPoints` on `Set.univ`, then Mathlib's `pointEquivClosedPoint` (Nullstellensatz, `ℂ` algebraically closed) gives a section of `X.hom`; seven lines. Mathlib lacked nothing.
- Upstream overlap: `AlgebraicGeometry.ComplexPoint.instNonemptyComplexPoint` proves the posted statement by `inferInstance` and is in the root's closure through `HodgeLadder.Tests.CodimensionZero`. The local copy is kept for `Nonempty X.left`, the iff and the light import; gaps row says what to check at a pin bump.
- Corollaries: six primed forms of the `de-rham-unit-nonzero` general tests and `wedgeSheaf_ne_zero`, the originals with `[Nonempty (ComplexPoint X)]` deleted. The checked Tests file is untouched.
- Red team: `docs/sketches/complex-point-nonempty.redteam.md`, pass with changes. Changes 1 to 4 done (false `Other` claim corrected, module split, gaps row, ledger note); optional 5 and 6 adopted (empty-scheme check, docstring note on the primed forms).
- Timing: each file checks in about 4 s with `lake env lean`; `lake build` of the General module 5 s; full `tools/check.py` about 21 s.
- Next: none for this rung. It is not needed for the ladder.
