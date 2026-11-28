# Handoff 2026-11-27: `complex-points-prod`

- Checked: `HodgeLadder/General/ComplexPointProd.lean` (homeomorphism, instances, general lemmas) and `HodgeLadder/Normalization/ProductChart.lean` (charts), both imported from `HodgeLadder.lean`, 19 declarations in the ledger, standard axioms only. Ledger `module` is the chart module, which imports the general one.
- Homeomorphism: `pointProdHomeomorph : ComplexPoint (X ⨯ Y) ≃ₜ ComplexPoint X × ComplexPoint Y` for every X, Y in `Over (Spec ℂ)`, no finiteness hypothesis; map and inverse pinned by `rfl` to `(map prod.fst, map prod.snd)` and `prod.lift`.
- Charts: `prodChart_mem_maximalAtlas`, first factor first through `Fin.append`; nonvacuity `prodChart_localChart_mem_maximalAtlas` with upstream's charts at a and b.
- Red team (`docs/sketches/complex-points-prod.redteam.md`, pass with changes): changes 1 to 8 done. The split follows section 10; the general module also imports upstream `ComplexPoint.AffineSpace` (a private import of `AffineScheme`, needed for `continuous_evaluate_top`).
- Optional changes done: `isAffine_prod` (the named instance), `smooth_prod : Smooth (X ⨯ Y).hom`, `pointTensorHomeomorph` for Mathlib's `X ⊗ Y` with its projection pin. With `smooth_prod` the last sentence of the requested `p1p1-witness` note was changed: `Smooth (projectiveLine ⨯ projectiveLine).hom` is now inferred (checked in scratch).
- Not done: the ℙ² ⨯ ℙ² Hausdorff witness (needs a test module); no new conjugated-chart rung, since `affine-chart-conj-test` already holds that statement.
- Timing: each module checks in about 5 to 7 s.
- Next: `p1p1-witness` (integrality and projectivity of ℙ¹ ⨯ ℙ¹), then `p1p1-fibres-transversal`.
