# Handoff 2026-11-26: `affine-chart-analytic`

- Checked: for X smooth of relative dimension d over ℂ, an open U and e : `openScheme X U ≅ 𝔸^d` in `Over (Spec ℂ)`, the algebraic chart `affineChart X U e` lies in `IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)` for upstream's charted space (`affineChart_mem_maximalAtlas`, `HodgeLadder/Normalization/AffineChart.lean`). Coordinate m is `AffineSpace.coord m` pulled back along e, with no conjugation. `affineChart_compatible_localChart` states compatibility with every `localChart` in both directions.
- Proof, about 75 lines:
  - The chart's coordinates are evaluations of regular functions on U (`affineChart_apply_eq_evaluate`), analytic through upstream's `analyticAt_localChart_symm_evaluate`.
  - The coordinates of `localChart`, pulled back to 𝔸^d, are analytic by `analyticAt_evaluate_affineSpaceEquiv_symm`, the red team's 30-line lemma, which is listed in `docs/gaps.md`.
  - Mathlib's `mem_maximalAtlas_of_contMDiffOn` concludes.
- Open-immersion form (red-team change A): `openImmersionChart`, `openImmersionChart_symm`, `openImmersionChart_mem_maximalAtlas`.
- New rung `affine-chart-analytic-p2`, checked, in `HodgeLadder/Tests/ProjectiveChart.lean` (change D, so the Normalization module imports no `Tests` or port module):
  - The standard chart xᵢ ≠ 0 of ℙⁿ is in the maximal atlas.
  - `projectiveChart_symm_underlying` and `projectiveChart_symm_mem_U_iff`: the inverse chart at v is the point with homogeneous coordinates `Fin.insertNth i 1 v`. Both proofs follow the red team's.
- New open rung `affine-chart-conj-test` (change F): the conjugated ℙ¹ chart is outside the atlas. Its statement is elaborated in the ledger note; it is not proved.
- Trap: `rw [hsymm]` with a ∀-equation for `φ.symm` rewrites the base point of `localEtaleCoordinates` first and fails on the motive; `rw [hsymm u]` works.
- Not done: `p2-lines-transversal` still lists `affine-chart-analytic` only in `depends_on`. The instance it reads is now in `affine-chart-analytic-p2`.
- Next: `p2-lines-transversal`, starting from `projectiveChart 2 2`, `projectivePlane_chart_mem_maximalAtlas 2` and `projectiveChart_symm_mem_U_iff`.
