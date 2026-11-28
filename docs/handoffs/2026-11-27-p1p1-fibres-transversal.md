# Handoff 2026-11-27: `p1p1-fibres-transversal`, `cycle-class-multiplicative-p1p1`

- Checked: `HodgeLadder/Tests/P1p1Fibres.lean` (48 declarations in the ledger) and `HodgeLadder/Tests/CycleClassMultiplicativeP1p1.lean` (`p1p1Fibres_cup_eq_p1p1Corner`), both imported from `HodgeLadder.lean`, standard axioms only.
- Points: ∞ = [1 : 0] is `infty` of `projective-line-point`, `inftyPoint = lineChart.symm 0` with `lineChart = projectiveChart 1 0` (coordinate x₁ / x₀). The fibres are images of the generic point of ℙ¹ under the sections `prod.lift constInfty (𝟙 _)` and `prod.lift (𝟙 _) constInfty`; the corner is `prod.lift inftyPoint inftyPoint`. No ring of an affine open of ℙ¹ × ℙ¹ is computed.
- Hypotheses: coheights 1, 1, 2 from (∞, ∞) < fibre < ⊤ and upstream's `coheight_le_complex`; `hT` on complex points; `htr` with `prodChart` of `lineChart` with itself, {∞} × ℙ¹ as coordinate 0; `hxreg`, `hwreg` from the sections being closed immersions from reduced ℙ¹ (`ker_eq_vanishingIdeal_of_isReduced`, `smooth_cycleComponentι_of_closedImmersion`).
- Title correction: the chart `openOne` (x₁ ≠ 0) misses ∞; the rung uses the chart x₀ ≠ 0. `htr` is existential in the chart, so nothing is weakened.
- `cycle-class-multiplicative-p1p1`: [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)], exact, sign +, by term from `cycleComponentSheafClass_cup_of_transversal p1p1 (d := 2)`; the `_noReg` form applies too. It holds for a zero point class as well, so it becomes a non-vacuous test once `p1p1-point-class-nonzero` is checked.
- Non-vacuity: the fibres differ, the corner is the chart origin, and the swapped coordinate order is false (`not_forall_mem_p1p1FibreFst_iff_coord_one`).
- Sign: none in either rung; the theorem's only sign is (−1)^{(2·1)(2·1)} = 1.
- Red team: `docs/sketches/p1p1-fibres-transversal.redteam.md`, pass with changes; changes 1 to 10 implemented, optional O1 and O2 done, O3 and O4 skipped.
- Timing: `P1p1Fibres` checks in about 8 s; the cup module builds in a few seconds once `HodgeLadder.Cycle.Multiplicative` is built.
- Next: `p1p1-point-class-nonzero` (H³ of the complement of (∞, ∞)), then `fibre-class-pullback` (pull back the class of the same `infty`, pr₁* before pr₂*) and `cup-positive-degree-test`.
