# Handoff 2026-11-28: `elliptic-curve-smooth`

- Checked: `HodgeLadder/Tests/EllipticCurveSmooth.lean` on the new general leaf `HodgeLadder/General/HypersurfaceSmooth.lean` (layer 0, Mathlib only); both imported from `HodgeLadder.lean`, 20 declarations in the ledger, standard axioms only.
- Result: `instance smoothOfRelativeDimension_ellipticCurve : SmoothOfRelativeDimension 1 ellipticCurve.hom`, and `Smooth ellipticCurve.hom` from it.
- General piece: one-equation Jacobian criterion. If the classes of the ∂ᵢf generate the unit ideal of R[Xᵢ] ⧸ (f), each localization away from ∂ᵢf has the submersive presentation `localizationAway.comp naive` (Jacobian ∂ᵢf · ∂ᵢf, dimension #σ − 1), so Spec (R[Xᵢ] ⧸ (f)) ⟶ Spec R is smooth of relative dimension #σ − 1 (`smoothOfRelativeDimension_spec`). No pointwise criterion and no regular-local-ring input.
- Combinations, checked by `linear_combination`: z ≠ 0, (4 − 6x²) f_x − 9xy f_y = 4 − 18x f with 4 a unit; y ≠ 0, u² h_u + (1 + uw) h_w = 1 + 3u h (from Euler's relation, 2w = 3h − u h_u − w h_w).
- Assembly: smoothness of relative dimension one is local on the source over the two chart opens (`ellipticCurve_chart_cover`); on each, the chart iso composed with the inclusion and the structure map is Spec of ℂ → ℂ[x, y] ⧸ (f) (`ellipticCurveChart*_inv_ι`, `chart_toSpec`), and the iso contributes relative dimension 0.
- Tests: the cusp y² = x³ fails the hypothesis (`cusp_span_pderiv_ne_top`, evaluation at the origin kills both partials); Ω has rank one on the nonzero localization of the chart z ≠ 0 away from 2y (`rank_kaehlerDifferential_affineChartAway`, red team optional change 6).
- Red team: `docs/sketches/elliptic-curve-smooth.redteam.md`, pass with changes, changes 1 to 6 applied (file moved to `HodgeLadder/Tests/`, gaps neighbours, conventions row "Relative dimension of a one-equation presentation").
- Signs: none.
- Timing: each file elaborates in about 5 s.
- Next: `elliptic-curve-integral`, then `elliptic-curve-witness`.
