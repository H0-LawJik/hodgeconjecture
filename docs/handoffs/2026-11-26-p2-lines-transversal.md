# Handoff 2026-11-26: `p2-lines-transversal`

- Checked: on ℙ², L₀ = {x₀ = 0}, L₁ = {x₁ = 0} and [0 : 0 : 1] meet every hypothesis of `cycle-class-multiplicative` at a = b = 1, d = 2, in its exact form (`HodgeLadder/Tests/ProjectivePlaneLines.lean`):
  - coheights 1, 1, 2 (`coheight_planeLine`, `coheight_planeOrigin`);
  - `hT` (`planeOrigin_support_eq_inter`), the singleton form, and the scheme-level `closure_planeLine_inter` (red-team change B);
  - `htr` with `projectiveChart 2 2`, L₀ on coordinate 0 and L₁ on coordinate 1 (`planeLines_transversal`);
  - `hxreg`, `hwreg` (`planeOrigin_support_subset_smoothSupportAmbientOpen`).
- Points: images under `projectiveChartImmersion 2 2` of the primes (Y_k) (kernel of `planeLineRestrict k : ℂ[Y₀, Y₁] → ℂ[T]`) and of evaluation at 0.
- Smooth locus, about 80 lines (`cycleComponent_planeLine_mem_smoothLocus`):
  - Mathlib's `subschemeCover` chart at the affine open x₂ ≠ 0, then `preimage_smoothLocus_eq` and `smoothLocus_eq_top`.
  - `isoOfRangeEq` with `U.fromSpec` and `Spec.preimage` give φ : ℂ[Y₀, Y₁] ≅ Γ(U). The vanishing ideal pulls back to (Y_k), so the chart is ℂ[T] over ℂ through `MvPolynomial.C`.
- The instance for `cycle-class-multiplicative-p2` elaborates by `exact` against the general statement (sketch section "p2-lines-transversal: statement").
- Traps:
  - an `affineOpens` element's proof does not serve as `IsAffineOpen` for `fromSpec` instances;
  - the cover index type `I₀` blocks the `IsOpenImmersion` instance and `simp only [Category.assoc]` on the cover map. Use an ascription and explicit `Category.assoc` terms.
- Red team: statement pass with changes (`docs/sketches/p2-lines-transversal.redteam.md`); A, B and C are implemented here, and D (the conventions row) was done by the red team.
- Next: `p2-point-class-nonzero`; then `cycle-class-multiplicative-p2` by `exact` once the general rung is checked.
