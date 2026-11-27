module

public import HodgeLadder.Hodge.DeRhamRationalBaseChange
public import HodgeLadder.Tests.CycleClassSignTestP2

/-!
# `H_dR⁴(ℙ²)` is a complex line

Rung `de-rham-p2-top-rank` (kind test; red team of `de-rham-rational-span`, section 7b). On
upstream's ℙ² over `ℂ` (`HodgeLadder.Tests.projectivePlane`),
`Module.finrank ℂ H_dR^4(projectivePlane) = 1`, with upstream's `ℂ`-module structure on de Rham
cohomology.

The proof reads two checked results.

1. `finrank_deRham_eq_finrank_rat` (rung `de-rham-rational-base-change`): on a smooth projective
   integral `X`, `finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`. ℙ² carries the three instances
   (`isIntegral_projectiveSpace`, `smooth_projectiveSpace`, `isProjective_projectiveSpace`).
2. `planeDegree_bijective` (rung `cycle-class-sign-test-p2`): the degree map
   `H⁴(ℙ²; ℚ) → ℚ` is a bijective additive map, hence a `ℚ`-linear equivalence, so
   `finrank_ℚ H⁴(ℙ²; ℚ) = 1`.

The test fails if the span of `de-rham-rational-span` held for a degenerate reason: with
`H_dR⁴(ℙ²) = 0` the rank would be `0`, and with an infinite-dimensional `H_dR⁴(ℙ²)` Mathlib's
`finrank` would also be `0`. So the identity also gives finite-dimensionality and nonvanishing of
`H_dR⁴(ℙ²)`.

The proof reads `finrank_deRham_eq_finrank_rat` and `planeDegree_bijective` only. The value also
follows from `span_range_fieldToDeRhamCohomology_rat` (rung `de-rham-rational-span`),
`fieldToDeRhamCohomology_rat_injective` (rung `de-rham-injective`) and `planeDegreeLinearEquiv`
without `de-rham-rational-independent`, so the test does not exercise ℂ-independence. Every Betti
number of ℙ² is at most `1`; the separating test is `de-rham-rational-independent-test-gm2`.

## Main definitions

* `HodgeLadder.Tests.planeDegreeLinearEquiv`: the degree map as `H⁴(ℙ²; ℚ) ≃ₗ[ℚ] ℚ`.

## Main results

* `HodgeLadder.Tests.finrank_rat_H_four_projectivePlane`: `finrank_ℚ H⁴(ℙ²; ℚ) = 1`.
* `HodgeLadder.Tests.finrank_deRham_four_projectivePlane`: `finrank_ℂ H_dR⁴(ℙ²) = 1`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

/-- The degree map as a `ℚ`-linear equivalence `H⁴(ℙ²; ℚ) ≃ₗ[ℚ] ℚ`: `planeDegree` is additive and
bijective (`planeDegree_bijective`), and an additive map of `ℚ`-vector spaces is `ℚ`-linear. -/
def planeDegreeLinearEquiv : H^(2 * 2)(projectivePlane; ℚ) ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofBijective planeDegree.toRatLinearMap planeDegree_bijective

/-- `finrank_ℚ H⁴(ℙ²; ℚ) = 1`, from the degree isomorphism. -/
theorem finrank_rat_H_four_projectivePlane : Module.finrank ℚ H^4(projectivePlane; ℚ) = 1 :=
  planeDegreeLinearEquiv.finrank_eq.trans (Module.finrank_self ℚ)

/-- **Rung `de-rham-p2-top-rank`.** On ℙ² over `ℂ`, `Module.finrank ℂ H_dR^4(projectivePlane) = 1`,
with upstream's `ℂ`-module structure on `H_dR⁴`. -/
theorem finrank_deRham_four_projectivePlane : Module.finrank ℂ H_dR^4(projectivePlane) = 1 :=
  (finrank_deRham_eq_finrank_rat projectivePlane 4).trans finrank_rat_H_four_projectivePlane

end HodgeLadder.Tests
