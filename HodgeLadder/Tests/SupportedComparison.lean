module

public import HodgeLadder.Cup.SupportedPair
public import HodgeLadder.Tests.CupComparison
public import HodgeLadder.Tests.ProjectiveLineTest

/-!
# The supported cup comparison on the projective line

Non-vacuity check for rungs `cup-singular-comparison` (supported case) and
`cup-comparison-supported-pair` (red team, 2026-11-26): the hypotheses hold on upstream's `ℙ¹` for
every closed `Z`, and the left side is nonzero for the supported class of the point at infinity
times `1`. The test has `q = 0`, so it does not see the sign `(−1)^{pq}`; that needs odd-degree
classes (rung `cup-odd-degree-test`).

## Main results

* `HodgeLadder.Tests.projectiveLine_cup_singular_comparison_supported`,
  `HodgeLadder.Tests.projectiveLine_supCup_point_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace HodgeLadder.Cup

namespace HodgeLadder.Tests

local instance : ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

/-- The supported cup comparison holds on `ℙ¹`, for every closed `Z`. -/
theorem projectiveLine_cup_singular_comparison_supported (Z : Closeds (ComplexPoint projectiveLine))
    {p q : ℕ} (α : H_[Z]^p(projectiveLine; ℚ)) (β : H^q(projectiveLine; ℚ)) :
    supportedEquivPair projectiveLine Z (p + q) (supCup α β (p + q) rfl) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing
        (TopPair.ofSubset (Z.compl : Set (TopCat.of (ComplexPoint projectiveLine))))
        (supportedEquivPair projectiveLine Z p α)
        (rationalCohomologyAddEquivSingularCohomology projectiveLine q β) (p + q) rfl :=
  cup_singular_comparison_supported_pair projectiveLine Z α β

/-- The supported product of the class of the point at infinity with `1` is nonzero. -/
theorem projectiveLine_supCup_point_ne_zero :
    supCup (cycleComponentSupportedInjectiveClass projectiveLine infty coheight_infty')
      (one projectiveLine) (2 * 1 + 0) rfl ≠ 0 := by
  rw [supCup_one]
  intro h
  apply class_infty_ne_zero_of acyclic_compl_infty
  rw [cycleComponentSheafClass_eq_forgetSupport, h, map_zero]

end HodgeLadder.Tests
