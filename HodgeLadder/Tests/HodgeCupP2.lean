module

public import HodgeLadder.Divisor.LefschetzEquality
public import HodgeLadder.Tests.CupPositiveDegreeP2

/-!
# Hodge classes with a nonzero cup product on ℙ²

Rung `cup-hodge-classes-test-p2`, the non-vacuity test of rung `cup-hodge-classes`. On
`projectivePlane`, the classes of the coordinate lines `L₀`, `L₁` are Hodge classes of
codimension one (`cycleComponentSheafClass_mem_hodgeClasses_one`), and their cup product is
nonzero (`planeLines_cup_ne_zero`). So the hypotheses of `HodgeLadder.CupPreservesHodgeClasses`
hold with a nonzero product, and the statement, once proved, gives `[pt] ∈ Hdg^2(ℙ²; ℚ)`.

## Main results

* `HodgeLadder.Tests.projectivePlane_exists_hodge_cup_ne_zero`
-/

@[expose] public section

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- On ℙ² there are two Hodge classes of codimension one whose cup product is nonzero. -/
theorem projectivePlane_exists_hodge_cup_ne_zero :
    ∃ α β : H^(2 * 1)(projectivePlane; ℚ), α ∈ Hdg^1(projectivePlane; ℚ) ∧
      β ∈ Hdg^1(projectivePlane; ℚ) ∧ Cup.cup α β (2 * (1 + 1)) (by ring) ≠ 0 :=
  ⟨_, _, cycleComponentSheafClass_mem_hodgeClasses_one _ _ (coheight_planeLine 0),
    cycleComponentSheafClass_mem_hodgeClasses_one _ _ (coheight_planeLine 1),
    planeLines_cup_ne_zero⟩

end HodgeLadder.Tests
