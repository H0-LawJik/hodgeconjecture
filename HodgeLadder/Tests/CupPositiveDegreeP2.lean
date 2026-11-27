module

public import HodgeLadder.Tests.CycleClassMultiplicativeP2
public import HodgeLadder.Tests.ProjectivePlanePoint

/-!
# A nonzero cup product of positive-degree classes on ℙ²

Rung `cup-positive-degree-test-p2` (decision 0010). On `projectivePlane`, the cup product of the
classes of the coordinate lines `L₀ = {x₀ = 0}`, `L₁ = {x₁ = 0}` is nonzero in `H⁴(ℙ²; ℚ)`:
`[L₀] ∪ [L₁] = [pt]` (`planeLines_cup_eq_planeOrigin`, rung `cycle-class-multiplicative-p2`) and
`[pt] ≠ 0` (`projectivePlane_point_class_ne_zero`, rung `p2-point-class-nonzero`).

The ring laws checked for `HodgeLadder.Cup.cup` (associativity, unit, graded commutativity) also
hold for the square-zero product, which vanishes on every pair of classes of positive degree.
This file rules that product out in even degrees on a projective variety:
`cup_ne_zero_of_positive_degree` exhibits two classes of degree two whose cup is nonzero.

## Main results

* `HodgeLadder.Tests.planeLines_cup_ne_zero`
* `HodgeLadder.Tests.cup_ne_zero_of_positive_degree`
-/

@[expose] public section

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- **`cup-positive-degree-test-p2`**: on ℙ², `[L₀] ∪ [L₁] ≠ 0` in `H⁴(ℙ²; ℚ)`. -/
theorem planeLines_cup_ne_zero :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) ≠ 0 := by
  rw [planeLines_cup_eq_planeOrigin]
  exact projectivePlane_point_class_ne_zero

/-- The cup product of record is not the square-zero product in positive degree: on ℙ² there
are two classes of degree two whose cup product is nonzero. -/
theorem cup_ne_zero_of_positive_degree :
    ∃ (α β : H^2(projectivePlane; ℚ)), HodgeLadder.Cup.cup α β 4 rfl ≠ 0 :=
  ⟨_, _, planeLines_cup_ne_zero⟩

end HodgeLadder.Tests
