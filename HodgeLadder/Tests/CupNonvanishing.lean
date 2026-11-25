module

public import HodgeLadder.Cup.Product
public import HodgeLadder.Tests.ProjectiveLineTest

/-!
# The cup product is not identically zero

Non-vacuity test for rung `cup-product`: on ℙ¹, the unit times the class of a point is that class,
which is nonzero (`projective-line-class-nonzero`). So both the product and the unit are nonzero.

## Main results

* `HodgeLadder.Tests.projectiveLine_one_cup_ne_zero`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Cup

namespace HodgeLadder.Tests

/-- On ℙ¹, `1 ∪ [pt] = [pt] ≠ 0`. -/
theorem projectiveLine_one_cup_ne_zero :
    cup (one projectiveLine) (cycleComponentSheafClass projectiveLine infty coheight_infty')
      (2 * 1) (zero_add _) ≠ 0 := by
  rw [one_cup]
  exact class_infty_ne_zero_of acyclic_compl_infty

end HodgeLadder.Tests
