module

public import HodgeLadder.Hodge.DeRhamCup
public import HodgeLadder.Tests.CupPositiveDegreeP2

/-!
# A nonzero de Rham cup product of positive-degree classes on ℙ²

Rung `de-rham-cup-test-p2`. On `projectivePlane`, with `[L₀], [L₁] ∈ H²(ℙ²; ℚ)` the classes of
the coordinate lines `L₀ = {x₀ = 0}`, `L₁ = {x₁ = 0}` and `ι = fieldToDeRhamCohomology ℚ`,
`deRhamCup (ι [L₀]) (ι [L₁]) 4 _ ≠ 0` in `H_dR⁴(ℙ²)`. By `fieldToDeRhamCohomology_cup`
(rung `de-rham-cup-exact`) the product is `ι ([L₀] ∪ [L₁])`, the map `ι` is injective
(`fieldToDeRhamCohomology_rat_injective`, rung `de-rham-injective`) and `[L₀] ∪ [L₁] ≠ 0`
(`planeLines_cup_ne_zero`, rung `cup-positive-degree-test-p2`).

The degree-zero tests of `HodgeLadder.Hodge.DeRhamCup` hold for every product with the same unit,
and the square-zero product vanishes on all pairs of classes of positive degree. This file rules
the square-zero product out for `deRhamCup` in even positive degree on a projective variety, and
records the value: `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` with `[pt]` the class of `[0 : 0 : 1]`,
from `planeLines_cup_eq_planeOrigin` (rung `cycle-class-multiplicative-p2`), and the negated value
fails since `[pt] ≠ 0` (rung `p2-point-class-nonzero`).

## Main results

* `HodgeLadder.Tests.planeLines_deRhamCup_ne_zero`
* `HodgeLadder.Tests.planeLines_deRhamCup_eq_planeOrigin`: the exact value `ι [pt]`, sign `+`
* `HodgeLadder.Tests.planeLines_deRhamCup_ne_neg`: the value is not `−ι [pt]`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

/-- **`de-rham-cup-test-p2`**: on ℙ², `deRhamCup (ι [L₀]) (ι [L₁]) ≠ 0` in `H_dR⁴(ℙ²)`, with
`ι = fieldToDeRhamCohomology ℚ projectivePlane 2` and `[Lᵢ]` the class of the coordinate line
`Lᵢ` (`cycleComponentSheafClass`). From `fieldToDeRhamCohomology_cup`, the injectivity of `ι`
and `planeLines_cup_ne_zero`. -/
theorem planeLines_deRhamCup_ne_zero :
    deRhamCup
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
      4 (by norm_num) ≠ 0 := by
  intro h
  apply planeLines_cup_ne_zero
  apply fieldToDeRhamCohomology_rat_injective projectivePlane (2 * (1 + 1))
  rw [map_zero, fieldToDeRhamCohomology_cup]
  exact h

/-- **The value, exact.** `deRhamCup (ι [L₀]) (ι [L₁]) = ι [pt]` in `H_dR⁴(ℙ²)`, sign `+`, with
`[pt]` the class of `[0 : 0 : 1]`: `planeLines_cup_eq_planeOrigin` carried through
`fieldToDeRhamCohomology_cup`. -/
theorem planeLines_deRhamCup_eq_planeOrigin :
    deRhamCup
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
      4 (by norm_num) =
      fieldToDeRhamCohomology ℚ projectivePlane (2 * (1 + 1))
        (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add) := by
  rw [← planeLines_cup_eq_planeOrigin, fieldToDeRhamCohomology_cup]
  rfl

/-- **The sign.** `deRhamCup (ι [L₀]) (ι [L₁]) ≠ −ι [pt]`: `ι` is injective and `[pt] ≠ 0`. -/
theorem planeLines_deRhamCup_ne_neg :
    deRhamCup
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
      (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
      4 (by norm_num) ≠
      -fieldToDeRhamCohomology ℚ projectivePlane (2 * (1 + 1))
        (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add) := by
  rw [planeLines_deRhamCup_eq_planeOrigin, ← map_neg]
  intro h
  have h2 := fieldToDeRhamCohomology_rat_injective projectivePlane (2 * (1 + 1)) h
  have h3 : (2 : ℚ) • cycleComponentSheafClass projectivePlane planeOrigin
      coheight_planeOrigin_add = 0 := by
    rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel _
  exact projectivePlane_point_class_ne_zero ((smul_eq_zero.mp h3).resolve_left two_ne_zero)

end HodgeLadder.Tests
