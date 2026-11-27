module

public import HodgeLadder.Tests.ProjectivePlaneLines
public import HodgeLadder.Cycle.Multiplicative

/-!
# `[L₀] ∪ [L₁] = [pt]` on ℙ²

Rung `cycle-class-multiplicative-p2` (decision 0010, the first transversal case). On
`projectivePlane`, the coordinate lines `L₀ = {x₀ = 0}`, `L₁ = {x₁ = 0}` (`planeLine 0`,
`planeLine 1`) meet transversally in `pt = [0 : 0 : 1]` (`planeOrigin`), and the cycle classes
satisfy `[L₀] ∪ [L₁] = [pt]` in `H⁴(ℙ²; ℚ)`, exact, sign `+`. The proof applies
`HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal` with `d = 2`, `a = b = 1`; every
hypothesis is supplied by rung `p2-lines-transversal`. The only adaptation is the coheight of the
point, stated upstream-side as `↑1 + ↑1` (`coheight_planeOrigin_add`).

The sign is visible only where `[pt] ≠ 0`, which is rung `p2-point-class-nonzero` (open).

## Main results

* `HodgeLadder.Tests.coheight_planeOrigin_add`
* `HodgeLadder.Tests.planeLines_cup_eq_planeOrigin`
-/

@[expose] public section

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- The coheight of `[0 : 0 : 1]` in the form `↑a + ↑b` with `a = b = 1`, as the transversal
theorem asks for it. -/
theorem coheight_planeOrigin_add :
    Order.coheight planeOrigin = ((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) := by
  rw [coheight_planeOrigin]; rfl

/-- **`[L₀] ∪ [L₁] = [pt]` on ℙ²**, exact, sign `+`: the Yoneda cup product of the cycle classes
of the coordinate lines `x₀ = 0` and `x₁ = 0` is the cycle class of their intersection point
`[0 : 0 : 1]`. -/
theorem planeLines_cup_eq_planeOrigin :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) =
      cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add :=
  HodgeLadder.Cycle.cycleComponentSheafClass_cup_of_transversal projectivePlane (d := 2)
    (planeLine 0) (planeLine 1) planeOrigin (coheight_planeLine 0) (coheight_planeLine 1)
    coheight_planeOrigin_add (by norm_num) planeOrigin_support_eq_inter
    (planeOrigin_support_subset_smoothSupportAmbientOpen 0)
    (planeOrigin_support_subset_smoothSupportAmbientOpen 1) planeLines_transversal

end HodgeLadder.Tests
