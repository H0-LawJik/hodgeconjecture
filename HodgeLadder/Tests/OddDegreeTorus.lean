module

public import HodgeLadder.Tests.AlgebraicTorusPoints
public import HodgeLadder.Cup.OddDegree

/-!
# A nonzero product of two classes in `H¹(𝔾ₘ²; ℚ)`

Rung `cup-odd-degree-gm2` (test for `cup-singular-comparison-absolute` and
`cup-graded-commutative`; the weaker companion of `cup-odd-degree-test`, which asks for a curve of
positive genus or an abelian surface). On the algebraic torus `𝔾ₘ²` (rungs `gm2-witness`,
`gm2-points`) the two coordinates `x`, `y` are nowhere vanishing on `𝔾ₘ²(ℂ) ≅ ℂˣ × ℂˣ`, and the
standard torus `(s, t) ↦ (exp (2πi s), exp (2πi t))` has period `1` in each variable. Rung
`cup-odd-degree-transfer` then gives sheaf classes `x₁ x₂ ∈ H¹(𝔾ₘ²; ℚ)`, the preimages under
upstream's `Ψ` of the winding classes of `x` and `y`, with

  `⟨Ψ (x₁ ∪ x₂), T⟩ = −1`, `⟨Ψ (x₂ ∪ x₁), T⟩ = 1`,

so `x₁ ∪ x₂ ≠ 0` and `x₁ ∪ x₂ ≠ x₂ ∪ x₁`. The cup product is the Yoneda product of rung
`cup-product`; the value `−1` carries the sign `(−1)^{1·1}` of `cup_singular_comparison` on a
computed instance.

## Main definitions

* `HodgeLadder.Tests.gmCoordOne`, `HodgeLadder.Tests.gmCoordTwo`, `HodgeLadder.Tests.gmTorus`

## Main results

* `HodgeLadder.Tests.gm2_torusEval_cup`, `HodgeLadder.Tests.gm2_torusEval_cup_swap`,
  `HodgeLadder.Tests.gm2_cup_ne_zero`, `HodgeLadder.Tests.gm2_exists_cup_ne_zero`,
  `HodgeLadder.Tests.gm2_cup_swap_ne`, `HodgeLadder.Tests.gm2_not_comparison_plus`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Cup ChernWinding

namespace HodgeLadder.Tests

/-- The first coordinate on `𝔾ₘ²(ℂ)`. -/
def gmCoordOne : C(ComplexPoint gm2, ℂ) := coordOne.comp ⟨gmHomeomorph, gmHomeomorph.continuous⟩

/-- The second coordinate on `𝔾ₘ²(ℂ)`. -/
def gmCoordTwo : C(ComplexPoint gm2, ℂ) := coordTwo.comp ⟨gmHomeomorph, gmHomeomorph.continuous⟩

/-- The first coordinate does not vanish. -/
theorem gmCoordOne_ne_zero (z : ComplexPoint gm2) : gmCoordOne z ≠ 0 := coordOne_ne_zero _

/-- The second coordinate does not vanish. -/
theorem gmCoordTwo_ne_zero (z : ComplexPoint gm2) : gmCoordTwo z ≠ 0 := coordTwo_ne_zero _

/-- The standard torus in `𝔾ₘ²(ℂ)`. -/
def gmTorus : C(ℝ × ℝ, ComplexPoint gm2) :=
  (⟨gmHomeomorph.symm, gmHomeomorph.symm.continuous⟩ : C(puncturedSquare, ComplexPoint gm2)).comp
    standardTorus

/-- `gmTorus` has period `1` in the first variable. -/
theorem gmTorus_one_left (t : ℝ) : gmTorus (1, t) = gmTorus (0, t) := by
  simp only [gmTorus, ContinuousMap.comp_apply]
  rw [standardTorus_one_left]

/-- `gmTorus` has period `1` in the second variable. -/
theorem gmTorus_one_right (s : ℝ) : gmTorus (s, 1) = gmTorus (s, 0) := by
  simp only [gmTorus, ContinuousMap.comp_apply]
  rw [standardTorus_one_right]

/-- The first coordinate along `gmTorus` is `exp (2πi s)`. -/
theorem gmCoordOne_gmTorus (p : ℝ × ℝ) :
    gmCoordOne (gmTorus p) = Complex.exp (twoPiI * (p.1 : ℂ)) := by
  simp only [gmCoordOne, gmTorus, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Homeomorph.apply_symm_apply]
  rfl

/-- The second coordinate along `gmTorus` is `exp (2πi t)`. -/
theorem gmCoordTwo_gmTorus (p : ℝ × ℝ) :
    gmCoordTwo (gmTorus p) = Complex.exp (twoPiI * (p.2 : ℂ)) := by
  simp only [gmCoordTwo, gmTorus, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Homeomorph.apply_symm_apply]
  rfl

/-- **On `𝔾ₘ²`, `⟨Ψ (x₁ ∪ x₂), T⟩ = −1`.** -/
theorem gm2_torusEval_cup :
    torusEval (Y := TopCat.of (ComplexPoint gm2)) gmTorus_one_left gmTorus_one_right
      (AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology gm2 2
        (cup (sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero)
          (sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero) 2 rfl)) = -1 :=
  torusEval_cup_sheafWinding _ _ _ _ _ _ gmCoordOne_gmTorus gmCoordTwo_gmTorus

/-- **On `𝔾ₘ²`, a nonzero product of two classes in `H¹(X; ℚ)`.** -/
theorem gm2_cup_ne_zero :
    cup (sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero)
      (sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero) 2 rfl ≠ 0 :=
  cup_sheafWinding_ne_zero gmTorus_one_left gmTorus_one_right _ _ _ _ gmCoordOne_gmTorus
    gmCoordTwo_gmTorus

/-- **`𝔾ₘ²` has two classes in `H¹(X; ℚ)` with nonzero product**, in the form of the rung. -/
theorem gm2_exists_cup_ne_zero : ∃ x y : H^1(gm2; ℚ), cup x y 2 rfl ≠ 0 :=
  ⟨_, _, gm2_cup_ne_zero⟩

/-- **On `𝔾ₘ²`, `⟨Ψ (x₂ ∪ x₁), T⟩ = 1`.** -/
theorem gm2_torusEval_cup_swap :
    torusEval (Y := TopCat.of (ComplexPoint gm2)) gmTorus_one_left gmTorus_one_right
      (AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology gm2 2
        (cup (sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero)
          (sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero) 2 rfl)) = 1 :=
  torusEval_cup_sheafWinding_swap _ _ _ _ _ _ gmCoordOne_gmTorus gmCoordTwo_gmTorus

/-- **On `𝔾ₘ²`, the two orders differ**: `x₂ ∪ x₁ ≠ x₁ ∪ x₂`. -/
theorem gm2_cup_swap_ne :
    cup (sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero)
        (sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero) 2 rfl ≠
      cup (sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero)
        (sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero) 2 rfl :=
  cup_sheafWinding_swap_ne gmTorus_one_left gmTorus_one_right _ _ _ _ gmCoordOne_gmTorus
    gmCoordTwo_gmTorus

/-- **The comparison without its sign is false on `𝔾ₘ²`**: no equation
`Ψ (x ∪ y) = cupSing (Ψ x) (Ψ y)` holds for all degree-one classes. With it,
`cup_singular_comparison_swap` would give `Ψ (x₁ ∪ x₂) = Ψ (x₂ ∪ x₁)`, while the torus cycle
takes the values `-1` and `1` on them. -/
theorem gm2_not_comparison_plus :
    ¬ ∀ x y : H^1(gm2; ℚ),
      AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology gm2 2
          (cup x y 2 rfl) =
        cupSing (TopCat.of (ComplexPoint gm2))
          (AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology gm2 1 x)
          (AlgebraicGeometry.ComplexPoint.rationalCohomologyAddEquivSingularCohomology gm2 1 y)
          2 rfl := by
  intro h
  have e1 := gm2_torusEval_cup
  have e2 := gm2_torusEval_cup_swap
  rw [cup_singular_comparison_swap (p := 1) (q := 1) (n := 2) gm2 _ _ (show 1 + 1 = 2 from rfl), ← h] at e1
  rw [e1] at e2
  norm_num at e2

end HodgeLadder.Tests
