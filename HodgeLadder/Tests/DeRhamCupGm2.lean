module

public import HodgeLadder.Hodge.DeRhamCup
public import HodgeLadder.Tests.OddDegreeTorus
public import HodgeLadder.Cup.CupSingular

/-!
# The de Rham cup product in degree `(1, 1)` on `𝔾ₘ²`

Tests for rung `de-rham-cup-exact`. With `x₁ x₂ ∈ H¹(𝔾ₘ²; ℚ)` the winding classes of the two
coordinates (rung `cup-odd-degree-gm2`) and `ι = fieldToDeRhamCohomology ℚ gm2`, the identity
`fieldToDeRhamCohomology_cup` transports `x₁ ∪ x₂ ≠ 0` and `x₁ ∪ x₂ ≠ x₂ ∪ x₁` to `H_dR²(𝔾ₘ²)`.
So in odd degree `deRhamCup (ι x₁) (ι x₂)` is nonzero, the factor order is visible, the product
twisted by `(−1)^{ab}` does not satisfy the identity, and graded commutativity holds with the
sign `(−1)^{1·1} = −1` of `Cup.cup_gradedComm`.

## Main results

* `HodgeLadder.Tests.gm2_deRhamCup_ne_zero`, `HodgeLadder.Tests.gm2_deRhamCup_swap_ne`,
  `HodgeLadder.Tests.gm2_deRhamCup_twist_ne`, `HodgeLadder.Tests.gm2_deRhamCup_antisymm`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

local notation "x₁" => HodgeLadder.Cup.sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero
local notation "x₂" => HodgeLadder.Cup.sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero

/-- **Odd-degree nonvacuity.** `deRhamCup (ι x₁) (ι x₂) ≠ 0` in `H_dR²(𝔾ₘ²)`: by
`fieldToDeRhamCohomology_cup` it is `ι (x₁ ∪ x₂)`, `ι` is injective and `x₁ ∪ x₂ ≠ 0`. -/
theorem gm2_deRhamCup_ne_zero :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
      2 (by norm_num) ≠ 0 := by
  intro h
  apply gm2_cup_ne_zero
  apply fieldToDeRhamCohomology_rat_injective gm2 2
  rw [map_zero, fieldToDeRhamCohomology_cup]
  exact h

/-- **The factor order is visible.** `deRhamCup (ι x₂) (ι x₁) ≠ deRhamCup (ι x₁) (ι x₂)`, from
`gm2_cup_swap_ne`. So the product with its arguments exchanged does not satisfy
`fieldToDeRhamCohomology_cup`. -/
theorem gm2_deRhamCup_swap_ne :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) ≠
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  intro h
  apply gm2_cup_swap_ne
  apply fieldToDeRhamCohomology_rat_injective gm2 2
  rw [fieldToDeRhamCohomology_cup, fieldToDeRhamCohomology_cup]
  exact h

/-- **No degree-dependent sign.** `ι (x₁ ∪ x₂) ≠ −deRhamCup (ι x₁) (ι x₂)`: the product twisted
by `(−1)^{ab}` does not satisfy `fieldToDeRhamCohomology_cup` at `a = b = 1`. -/
theorem gm2_deRhamCup_twist_ne :
    fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) ≠
      -deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  intro htw
  have hc : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  rw [hc, eq_neg_iff_add_eq_zero, ← two_nsmul] at htw
  have h2 : (2 : ℂ) • deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁)
      (fieldToDeRhamCohomology ℚ gm2 1 x₂) 2 (by norm_num) = 0 := by
    rw [ofNat_smul_eq_nsmul (R := ℂ)]; exact htw
  have h3 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [← hc] at h3
  exact gm2_cup_ne_zero (fieldToDeRhamCohomology_rat_injective gm2 2 (h3.trans (map_zero _).symm))

/-- **Graded commutativity, literature sign.** `deRhamCup (ι x₂) (ι x₁) = −deRhamCup (ι x₁) (ι x₂)`,
the sign `(−1)^{1·1}` of `Cup.cup_gradedComm` carried through `fieldToDeRhamCohomology_cup`. -/
theorem gm2_deRhamCup_antisymm :
    deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) =
      -deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := by
  have h12 : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₁ x₂ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₁) (fieldToDeRhamCohomology ℚ gm2 1 x₂)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  have h21 : fieldToDeRhamCohomology ℚ gm2 2 (HodgeLadder.Cup.cup x₂ x₁ 2 rfl) =
      deRhamCup (fieldToDeRhamCohomology ℚ gm2 1 x₂) (fieldToDeRhamCohomology ℚ gm2 1 x₁)
        2 (by norm_num) := fieldToDeRhamCohomology_cup gm2 (a := 1) (b := 1) (n := 2) rfl _ _
  rw [← h12, ← h21, HodgeLadder.Cup.cup_gradedComm gm2 x₂ x₁ rfl, map_zsmul]
  norm_num

end HodgeLadder.Tests
