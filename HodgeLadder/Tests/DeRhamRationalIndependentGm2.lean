module

public import HodgeLadder.Tests.OddDegreeTorus
public import HodgeLadder.Cup.CupSingular
public import HodgeLadder.Hodge.DeRhamRationalIndependent

/-!
# Two ℚ-independent classes in `H¹(𝔾ₘ²; ℚ)` with ℂ-independent de Rham images

Rung `de-rham-rational-independent-test-gm2` (kind test; red team of
`de-rham-rational-independent`, finding 7b, and of `de-rham-rational-base-change`, finding 7). On
the algebraic torus `𝔾ₘ²` the winding classes `x₁`, `x₂` of the two coordinates are linearly
independent over `ℚ` in `H¹(𝔾ₘ²(ℂ); ℚ)`, and their images under upstream's
`ι = fieldToDeRhamCohomology ℚ gm2 1` are linearly independent over `ℂ` in `H_dR¹(𝔾ₘ²)`.

This is the shape that separates ℂ-independence from ℚ-injectivity (rung `de-rham-injective`): the
map `ℚ² → ℂ`, `(a, b) ↦ a + b √2` is injective with ℂ-dependent image. Every Betti number of ℙ² is
at most `1`, so the ℙ² test `de-rham-p2-top-rank` cannot see the difference.

The ℚ-independence uses the cup product of record.

1. In degree `(1, 1)` graded commutativity (`cup_gradedComm`) has sign `(-1)^{1·1} = -1`, so
   `x ∪ x = -(x ∪ x)` and `x ∪ x = 0` over `ℚ` (`cup_self_eq_zero_gm2`). With sign `+1` the identity
   would be empty and this step would fail.
2. The cup is additive in each factor (`add_cup`, `cup_add`), hence `ℚ`-linear in each factor.
3. From `a x₁ + b x₂ = 0`, cupping with `x₂` on the right gives `a (x₁ ∪ x₂) = 0`, cupping with `x₁`
   on the left gives `b (x₁ ∪ x₂) = 0`, and `x₁ ∪ x₂ ≠ 0` (`gm2_cup_ne_zero`, rung
   `cup-odd-degree-gm2`) gives `a = b = 0`.

The ℂ-independence is then `linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`: `𝔾ₘ²` is
smooth and integral, not projective, so this test exercises `de-rham-rational-independent` and not
the projective base-change rung.

## Main definitions

* `HodgeLadder.Tests.gm2CupLeft`, `HodgeLadder.Tests.gm2CupRight`: the cup with a fixed degree-one
  class, as additive maps.

## Main results

* `HodgeLadder.Tests.cup_self_eq_zero_gm2`: `x ∪ x = 0` for `x ∈ H¹(𝔾ₘ²; ℚ)`.
* `HodgeLadder.Tests.linearIndependent_windingClasses_gm2`: `x₁`, `x₂` are ℚ-independent.
* `HodgeLadder.Tests.linearIndependent_deRham_windingClasses_gm2`: their de Rham images are
  ℂ-independent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Cup

namespace HodgeLadder.Tests

/-- In degree one the cup square vanishes over `ℚ`: graded commutativity has sign `-1` in degree
`(1, 1)`, so `x ∪ x = -(x ∪ x)`. -/
theorem cup_self_eq_zero_gm2 (x : H^1(gm2; ℚ)) : cup x x 2 rfl = 0 := by
  have h := cup_gradedComm (X := gm2) x x (show 1 + 1 = 2 from rfl)
  norm_num at h
  have h2 : (2 : ℚ) • cup x x 2 rfl = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The cup `x ↦ x ∪ y` with a fixed class `y ∈ H¹(𝔾ₘ²; ℚ)` on the right, as an additive map. -/
def gm2CupLeft (y : H^1(gm2; ℚ)) : H^1(gm2; ℚ) →+ H^2(gm2; ℚ) :=
  AddMonoidHom.mk' (fun x ↦ cup x y 2 rfl) (fun a b ↦ add_cup a b y 2 rfl)

/-- The cup `y ↦ x ∪ y` with a fixed class `x ∈ H¹(𝔾ₘ²; ℚ)` on the left, as an additive map. -/
def gm2CupRight (x : H^1(gm2; ℚ)) : H^1(gm2; ℚ) →+ H^2(gm2; ℚ) :=
  AddMonoidHom.mk' (fun y ↦ cup x y 2 rfl) (fun a b ↦ cup_add x a b 2 rfl)

/-- The winding classes of the two coordinates of `𝔾ₘ²` are linearly independent over `ℚ` in
`H¹(𝔾ₘ²(ℂ); ℚ)`. -/
theorem linearIndependent_windingClasses_gm2 :
    LinearIndependent ℚ ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero,
      sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero] := by
  set x₁ := sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero
  set x₂ := sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero
  have hne : cup x₁ x₂ 2 rfl ≠ 0 := gm2_cup_ne_zero
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hR := congrArg (gm2CupLeft x₂).toRatLinearMap hab
  have hL := congrArg (gm2CupRight x₁).toRatLinearMap hab
  simp only [map_add, map_smul, map_zero] at hR hL
  change a • cup x₁ x₂ 2 rfl + b • cup x₂ x₂ 2 rfl = 0 at hR
  change a • cup x₁ x₁ 2 rfl + b • cup x₁ x₂ 2 rfl = 0 at hL
  rw [cup_self_eq_zero_gm2, smul_zero, add_zero] at hR
  rw [cup_self_eq_zero_gm2, smul_zero, zero_add] at hL
  exact ⟨(smul_eq_zero.mp hR).resolve_right hne, (smul_eq_zero.mp hL).resolve_right hne⟩

/-- **Rung `de-rham-rational-independent-test-gm2`.** The de Rham images of the two winding classes
of `𝔾ₘ²` under upstream's `fieldToDeRhamCohomology ℚ gm2 1` are linearly independent over `ℂ`. -/
theorem linearIndependent_deRham_windingClasses_gm2 :
    LinearIndependent ℂ (fieldToDeRhamCohomology ℚ gm2 1 ∘
      ![sheafWindingClass gm2 gmCoordOne gmCoordOne_ne_zero,
        sheafWindingClass gm2 gmCoordTwo gmCoordTwo_ne_zero]) :=
  linearIndependent_fieldToDeRhamCohomology_rat_of_smooth gm2 1
    linearIndependent_windingClasses_gm2

end HodgeLadder.Tests
