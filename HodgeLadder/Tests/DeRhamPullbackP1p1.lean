module

public import HodgeLadder.Hodge.DeRhamPullback
public import HodgeLadder.Tests.PullbackFunctorial

/-!
# Non-vacuity of `deRhamPullback` on `ℙ¹ × ℙ¹`

Rung `de-rham-pullback-test`, non-vacuity of rung `de-rham-pullback`. Along the first
projection `prod.fst : ℙ¹ × ℙ¹ ⟶ ℙ¹`, the de Rham pullback of the image `ι [∞] ∈ H²_dR(ℙ¹)`
of the point class `[∞] ∈ H²(ℙ¹; ℚ)` is nonzero. So `deRhamPullback` is not the zero map on a
non-identity morphism. By
`deRhamPullback_fieldToDeRhamCohomology` the class is `ι (pr₁^* [∞])`; `ι` is injective
(`fieldToDeRhamCohomology_rat_injective`, rung `de-rham-injective`) and `pr₁^* [∞] ≠ 0`
(`p1p1_pullbackCoh_fst_class_ne_zero`, rung `pullback-functorial-test`).

`p1p1_deRhamPullback_fst_injective` is stronger and exercises the composition and identity laws
on a non-identity morphism in every degree: `prod.fst` has the section `fibreSectionSnd`, so
`deRhamPullback prod.fst n` is injective (`deRhamPullback_injective_of_section`).

## Main results

* `HodgeLadder.Tests.p1p1_deRhamPullback_fst_class_ne_zero`
* `HodgeLadder.Tests.p1p1_deRhamPullback_fst_injective`
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint HodgeLadder.Cup

namespace HodgeLadder.Tests

/-- **The de Rham pullback along `pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹` is nonzero on `ι [∞]`**, with
`[∞] = cycleComponentSheafClass projectiveLine infty _ ∈ H²(ℙ¹; ℚ)` and
`ι = fieldToDeRhamCohomology ℚ projectiveLine 2`. -/
theorem p1p1_deRhamPullback_fst_class_ne_zero :
    deRhamPullback (prod.fst : p1p1 ⟶ projectiveLine) (2 * 1)
      (fieldToDeRhamCohomology ℚ projectiveLine (2 * 1)
        (cycleComponentSheafClass projectiveLine infty coheight_infty')) ≠ 0 := by
  rw [deRhamPullback_fieldToDeRhamCohomology]
  intro h
  apply p1p1_pullbackCoh_fst_class_ne_zero
  apply fieldToDeRhamCohomology_rat_injective p1p1 (2 * 1)
  rw [h, map_zero]

/-- **The de Rham pullback along `pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹` is injective in every degree**, through
the section `fibreSectionSnd = prod.lift (𝟙 _) constInfty`. -/
theorem p1p1_deRhamPullback_fst_injective (n : ℕ) :
    Function.Injective (deRhamPullback (prod.fst : p1p1 ⟶ projectiveLine) n) :=
  deRhamPullback_injective_of_section _ fibreSectionSnd (prod.lift_fst _ _) n

end HodgeLadder.Tests
