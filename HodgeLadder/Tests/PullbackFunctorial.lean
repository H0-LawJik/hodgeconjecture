module

public import HodgeLadder.Pullback.Functorial
public import HodgeLadder.Tests.ProjectiveLineTest
public import HodgeLadder.Tests.P1p1Fibres

/-!
# Pullback along a projection of ℙ¹ × ℙ¹ keeps the point class nonzero

Non-vacuity test for rung `pullback-functorial`. The section `fibreSectionSnd = prod.lift (𝟙) ∞`
of `prod.fst : ℙ¹ × ℙ¹ ⟶ ℙ¹` satisfies `fibreSectionSnd ≫ prod.fst = 𝟙`, so by the composition
and identity laws `prod.fst^*` is injective on `H²`. The class of the point `∞` of ℙ¹ is nonzero
(`projective-line-class-nonzero`), hence so is its pullback to `H²(ℙ¹ × ℙ¹; ℚ)`. The proof uses
both functoriality laws; neither the unit nor the cup product enters. A third check pins the
`ℚ`-structure of `pullbackCohLinear` against upstream's scalar action.

## Main results

* `HodgeLadder.Tests.p1p1_pullbackCoh_fst_injective`
* `HodgeLadder.Tests.p1p1_pullbackCoh_fst_class_ne_zero`
* `HodgeLadder.Tests.pullbackCoh_fieldScalar`: `pullbackCohLinear` is linear for upstream's
  scalar action `Sheaf.H.map (fieldScalarSheaf ℚ X q)`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint HodgeLadder.Cup HodgeLadder.Pullback

namespace HodgeLadder.Tests

/-- `prod.fst^* : Hⁿ(ℙ¹; ℚ) → Hⁿ(ℙ¹ × ℙ¹; ℚ)` is injective, through the section
`fibreSectionSnd`. -/
theorem p1p1_pullbackCoh_fst_injective (n : ℕ) :
    Function.Injective (pullbackCoh (prod.fst : p1p1 ⟶ projectiveLine) n) :=
  pullbackCoh_injective_of_section _ fibreSectionSnd (prod.lift_fst _ _) n

/-- The pullback of the point class `[∞] ∈ H²(ℙ¹; ℚ)` along `prod.fst` is nonzero in
`H²(ℙ¹ × ℙ¹; ℚ)`. -/
theorem p1p1_pullbackCoh_fst_class_ne_zero :
    pullbackCoh (prod.fst : p1p1 ⟶ projectiveLine) (2 * 1)
      (cycleComponentSheafClass projectiveLine infty coheight_infty') ≠ 0 := by
  intro h
  apply class_infty_ne_zero_of acyclic_compl_infty
  apply p1p1_pullbackCoh_fst_injective (2 * 1)
  rw [h, ← pullbackCohLinear_apply, map_zero]

/-- **The ℚ-structure is upstream's.** Pullback commutes with upstream's scalar action
`q • α = Sheaf.H.map (fieldScalarSheaf ℚ X q) n α`, read through `pullbackCohLinear`. -/
theorem pullbackCoh_fieldScalar {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X) (n : ℕ) (q : ℚ)
    (α : H^n(X; ℚ)) :
    pullbackCoh g n (Sheaf.H.map.{0} (fieldScalarSheaf ℚ X q) n α) =
      Sheaf.H.map.{0} (fieldScalarSheaf ℚ X' q) n (pullbackCoh g n α) := by
  rw [← field_smul_eq, ← field_smul_eq, ← pullbackCohLinear_apply, map_smul,
    pullbackCohLinear_apply]

end HodgeLadder.Tests
