module

public import HodgeLadder.Tests.ProjectivePlaneFundamental
public import HodgeLadder.Tests.CycleClassSignTestP2

/-!
# The degree on `H⁴(ℙ²; ℚ)` is evaluation on the fundamental class

Corollaries of rung `p2-fundamental-class`, kept apart from it because they import
`HodgeLadder.Tests.CycleClassSignTestP2` (rung `cycle-class-sign-test-p2`, minutes to elaborate).

* `H₄(ℙ²(ℂ) ∖ pt; ℚ) = 0` as well (sheaf form `subsingleton_H'_compl_planeOrigin 1`), so the
  projection `H₄(ℙ²(ℂ); ℚ) → H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ pt; ℚ)` is bijective and exactly one `μ` restricts to
  the complex local orientation: the literature's one-point characterization of `[ℙ²]`.
* With `planeDegree_eq_eval_of_restrict`, its hypothesis discharged: `deg α = ⟨Ψ α, μ⟩` for that
  `μ`, unconditionally, and `⟨Ψ [pt], μ⟩ = 1`.

## Main results

* `HodgeLadder.Tests.existsUnique_restrict_complexLocalOrientation`
* `HodgeLadder.Tests.exists_planeDegree_eq_eval`, `eval_planeOrigin_of_restrict`
* `HodgeLadder.Tests.ne_zero_of_restrict_complexLocalOrientation`: non-vacuity, `μ ≠ 0`.
* `HodgeLadder.Tests.planeOrigin_relativeHomologyProjection_bijective`,
  `subsingleton_homology_four_compl_planeOrigin`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLadder.Tests

/-- Every open of `ℙ²(ℂ)` is paracompact (upstream's `openParacompactSpace`), for upstream's
sheaf–singular comparison `rationalCohomologyAddEquivSingularCohomology`. -/
local instance : ∀ V : Opens (ComplexPoint projectivePlane), ParacompactSpace V :=
  openParacompactSpace projectivePlane

/-- `H₄(ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ) = 0`. -/
theorem subsingleton_homology_four_compl_planeOrigin :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) 4) :=
  subsingleton_homology_compl_planeOrigin_of_H' 4 (subsingleton_H'_compl_planeOrigin 1)

/-- `H₄(ℙ²(ℂ); ℚ) → H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ)` is bijective. -/
theorem planeOrigin_relativeHomologyProjection_bijective :
    Function.Bijective
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom :=
  ⟨relativeHomologyProjection_injective_of_subsingleton (pointComplementPair planeOriginPoint) 4
      subsingleton_homology_four_compl_planeOrigin,
    planeOrigin_relativeHomologyProjection_surjective⟩

/-- **The fundamental class of ℙ²(ℂ)**: exactly one `μ ∈ H₄(ℙ²(ℂ); ℚ)` restricts to the complex
local orientation at `[0 : 0 : 1]`. On a connected manifold this one-point condition is the
literature's characterization of the fundamental class of the orientation through that local
generator; that the generator is the complex one is row "Complex orientation of ℂ^p" of
`docs/conventions.md`. That `μ` restricts to `complexLocalOrientation` at every other point is not
proved here. -/
theorem existsUnique_restrict_complexLocalOrientation :
    ∃! μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint :=
  planeOrigin_relativeHomologyProjection_bijective.existsUnique _

/-- **`deg α = ⟨Ψ α, [ℙ²]⟩`**, unconditionally: for the class `μ` restricting to the complex
local orientation at `[0 : 0 : 1]`, the degree of every `α ∈ H⁴(ℙ²; ℚ)` is the evaluation of
`Ψ α` on `μ`, with `Ψ` upstream's `rationalCohomologyAddEquivSingularCohomology`. -/
theorem exists_planeDegree_eq_eval :
    ∃ μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint ∧
      ∀ α : H^(2 * 2)(projectivePlane; ℚ),
        planeDegree α = cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane))
          (2 * 2) (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2) α) μ := by
  obtain ⟨μ, hμ⟩ := exists_restrict_complexLocalOrientation
  exact ⟨μ, hμ, planeDegree_eq_eval_of_restrict μ hμ⟩

/-- **`⟨Ψ [pt], [ℙ²]⟩ = 1`**: the singular image of upstream's point class evaluates to one on
the class restricting to the complex local orientation. -/
theorem eval_planeOrigin_of_restrict
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) :
    cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2)
        (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2)
          (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin)) μ = 1 :=
  (planeDegree_eq_eval_of_restrict μ hμ _).symm.trans planeDegree_planeOrigin

/-- A class restricting to the complex local orientation at `[0 : 0 : 1]` is nonzero. -/
theorem ne_zero_of_restrict_complexLocalOrientation
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) : μ ≠ 0 := by
  rintro rfl
  have := eval_planeOrigin_of_restrict 0 hμ
  simp at this

end HodgeLadder.Tests
