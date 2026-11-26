module

public import HodgeLadder.Cup.SupportedOpenFinal
public import HodgeLadder.Tests.CupComparison

/-!
# The supported cup comparison on an open of the projective line

Non-vacuity check for rung `cup-comparison-supported-open`: its hypotheses (`IsIntegral`,
`Smooth`, `T2Space` and paracompact opens) hold on upstream's `ℙ¹`, for every closed `Z` and every
open `V`, so the theorem applies to it. The check does not exhibit a nonzero class of a pair
`(V, V ⊓ (X ∖ Z))` with `V ≠ ⊤`, and it does not see the sign `(−1)^{pq}`.

## Main results

* `HodgeLadder.Tests.projectiveLine_cup_singular_comparison_open`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace AlgebraicTopology.Singular
  HodgeLadder.Cup

namespace HodgeLadder.Tests

local instance : ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

/-- The supported cup comparison on an open holds on `ℙ¹`, for every closed `Z` and open `V`. -/
theorem projectiveLine_cup_singular_comparison_open (Z : Closeds (ComplexPoint projectiveLine))
    (V : Opens (ComplexPoint projectiveLine)) {p q : ℕ}
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor
      (TopCat.of (ComplexPoint projectiveLine))).obj (AddCommGrpCat.of ℚ)) p
      (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) (β : H^q(projectiveLine; ℚ)) :
    supportedRationalSingularSectionCohomologyEquivRelative
        (TopCat.of (ComplexPoint projectiveLine)) Z.compl V
        (p + q) (flasqueModelOpen projectiveLine Z V (p + q) (supCupY α β (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing
        (pairVU (TopCat.of (ComplexPoint projectiveLine)) Z.compl V)
        (supportedRationalSingularSectionCohomologyEquivRelative
          (TopCat.of (ComplexPoint projectiveLine)) Z.compl V p
          (flasqueModelOpen projectiveLine Z V p α))
        (cohomologyMap ℚ q (Opens.inclusion' (X := TopCat.of (ComplexPoint projectiveLine)) V)
          (rationalCohomologyAddEquivSingularCohomology projectiveLine q β))
        (p + q) rfl :=
  cup_singular_comparison_open projectiveLine Z V α β

end HodgeLadder.Tests
