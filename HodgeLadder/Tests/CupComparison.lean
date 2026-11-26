module

public import HodgeLadder.Cup.CupSingular
public import HodgeLadder.Tests.ProjectiveLine

/-!
# The cup comparison on the projective line

Non-vacuity check for rungs `cup-singular-comparison-absolute` and `cup-graded-commutative`:
their four hypotheses (`IsIntegral`, `Smooth`, `T2Space` and paracompact opens) hold on
upstream's `ℙ¹`, so the theorems apply to it. The paracompactness of opens is upstream's theorem
`ComplexPoint.openParacompactSpace`, supplied here as a local instance.

## Main results

* `HodgeLadder.Tests.projectiveLine_cup_singular_comparison`,
  `HodgeLadder.Tests.projectiveLine_cup_gradedComm`
-/

@[expose] public noncomputable section

open AlgebraicGeometry ComplexPoint TopologicalSpace HodgeLadder.Cup

namespace HodgeLadder.Tests

local instance : ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

/-- The cup comparison holds on `ℙ¹`. -/
theorem projectiveLine_cup_singular_comparison {p q : ℕ} (x : H^p(projectiveLine; ℚ))
    (y : H^q(projectiveLine; ℚ)) :
    rationalCohomologyAddEquivSingularCohomology projectiveLine (p + q) (cup x y (p + q) rfl) =
      (((p : ℤ) * q).negOnePow : ℤ) • cupSing (TopCat.of (ComplexPoint projectiveLine))
        (rationalCohomologyAddEquivSingularCohomology projectiveLine p x)
        (rationalCohomologyAddEquivSingularCohomology projectiveLine q y) (p + q) rfl :=
  cup_singular_comparison projectiveLine x y

/-- Graded commutativity holds on `ℙ¹`. -/
theorem projectiveLine_cup_gradedComm {p q n : ℕ} (x : H^p(projectiveLine; ℚ))
    (y : H^q(projectiveLine; ℚ)) (h : p + q = n) :
    cup x y n h = ((-1 : ℤ) ^ (p * q)) • cup y x n (by omega) :=
  cup_gradedComm projectiveLine x y h

end HodgeLadder.Tests
