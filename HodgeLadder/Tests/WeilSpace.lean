module

public import HodgeLadder.Weil.Space
public import HodgeLadder.Tests.ProjectiveLineTest

/-!
# The Weil space is nonzero somewhere

Non-vacuity test for rung `weil-space`. On ℙ¹ the Weil space of the identity at `d = −1` is all
of `H²(ℙ¹; ℚ)` (`weilSpace_id_neg_one`), which holds the nonzero class of the point `∞`
(rung `projective-line-class-nonzero`). With `weilSpace_id_one` (zero at `d = 1`) this pins the
sign of the eigenvalue: a definition with the sign swapped, or one that is always `⊥`, fails one
of the two.

## Main results

* `HodgeLadder.Tests.projectiveLine_weilSpace_id_neg_one_ne_bot`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint HodgeLadder.Weil

namespace HodgeLadder.Tests

/-- The Weil space of the identity at `d = −1` is nonzero on ℙ¹: it is all of `H²(ℙ¹; ℚ)`,
which holds the nonzero point class. Fails if `weilSpace` were always `⊥`. -/
theorem projectiveLine_weilSpace_id_neg_one_ne_bot :
    weilSpace projectiveLine (𝟙 _) (-1) ≠ ⊥ := by
  rw [weilSpace_id_neg_one]
  intro h
  apply class_infty_ne_zero_of acyclic_compl_infty
  have : cycleComponentSheafClass projectiveLine infty coheight_infty' ∈
      (⊤ : Submodule ℚ H^2(projectiveLine; ℚ)) := Submodule.mem_top
  rw [h] at this
  exact (Submodule.mem_bot ℚ).mp this

end HodgeLadder.Tests
