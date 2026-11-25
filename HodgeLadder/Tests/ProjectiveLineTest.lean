module

public import HodgeLadder.Tests.ProjectiveLinePoint
public import HodgeLadder.Tests.ClassNonzero
public import HodgeLadder.Tests.CurveH2
public import HodgeLadder.Divisor.LefschetzEquality

/-!
# The ℙ¹ test case

Rungs `projective-line-class-nonzero`, `projective-line-h2` and `projective-line-test`. On
upstream's ℙ¹ the class of the point `[1 : 0]` is nonzero, `H²(ℙ¹; ℚ)` is one-dimensional and
spanned by it, and `Hdg^1(ℙ¹; ℚ) = algebraicCycleClassSpan ℙ¹ 1` is one-dimensional. This is the
degree-two non-vacuity test for `lefschetz-1-1-equality`.

## Main results

* `HodgeLadder.Tests.projectiveLine_class_ne_zero`
* `HodgeLadder.Tests.projectiveLine_h2`
* `HodgeLadder.Tests.projectiveLine_test`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Order

namespace HodgeLadder.Tests

lemma coheight_infty' : coheight infty = ((1 : ℕ) : ℕ∞) := by
  rw [Nat.cast_one]; exact coheight_infty

variable (hacyc : ∀ q : ℕ, 0 < q →
  Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor
    (TopCat.of (ComplexPoint projectiveLine))).obj (AddCommGrpCat.of ℚ)) q
    (cycleComponentAnalyticClosedSupport projectiveLine infty).compl))

include hacyc

lemma class_infty_ne_zero_of : cycleComponentSheafClass projectiveLine infty coheight_infty' ≠ 0 :=
  cycleComponentSheafClass_ne_zero_of_subsingleton projectiveLine infty coheight_infty'
    (hacyc 1 one_pos)

lemma finrank_h2_of : Module.finrank ℚ (H^(2 * 1)(projectiveLine; ℚ)) = 1 :=
  finrank_H2_of_subsingleton projectiveLine infty coheight_infty' (hacyc 1 one_pos)
    (hacyc 2 two_pos)

lemma span_eq_top_of : algebraicCycleClassSpan projectiveLine 1 = ⊤ := by
  have hle : Submodule.span ℚ {cycleComponentSheafClass projectiveLine infty coheight_infty'} ≤
      algebraicCycleClassSpan projectiveLine 1 :=
    le_sSup ⟨infty, coheight_infty', rfl⟩
  have hall := (finrank_eq_one_iff_of_nonzero' _ (class_infty_ne_zero_of hacyc)).mp
    (finrank_h2_of hacyc)
  refine top_le_iff.mp fun w _ => hle ?_
  obtain ⟨c, hc⟩ := hall w
  exact hc ▸ Submodule.smul_mem _ c (Submodule.subset_span rfl)

omit hacyc in
lemma hdg_eq_span : Hdg^1(projectiveLine; ℚ) = algebraicCycleClassSpan projectiveLine 1 :=
  lefschetzOneOneEquality_holds projectiveLine

lemma finrank_hdg_of : Module.finrank ℚ (Hdg^1(projectiveLine; ℚ)) = 1 := by
  rw [hdg_eq_span, span_eq_top_of hacyc, finrank_top]
  exact finrank_h2_of hacyc

end HodgeLadder.Tests
