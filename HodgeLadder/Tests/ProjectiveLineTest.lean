module

public import HodgeLadder.Tests.ProjectiveLinePoint
public import HodgeLadder.Tests.ClassNonzero
public import HodgeLadder.Tests.CurveH2
public import HodgeLadder.Divisor.LefschetzEquality
public import HodgeLadder.Tests.ContractibleAcyclic

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

omit hacyc in
/-- The complement of `[1 : 0]` has no rational cohomology in positive degrees. -/
theorem acyclic_compl_infty (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor
      (TopCat.of (ComplexPoint projectiveLine))).obj (AddCommGrpCat.of ℚ)) q
      (cycleComponentAnalyticClosedSupport projectiveLine infty).compl) := by
  have : ContractibleSpace ↥(cycleComponentAnalyticClosedSupport projectiveLine infty).compl :=
    complInftyHomeomorph.toHomotopyEquiv.contractibleSpace
  exact contractibleOpen_subsingleton_H' projectiveLine _ q hq

omit hacyc in
/-- **`projective-line-class-nonzero`**: the class of a point of ℙ¹ is nonzero in degree two. -/
theorem projectiveLine_class_ne_zero :
    ∃ (x : projectiveLine.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
      cycleComponentSheafClass projectiveLine x hx ≠ 0 ∧
        algebraicCycleClassSpan projectiveLine 1 ≠ ⊥ := by
  refine ⟨infty, coheight_infty', class_infty_ne_zero_of acyclic_compl_infty, fun h => ?_⟩
  have h1 := finrank_h2_of acyclic_compl_infty
  rw [← finrank_top, ← span_eq_top_of acyclic_compl_infty, h, finrank_bot] at h1
  exact zero_ne_one h1

omit hacyc in
/-- **`projective-line-h2`**: `H²(ℙ¹; ℚ)` is one-dimensional and spanned by divisor classes. -/
theorem projectiveLine_h2 :
    Module.finrank ℚ (H^(2 * 1)(projectiveLine; ℚ)) = 1 ∧
      algebraicCycleClassSpan projectiveLine 1 = ⊤ :=
  ⟨finrank_h2_of acyclic_compl_infty, span_eq_top_of acyclic_compl_infty⟩

omit hacyc in
/-- **`projective-line-test`**: on ℙ¹, `Hdg^1 = algebraicCycleClassSpan 1`, and both are
one-dimensional over `ℚ`. -/
theorem projectiveLine_test :
    Hdg^1(projectiveLine; ℚ) = algebraicCycleClassSpan projectiveLine 1 ∧
      Module.finrank ℚ (Hdg^1(projectiveLine; ℚ)) = 1 :=
  ⟨hdg_eq_span, finrank_hdg_of acyclic_compl_infty⟩

end HodgeLadder.Tests
