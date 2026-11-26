module

public import HodgeLadder.Cup.SupportedOpenFinal
public import HodgeLadder.Tests.CupComparison
public import HodgeLadder.Tests.Witness
public import Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected

/-!
# The supported cup comparison on an open: instances and a nonzero case

Non-vacuity checks for rung `cup-comparison-supported-open` (rung `cup-comparison-open-test`).

* The hypotheses (`IsIntegral`, `Smooth`, `T2Space` and paracompact opens) hold on upstream's
  `ℙ¹`, for every closed `Z` and every open `V`, so the theorem applies to it
  (`projectiveLine_cup_singular_comparison_open`).
* For a closed immersion `i : Y → X` of smooth varieties, `Z = i(Y(ℂ))` and `T` upstream's chart
  neighborhood `smoothClosedSupportNeighborhood` (the open where upstream's normalized local
  classes live), the class `α = Φ_T⁻¹` of upstream's normal coclass, moved along
  `openIntersectionPairIsoSupportComplement`, is nonzero, and both sides of the theorem at
  `β = 1` are nonzero (`cup_comparison_open_nonzero`).
* On `ℙ¹` with `Y = Spec ℂ` and `i` a complex point `z₀`, this gives a nonzero class of
  `(T, T ∖ {z₀})` in degree 2 and a nonzero identity there
  (`projectiveLine_cup_comparison_open_nonzero`); upstream's `instNonemptyComplexPoint` supplies
  a complex point.

What the checks do not test: `q = 0` throughout, so the sign `(−1)^{pq}` is `1` and stays untested;
`T ≠ ⊤` is not proved (the chart neighborhood is a proper open in the cases of interest, and
nothing in the proof uses that); the product of two supported classes is not exercised.

## Main results

* `HodgeLadder.Tests.projectiveLine_cup_singular_comparison_open`
* `HodgeLadder.Tests.cup_comparison_open_nonzero`,
  `HodgeLadder.Tests.projectiveLine_cup_comparison_open_nonzero`
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

section Chart

variable (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (z : ComplexPoint Y)
  (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- The image of `Y(ℂ)` in `X(ℂ)`, as a closed set. -/
abbrev imageClosed : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), isClosed_range_map_of_closedImmersion i⟩

local instance chartHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance chartSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  chartHasDerivedCategory X

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option backward.isDefEq.respectTransparency false in
/-- **A nonzero instance of the comparison on a small open.** Let `i : Y → X` be a closed
immersion of smooth varieties of dimensions `m` and `d`, `Z = i(Y(ℂ))`, and `T` upstream's chart
neighborhood `smoothClosedSupportNeighborhood` of `i(z)` inside `V`. There is a class `α` of the
pair `(T, T ⊓ (X ∖ Z))` in degree `2(d − m)` that is nonzero, that `Φ_T` followed by the pair
isomorphism `openIntersectionPairIsoSupportComplement` sends to upstream's normal coclass
`smoothClosedSupportNormalCoclass`, and for which both sides of `cup_singular_comparison_open`
at `β = 1` are nonzero. -/
theorem cup_comparison_open_nonzero :
    ∃ α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor
        (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) (2 * (d - m))
        (homOfLE (inf_le_left : smoothClosedSupportNeighborhood X Y i m d z V hzV ⊓
          (imageClosed X Y i).compl ≤ smoothClosedSupportNeighborhood X Y i m d z V hzV)),
      α ≠ 0 ∧
      relativeCohomologyMap ℚ (2 * (d - m))
          (openIntersectionPairIsoSupportComplement (TopCat.of (ComplexPoint X))
            (Set.range (Point.map i)) (isClosed_range_map_of_closedImmersion i)
            (smoothClosedSupportNeighborhood X Y i m d z V hzV)).inv
          (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
            (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV)
            (2 * (d - m)) (flasqueModelOpen X (imageClosed X Y i)
              (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m)) α)) =
        smoothClosedSupportNormalCoclass X Y i m d z V hzV ∧
      supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
          (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV)
          (2 * (d - m) + 0) (flasqueModelOpen X (imageClosed X Y i)
            (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m) + 0)
            (supCupY α (oneY (TopCat.of (ComplexPoint X))) (2 * (d - m) + 0) rfl)) ≠ 0 ∧
      relCupSing (pairVU (TopCat.of (ComplexPoint X)) (imageClosed X Y i).compl
          (smoothClosedSupportNeighborhood X Y i m d z V hzV))
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
          (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV)
          (2 * (d - m)) (flasqueModelOpen X (imageClosed X Y i)
            (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m)) α))
        (cohomologyMap ℚ 0 (Opens.inclusion' (X := TopCat.of (ComplexPoint X))
          (smoothClosedSupportNeighborhood X Y i m d z V hzV))
          (rationalCohomologyAddEquivSingularCohomology X 0 (oneY (TopCat.of (ComplexPoint X)))))
        (2 * (d - m) + 0) rfl ≠ 0 := by
  set e := openIntersectionPairIsoSupportComplement (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (isClosed_range_map_of_closedImmersion i)
    (smoothClosedSupportNeighborhood X Y i m d z V hzV)
  set c := smoothClosedSupportNormalCoclass X Y i m d z V hzV
  set Φ := (flasqueModelOpen X (imageClosed X Y i)
      (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m))).trans
    (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
      (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m)))
  set γ := relativeCohomologyMap ℚ (2 * (d - m)) e.hom c
  have hinv : relativeCohomologyMap ℚ (2 * (d - m)) e.inv γ = c := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, e.inv_hom_id,
      relativeCohomologyMap_id]
    rfl
  have hc : c ≠ 0 := by
    intro h
    have heval := smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV
    rw [show smoothClosedSupportNormalCoclass X Y i m d z V hzV = c from rfl, h, map_zero,
      LinearMap.zero_apply] at heval
    exact zero_ne_one heval
  have hγ : γ ≠ 0 := fun h => hc (by rw [← hinv, h, map_zero])
  have hΦα : Φ (Φ.symm γ) = γ := Φ.apply_symm_apply γ
  have hL : supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
      (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (2 * (d - m) + 0) (flasqueModelOpen X (imageClosed X Y i)
        (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m) + 0)
        (supCupY (Φ.symm γ) (oneY (TopCat.of (ComplexPoint X))) (2 * (d - m) + 0) rfl)) = γ := by
    change supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
      (imageClosed X Y i).compl (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (2 * (d - m)) (flasqueModelOpen X (imageClosed X Y i)
        (smoothClosedSupportNeighborhood X Y i m d z V hzV) (2 * (d - m))
        (supCupY (Φ.symm γ) (oneY (TopCat.of (ComplexPoint X))) (2 * (d - m)) (add_zero _))) = γ
    rw [supCupY_oneY]
    exact hΦα
  refine ⟨Φ.symm γ, fun h => hγ ?_, ?_, ?_, ?_⟩
  · rw [← hΦα, h, map_zero]
  · exact (congrArg _ hΦα).trans hinv
  · rw [hL]
    exact hγ
  · have h := cup_singular_comparison_open X (imageClosed X Y i)
      (smoothClosedSupportNeighborhood X Y i m d z V hzV) (Φ.symm γ)
      (oneY (TopCat.of (ComplexPoint X)))
    simp only [Nat.cast_zero, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul] at h
    rw [← h, hL]
    exact hγ

end Chart

section ProjectiveLinePoint

local instance : SmoothOfRelativeDimension 0 point.hom := by
  dsimp [point]
  infer_instance

/-- A complex point of `ℙ¹`, as a morphism `Spec ℂ → ℙ¹`, is a closed immersion: it is a section
of the separated structure morphism. -/
theorem isClosedImmersion_complexPoint (z₀ : ComplexPoint projectiveLine) :
    IsClosedImmersion z₀.left := by
  have h : z₀.left ≫ projectiveLine.hom = 𝟙 _ := Over.w z₀
  have : IsClosedImmersion (z₀.left ≫ projectiveLine.hom) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp z₀.left projectiveLine.hom

attribute [local instance] isClosedImmersion_complexPoint

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option backward.isDefEq.respectTransparency false in
/-- **A nonzero instance on `ℙ¹`.** For a complex point `z₀` of `ℙ¹` (a closed immersion
`Spec ℂ → ℙ¹`, `m = 0`, `d = 1`) and `T` upstream's chart neighborhood of `z₀`, the pair
`(T, T ∖ {z₀})` has a nonzero class in degree 2 for which both sides of
`cup_singular_comparison_open` at `β = 1` are nonzero. -/
theorem projectiveLine_cup_comparison_open_nonzero (z₀ : ComplexPoint projectiveLine) :
    ∃ α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor
        (TopCat.of (ComplexPoint projectiveLine))).obj (AddCommGrpCat.of ℚ)) (2 * (1 - 0))
        (homOfLE (inf_le_left :
          smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial ⊓
            (imageClosed projectiveLine point z₀).compl ≤
          smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial)),
      α ≠ 0 ∧
      supportedRationalSingularSectionCohomologyEquivRelative
          (TopCat.of (ComplexPoint projectiveLine)) (imageClosed projectiveLine point z₀).compl
          (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial)
          (2 * (1 - 0) + 0) (flasqueModelOpen projectiveLine (imageClosed projectiveLine point z₀)
            (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial)
            (2 * (1 - 0) + 0)
            (supCupY α (oneY (TopCat.of (ComplexPoint projectiveLine))) (2 * (1 - 0) + 0) rfl)) ≠ 0 ∧
      relCupSing (pairVU (TopCat.of (ComplexPoint projectiveLine))
          (imageClosed projectiveLine point z₀).compl
          (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial))
        (supportedRationalSingularSectionCohomologyEquivRelative
          (TopCat.of (ComplexPoint projectiveLine)) (imageClosed projectiveLine point z₀).compl
          (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial)
          (2 * (1 - 0)) (flasqueModelOpen projectiveLine (imageClosed projectiveLine point z₀)
            (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial)
            (2 * (1 - 0)) α))
        (cohomologyMap ℚ 0 (Opens.inclusion' (X := TopCat.of (ComplexPoint projectiveLine))
          (smoothClosedSupportNeighborhood projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial))
          (rationalCohomologyAddEquivSingularCohomology projectiveLine 0
            (oneY (TopCat.of (ComplexPoint projectiveLine)))))
        (2 * (1 - 0) + 0) rfl ≠ 0 := by
  obtain ⟨α, h0, -, hL, hR⟩ :=
    cup_comparison_open_nonzero projectiveLine point z₀ 0 1 (𝟙 point) ⊤ trivial
  exact ⟨α, h0, hL, hR⟩

end ProjectiveLinePoint

end HodgeLadder.Tests
