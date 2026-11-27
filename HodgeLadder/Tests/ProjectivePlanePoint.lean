module

public import HodgeLadder.Tests.ProjectivePlaneLines
public import HodgeLadder.Tests.ClassNonzero
public import HodgeLadder.Tests.ContractibleAcyclic
public import LefschetzPort.Oka.Topology.Sheaves.Cohomology.Dimension
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Contractible

/-!
# The class of a point of ℙ² is nonzero

Rung `p2-point-class-nonzero`: the class of `[0 : 0 : 1]` in `H⁴(ℙ²; ℚ)`, upstream's
`cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin`, is nonzero. With
`cycle-class-multiplicative-p2` it gives `cup-positive-degree-test-p2` (decision 0010).

Route, as for `projective-line-class-nonzero` one degree up. Upstream proves the supported class
nonzero (`cycleComponentSmoothSupportCoclassSection_ne_zero` through the normalization
isomorphism), and forgetting the support is injective in degree four when the complement `U` of
the point has no rational cohomology in degree three (`forget-support-exact`). The ladder's
contractible-open lemma (`contractible-open-acyclic`) does not apply to `U` itself, which has the
homotopy type of `S²`; the ladder compares `Sheaf.H'` with singular cohomology only on contractible
opens (`contractible-open-acyclic`), so the planned deformation retraction of `U` onto a line is
replaced by three Mayer–Vietoris steps
(`TopCat.Sheaf.subsingleton_H'_sup` from the Oka port), each with contractible pieces:

1. `U = {x₀ ≠ 0} ∪ {x₁ ≠ 0}`, both copies of `ℂ²`, so `H³(U) = 0` once `H²` of their
   intersection vanishes. In the chart `x₀ ≠ 0` (coordinates `(x₁ / x₀, x₂ / x₀)`) the
   intersection is `{v₀ ≠ 0} ≅ ℂ^* × ℂ`.
2. `{v₀ ≠ 0}` is the union of the two slit pieces `v₀ ∉ (-∞, 0]` and `v₀ ∉ [0, ∞)`, star-convex
   about `(1, 1)` and `(-1, -1)`; their intersection is `{Im v₀ ≠ 0}`, so `H²` vanishes once
   `H¹(Im v₀ ≠ 0) = 0`.
3. `{Im v₀ ≠ 0}` is the disjoint union of two convex half-spaces; `H⁰(∅) = 0`
   (`TopCat.Sheaf.subsingleton_H'_bot`).

Each piece is the image of a star-convex set of `ℂ²` under the inverse of a standard chart, hence
contractible, hence acyclic in positive degrees (`contractibleOpen_subsingleton_H'`).

## Main definitions

* `HodgeLadder.Tests.planeConst`, `planeChartOpen`, `planeChartZeroOpen`
* `HodgeLadder.Tests.chartSlitPos`, `chartSlitNeg`, `chartHalfPos`, `chartHalfNeg`

## Main results

* `HodgeLadder.Tests.projectivePlane_point_class_ne_zero`: the rung.
* `HodgeLadder.Tests.cycleComponentSheafClass_ne_zero_of_subsingleton_odd`: on any smooth
  projective integral `X`, a point of coheight `p + 1` has nonzero class when `H^{2p+1}` of the
  complement of its support vanishes. Its case `p = 0` is
  `cycleComponentSheafClass_ne_zero_of_subsingleton` (rung `projective-line-class-nonzero`), its
  case `p = 1` is `cycleComponentSheafClass_ne_zero_of_subsingleton_three`.
* `HodgeLadder.Tests.subsingleton_H'_three_compl_planeOrigin`: `H³(ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ) = 0`.
* `HodgeLadder.Tests.planeOrigin_support_compl`, `planeChartOpen_zero_inf_one`: the cover.
* `HodgeLadder.Tests.contractibleSpace_planeChartOpen`, `contractibleSpace_planeChartZeroOpen`,
  `contractibleSpace_of_starConvex_image`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint Order

namespace HodgeLadder.Tests

open HodgeLadder.Normalization

/-! ### Contractible pieces of charts -/

/-- A subset of the source of a partial homeomorphism to a real vector space is contractible when
its image is star-convex and nonempty. -/
theorem contractibleSpace_of_starConvex_image {M E : Type*} [TopologicalSpace M]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (φ : OpenPartialHomeomorph M E) {s : Set M} (hs : s ⊆ φ.source)
    {c : E} (hc : StarConvex ℝ c (φ '' s)) (hne : s.Nonempty) : ContractibleSpace s := by
  have := hc.contractibleSpace (hne.image φ)
  exact (φ.homeomorphOfImageSubsetSource hs rfl).toHomotopyEquiv.contractibleSpace

/-- The rational constant sheaf on ℙ²(ℂ). -/
abbrev planeConst : TopCat.AbSheaf (TopCat.of (ComplexPoint projectivePlane)) :=
  (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint projectivePlane))).obj
    (AddCommGrpCat.of ℚ)

/-- The standard open `xᵢ ≠ 0` of ℙ²(ℂ), the source of `projectiveChart 2 i`. -/
def planeChartOpen (i : Fin 3) : Opens (ComplexPoint projectivePlane) :=
  ⟨(projectiveChart 2 i).source, (projectiveChart 2 i).open_source⟩

/-- The open of ℙ²(ℂ) cut out in the chart `x₀ ≠ 0` (coordinates `(x₁ / x₀, x₂ / x₀)`) by an
open `S ⊆ ℂ²`. -/
def planeChartZeroOpen (S : Set (Fin 2 → ℂ)) (hS : IsOpen S) :
    Opens (ComplexPoint projectivePlane) :=
  ⟨(projectiveChart 2 0).source ∩ projectiveChart 2 0 ⁻¹' S,
    (projectiveChart 2 0).isOpen_inter_preimage hS⟩

/-- `planeChartZeroOpen` carries intersections to intersections. -/
theorem planeChartZeroOpen_inf (S T : Set (Fin 2 → ℂ)) (hS : IsOpen S) (hT : IsOpen T) :
    planeChartZeroOpen S hS ⊓ planeChartZeroOpen T hT =
      planeChartZeroOpen (S ∩ T) (hS.inter hT) := by
  ext z
  simp only [planeChartZeroOpen, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- `planeChartZeroOpen` carries unions to unions. -/
theorem planeChartZeroOpen_sup (S T : Set (Fin 2 → ℂ)) (hS : IsOpen S) (hT : IsOpen T) :
    planeChartZeroOpen S hS ⊔ planeChartZeroOpen T hT =
      planeChartZeroOpen (S ∪ T) (hS.union hT) := by
  ext z
  simp only [planeChartZeroOpen, Opens.coe_sup, Opens.coe_mk, Set.mem_union, Set.mem_inter_iff,
    Set.mem_preimage]
  tauto

/-- `planeChartZeroOpen ∅` is empty. -/
theorem planeChartZeroOpen_empty : planeChartZeroOpen ∅ isOpen_empty = ⊥ := by
  ext z
  simp [planeChartZeroOpen]

/-- `planeChartZeroOpen` depends only on the set, not on the openness proof. -/
theorem planeChartZeroOpen_congr {S T : Set (Fin 2 → ℂ)} (hS : IsOpen S) (hT : IsOpen T)
    (h : S = T) : planeChartZeroOpen S hS = planeChartZeroOpen T hT := by
  subst h; rfl

/-! ### Four pieces of `ℂ^* × ℂ` -/

/-- `{v | v₀ ∈ ℂ ∖ (-∞, 0]}`. -/
def chartSlitPos : Set (Fin 2 → ℂ) := {v | v 0 ∈ Complex.slitPlane}
/-- `{v | -v₀ ∈ ℂ ∖ (-∞, 0]}`. -/
def chartSlitNeg : Set (Fin 2 → ℂ) := {v | -v 0 ∈ Complex.slitPlane}
/-- `{v | 0 < Im v₀}`. -/
def chartHalfPos : Set (Fin 2 → ℂ) := {v | 0 < (v 0).im}
/-- `{v | Im v₀ < 0}`. -/
def chartHalfNeg : Set (Fin 2 → ℂ) := {v | (v 0).im < 0}

/-- `chartSlitPos` is open. -/
theorem isOpen_chartSlitPos : IsOpen chartSlitPos :=
  Complex.isOpen_slitPlane.preimage (continuous_apply 0)
/-- `chartSlitNeg` is open. -/
theorem isOpen_chartSlitNeg : IsOpen chartSlitNeg :=
  Complex.isOpen_slitPlane.preimage (continuous_apply 0).neg
/-- `chartHalfPos` is open. -/
theorem isOpen_chartHalfPos : IsOpen chartHalfPos :=
  isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
/-- `chartHalfNeg` is open. -/
theorem isOpen_chartHalfNeg : IsOpen chartHalfNeg :=
  isOpen_lt (Complex.continuous_im.comp (continuous_apply 0)) continuous_const

/-- The two slit pieces cover `{v₀ ≠ 0}`. -/
theorem chartSlitPos_union_chartSlitNeg : chartSlitPos ∪ chartSlitNeg = {v | v 0 ≠ 0} := by
  ext v
  simp only [chartSlitPos, chartSlitNeg, Set.mem_union, Set.mem_ofPred_eq,
    Complex.mem_slitPlane_iff,
    Complex.neg_re, Complex.neg_im, ne_eq, neg_eq_zero, Complex.ext_iff, Complex.zero_re,
    Complex.zero_im, not_and_or, Left.neg_pos_iff]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h.ne'
    · exact Or.inr h
    · exact Or.inl h.ne
    · exact Or.inr h
  · rintro (h | h)
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- The two slit pieces meet in `{Im v₀ ≠ 0}`, the union of the two half-spaces. -/
theorem chartSlitPos_inter_chartSlitNeg :
    chartSlitPos ∩ chartSlitNeg = chartHalfPos ∪ chartHalfNeg := by
  ext v
  simp only [chartSlitPos, chartSlitNeg, chartHalfPos, chartHalfNeg, Set.mem_union,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Complex.mem_slitPlane_iff, Complex.neg_re,
    Complex.neg_im, ne_eq,
    neg_eq_zero, Left.neg_pos_iff]
  constructor
  · rintro ⟨h | h, h' | h'⟩
    · exact absurd (h.trans h') (lt_irrefl _)
    · rcases lt_or_gt_of_ne h' with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rintro (h | h)
    · exact ⟨Or.inr h.ne', Or.inr h.ne'⟩
    · exact ⟨Or.inr h.ne, Or.inr h.ne⟩

/-- The two half-spaces are disjoint. -/
theorem chartHalfPos_inter_chartHalfNeg : chartHalfPos ∩ chartHalfNeg = ∅ := by
  ext v
  simp only [chartHalfPos, chartHalfNeg, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro h; exact h.le

/-- The `ℝ`-linear coordinate `v ↦ v₀`. -/
def chartCoordZero : (Fin 2 → ℂ) →ₗ[ℝ] ℂ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) 0

/-- `chartSlitPos` is star-convex about `(1, 1)`. -/
theorem starConvex_chartSlitPos : StarConvex ℝ (fun _ => 1) chartSlitPos :=
  Complex.starConvex_one_slitPlane.linear_preimage chartCoordZero
/-- `chartSlitNeg` is star-convex about `(-1, -1)`. -/
theorem starConvex_chartSlitNeg : StarConvex ℝ (fun _ => -1) chartSlitNeg :=
  (show StarConvex ℝ ((-chartCoordZero) (fun _ => -1)) Complex.slitPlane by
    simpa [chartCoordZero] using Complex.starConvex_one_slitPlane).linear_preimage
      (-chartCoordZero)
/-- `chartHalfPos` is star-convex about `(i, i)`. -/
theorem starConvex_chartHalfPos : StarConvex ℝ (fun _ => Complex.I) chartHalfPos :=
  ((convex_halfSpace_im_gt 0).linear_preimage chartCoordZero).starConvex
    (show (0 : ℝ) < Complex.I.im by simp)
/-- `chartHalfNeg` is star-convex about `(-i, -i)`. -/
theorem starConvex_chartHalfNeg : StarConvex ℝ (fun _ => -Complex.I) chartHalfNeg :=
  ((convex_halfSpace_im_lt 0).linear_preimage chartCoordZero).starConvex
    (show (-Complex.I).im < (0 : ℝ) by simp)

/-- A star-convex nonempty open of the chart `x₀ ≠ 0` is contractible. -/
theorem contractibleSpace_planeChartZeroOpen (S : Set (Fin 2 → ℂ)) (hS : IsOpen S)
    {c : Fin 2 → ℂ} (hc : StarConvex ℝ c S) (hne : S.Nonempty) :
    ContractibleSpace (planeChartZeroOpen S hS) := by
  have himg : projectiveChart 2 0 '' (planeChartZeroOpen S hS : Set _) = S := by
    change projectiveChart 2 0 '' ((projectiveChart 2 0).source ∩ projectiveChart 2 0 ⁻¹' S) = S
    ext v
    refine ⟨fun ⟨z, ⟨_, hz⟩, hzv⟩ => hzv ▸ hz, fun hv => ?_⟩
    have hvt : v ∈ (projectiveChart 2 0).target := by
      rw [projectiveChart, affineChart_target]; trivial
    refine ⟨(projectiveChart 2 0).symm v, ⟨(projectiveChart 2 0).map_target hvt, ?_⟩,
      (projectiveChart 2 0).right_inv hvt⟩
    change projectiveChart 2 0 ((projectiveChart 2 0).symm v) ∈ S
    rw [(projectiveChart 2 0).right_inv hvt]; exact hv
  obtain ⟨v, hv⟩ := hne
  refine contractibleSpace_of_starConvex_image (projectiveChart 2 0)
    (s := (planeChartZeroOpen S hS : Set _)) Set.inter_subset_left (c := c)
    (by rw [himg]; exact hc) ?_
  rw [← himg] at hv
  obtain ⟨z, hz, -⟩ := hv
  exact ⟨z, hz⟩

/-- Each standard open of ℙ²(ℂ) is contractible (it is `ℂ²`). -/
theorem contractibleSpace_planeChartOpen (i : Fin 3) : ContractibleSpace (planeChartOpen i) := by
  have himg : projectiveChart 2 i '' (planeChartOpen i : Set _) = Set.univ := by
    change projectiveChart 2 i '' (projectiveChart 2 i).source = Set.univ
    rw [(projectiveChart 2 i).image_source_eq_target, projectiveChart, affineChart_target]
  refine contractibleSpace_of_starConvex_image (projectiveChart 2 i)
    (s := (planeChartOpen i : Set _)) le_rfl (c := 0) (by rw [himg]; exact starConvex_univ 0) ?_
  exact ⟨(projectiveChart 2 i).symm 0, (projectiveChart 2 i).map_target
    (by rw [projectiveChart, affineChart_target]; trivial)⟩

/-- A complex point lies in the source of the chart `xᵢ ≠ 0` exactly when its underlying point
lies in the standard open `xᵢ ≠ 0`. -/
theorem mem_projectiveChart_source_iff (i : Fin 3) (z : ComplexPoint projectivePlane) :
    z ∈ (projectiveChart 2 i).source ↔
      z.underlying ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ i := by
  rw [← projectiveChartOpen_eq, projectiveChart, affineChart_source]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Point.underlying_map]
    exact q.underlying.property
  · intro h
    exact ⟨(openEquiv _ _).symm ⟨z, h⟩,
      congrArg Subtype.val ((openEquiv _ _).apply_symm_apply _)⟩

/-- A point of the chart `xᵢ ≠ 0` lies in the standard open `xⱼ ≠ 0` exactly when coordinate
`j` of `Fin.insertNth i 1 (φᵢ z)` is nonzero. -/
theorem mem_projectiveChart_source_iff_of_mem (i j : Fin 3) (z : ComplexPoint projectivePlane)
    (hz : z ∈ (projectiveChart 2 i).source) :
    z ∈ (projectiveChart 2 j).source ↔
      Fin.insertNth (α := fun _ => ℂ) i 1 (projectiveChart 2 i z) j ≠ 0 := by
  rw [mem_projectiveChart_source_iff, ← projectiveChart_symm_mem_U_iff 2 i j,
    (projectiveChart 2 i).left_inv hz]

/-- In the chart `x₀ ≠ 0`, the standard open `x₁ ≠ 0` is `{v₀ ≠ 0}`. -/
theorem planeChartOpen_zero_inf_one :
    planeChartOpen 0 ⊓ planeChartOpen 1 =
      planeChartZeroOpen {v | v 0 ≠ 0} (isOpen_ne_fun (continuous_apply 0) continuous_const) := by
  ext z
  change z ∈ (projectiveChart 2 0).source ∧ z ∈ (projectiveChart 2 1).source ↔
    z ∈ (projectiveChart 2 0).source ∧ projectiveChart 2 0 z 0 ≠ 0
  refine and_congr_right fun hz => ?_
  rw [mem_projectiveChart_source_iff_of_mem 0 1 z hz]
  rfl

/-- The complement of `[0 : 0 : 1]` is the union of the standard opens `x₀ ≠ 0` and `x₁ ≠ 0`. -/
theorem planeOrigin_support_compl :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin).compl =
      planeChartOpen 0 ⊔ planeChartOpen 1 := by
  have hO : ∀ j : Fin 2, planeOriginPoint ∉ (projectiveChart 2 j.castSucc).source := by
    intro j hj
    rw [mem_projectiveChart_source_iff_of_mem 2 _ _ planeOriginPoint_mem_source,
      projectiveChart_planeOriginPoint] at hj
    fin_cases j <;> exact hj rfl
  ext z
  change z ∉ (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin : Set _) ↔
    z ∈ (projectiveChart 2 0).source ∨ z ∈ (projectiveChart 2 1).source
  rw [planeOrigin_support_eq_singleton, Set.mem_singleton_iff]
  constructor
  · intro hne
    obtain ⟨j, hj⟩ := exists_mem_U z.underlying
    rw [← mem_projectiveChart_source_iff] at hj
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
    · have h0 : projectiveChart 2 2 z ≠ 0 := by
        intro h0
        apply hne
        rw [← (projectiveChart 2 2).left_inv hj, h0]
        rfl
      have : projectiveChart 2 2 z 0 ≠ 0 ∨ projectiveChart 2 2 z 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h0 (funext fun m => by fin_cases m <;> simp [hc.1, hc.2])
      rcases this with h | h
      · exact Or.inl ((mem_projectiveChart_source_iff_of_mem 2 0 z hj).mpr h)
      · exact Or.inr ((mem_projectiveChart_source_iff_of_mem 2 1 z hj).mpr h)
  · rintro (h | h) rfl
    · exact hO 0 h
    · exact hO 1 h

/-! ### `H³` of the complement of the point -/

/-- `H³(ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ) = 0`. -/
theorem subsingleton_H'_three_compl_planeOrigin :
    Subsingleton (Sheaf.H' planeConst 3
      (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin).compl) := by
  have hc : ∀ (U : Opens (ComplexPoint projectivePlane)) [ContractibleSpace U] (q : ℕ),
      Subsingleton (Sheaf.H' planeConst (q + 1) U) := fun U _ q =>
    contractibleOpen_subsingleton_H' projectivePlane U (q + 1) q.succ_pos
  -- `H¹` of the two half-spaces `Im v₀ > 0`, `Im v₀ < 0` (disjoint, each convex)
  have h1 : Subsingleton (Sheaf.H' planeConst 1
      (planeChartZeroOpen chartHalfPos isOpen_chartHalfPos ⊔
        planeChartZeroOpen chartHalfNeg isOpen_chartHalfNeg)) := by
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartHalfPos starConvex_chartHalfPos
      ⟨fun _ => Complex.I, by simp [chartHalfPos]⟩
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartHalfNeg starConvex_chartHalfNeg
      ⟨fun _ => -Complex.I, by simp [chartHalfNeg]⟩
    refine TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ 0 ?_ (hc _ 0) (hc _ 0)
    rw [planeChartZeroOpen_inf,
      planeChartZeroOpen_congr _ isOpen_empty chartHalfPos_inter_chartHalfNeg,
      planeChartZeroOpen_empty]
    exact TopCat.Sheaf.subsingleton_H'_bot planeConst 0
  -- `H²` of `ℂ^* × ℂ`, covered by the two slit pieces
  have h2 : Subsingleton (Sheaf.H' planeConst 2 (planeChartOpen 0 ⊓ planeChartOpen 1)) := by
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartSlitPos starConvex_chartSlitPos
      ⟨fun _ => 1, by simp [chartSlitPos]⟩
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartSlitNeg starConvex_chartSlitNeg
      ⟨fun _ => -1, by simp [chartSlitNeg]⟩
    rw [planeChartOpen_zero_inf_one,
      planeChartZeroOpen_congr _ (isOpen_chartSlitPos.union isOpen_chartSlitNeg)
        chartSlitPos_union_chartSlitNeg.symm, ← planeChartZeroOpen_sup]
    refine TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ 1 ?_ (hc _ 1) (hc _ 1)
    rw [planeChartZeroOpen_inf,
      planeChartZeroOpen_congr _ (isOpen_chartHalfPos.union isOpen_chartHalfNeg)
        chartSlitPos_inter_chartSlitNeg, ← planeChartZeroOpen_sup]
    exact h1
  -- `H³` of the complement, covered by the two charts `x₀ ≠ 0`, `x₁ ≠ 0`
  have := contractibleSpace_planeChartOpen 0
  have := contractibleSpace_planeChartOpen 1
  rw [planeOrigin_support_compl]
  exact TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ 2 h2 (hc _ 2) (hc _ 2)

/-! ### The class -/

/-- The class of a point of coheight `p + 1` is nonzero when the complement of its support has
no rational cohomology in degree `2 p + 1`: upstream's supported class is nonzero (normalization
isomorphism), and forgetting the support is injective in degree `2 p + 2` (`forget-support-exact`).
-/
theorem cycleComponentSheafClass_ne_zero_of_subsingleton_odd (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) (p : ℕ)
    (hx : coheight x = ((p + 1 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) (2 * p + 1) (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0 := by
  intro h0
  rw [cycleComponentSheafClass_eq_forgetSupport] at h0
  have hinj := forgetSupport_injective_of_subsingleton X (cycleComponentAnalyticClosedSupport X x)
    (2 * p + 1) h
  have hs : cycleComponentSupportedInjectiveClass X x hx = 0 :=
    hinj (h0.trans (map_zero _).symm)
  apply cycleComponentSmoothSupportCoclassSection_ne_zero X x hx
  rw [← cycleComponentSupportedInjectiveClass_normalization X x hx, hs]
  exact AddEquiv.map_zero _

/-- The codimension-one criterion of `projective-line-class-nonzero` is the case `p = 0`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 1 (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0 :=
  cycleComponentSheafClass_ne_zero_of_subsingleton_odd X x 0 hx h

/-- The class of a codimension-two point is nonzero when the complement of its support has no
rational cohomology in degree three: the case `p = 1` of
`cycleComponentSheafClass_ne_zero_of_subsingleton_odd`. -/
theorem cycleComponentSheafClass_ne_zero_of_subsingleton_three (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (hx : coheight x = ((2 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 3 (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0 :=
  cycleComponentSheafClass_ne_zero_of_subsingleton_odd X x 1 hx h

/-- **`p2-point-class-nonzero`**: the class of `[0 : 0 : 1]` in `H⁴(ℙ²; ℚ)` is nonzero. -/
theorem projectivePlane_point_class_ne_zero :
    cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin ≠ 0 :=
  cycleComponentSheafClass_ne_zero_of_subsingleton_three projectivePlane planeOrigin
    coheight_planeOrigin subsingleton_H'_three_compl_planeOrigin

end HodgeLadder.Tests
