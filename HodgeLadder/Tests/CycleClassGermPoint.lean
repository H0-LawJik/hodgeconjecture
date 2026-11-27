module

public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization
public import Other.AlgebraicTopology.LocalHomology.ChartPointClassNormalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
public import HodgeLadder.Normalization.ChartStep
public import Other.AlgebraicGeometry.Cycle.Component.PointBoundary
public import Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
meta import Lean

/-!
# Cross-check of `cycle-class-germ` at a closed point by upstream's point route

Rung `cycle-class-germ-point` (red team on `cycle-class-germ`, change H). A test with an
independent code path.

Fix a complex point `y₀` of a smooth integral projective `X` over `ℂ` of dimension `d`. The
closed point `x = y₀.underlying` has coheight `d`, its analytic support `Z` is `{y₀}`, and
`X ∖ Z_sing` is all of `X(ℂ)`. The chart `closedPointChart X y₀` is the chart of
`HodgeLadder.Normalization.adaptedChart_closedPoint`: upstream's `chartAt y₀` translated so that
`y₀` goes to `0`, with the trivial tangential factor `ℂ⁰`.

Write `T α` for upstream's singular transport at `⊤` of a supported class (the left side of
`cycle-class-germ`). Two code paths describe `T [Z]` near `y₀`.

1. `cycle-class-germ`: the flattening-chart coclasses that upstream glues on `X ∖ Z_sing`, moved
   to `e` through the chart step.
2. Upstream's point normalization (`cycleComponentSupportedInjectiveClass_point_normalization`,
   `analyticComponentPointSupportedInjectiveCoclass_relative`): `T [Z]` is
   `analyticComponentPointRelativeCoclass`, the pullback to `(X, X ∖ Z)` of the older point
   coclass `analyticPointLocalCoclass`, which is the normalized dual of the local class
   `localClassOfChart` of upstream's `localChart` at `y₀`.

The rung says that the second path gives the conclusion of the first at this chart: the point
coclass restricts on a neighbourhood of `y₀` to `chartNormalProjectionCoclass` of the chart,
exactly (no sign, no scalar). Its proof is a direct computation on the flattened neighbourhood of
the chart: the normal class there goes to `localClassOfChart` of `localChart X d y₀` under the
inclusion into `(X, X ∖ {y₀})` (radial compression, then translation by `chartAt y₀ y₀`, then
upstream's `chartTargetPointPairMap_localClass`), and both coclasses pair to 1 with it.

Independence. The module imports neither `HodgeLadder.Normalization.Germ` nor
`HodgeLadder.Normalization.Singular`, and a guard at the end of the file fails the build if it
does, or if the rung's proof uses the chart step of `cycle-class-germ`.

What the two routes share: the definition of the supported class through upstream's coclass
section `cycleComponentSmoothSupportCoclassSection` (a gluing of flattening-chart
`chartNormalProjectionCoclass` germs), upstream's
`complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, and the normalization of
ℂ^d: `standardComplexLocalClass` and `normalizedRelativeCoclass`. What they do not share:
`cycle-class-germ` uses `normalization_singular`, the stalk as a chart germ, the lift to the open
subscheme `X ∖ Z_sing`, the chart step (holomorphic transitions,
`exists_open_chartNormalProjectionCoclass_eq`) and the tangential matching; the point route uses
upstream's singleton comparison `smoothClosedSupportCoclassSection_eq_point_of_singleton`, the old
point coclass `analyticPointLocalCoclass`, and the radial computation above. So the test detects a
sign or scalar error in either route's plumbing, at `p = dim X` only. An error in the orientation
of ℂ^d (for example the ordering (Re, …, Re, Im, …, Im) in place of consecutive (Re, Im) pairs)
would cancel between the routes, so the test does not detect one; that orientation is pinned by
the rungs `cross-orientation` and `real-affine-orientation` (conventions rows "Complex orientation
of ℂ^p", "Fundamental-class normalization", "Point local coclass").

## Main definitions

* `HodgeLadder.Tests.CycleClassGermPoint.closedPointChart`: the adapted chart at `y₀`.

## Main results

* `transport_supportedClass_eq_pointRelativeCoclass`: path 2, `T [Z]` is the old point coclass
  at every closed point.
* `pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass`: the cross-check, the point
  coclass restricts near `y₀` to the chart coclass.
* `transport_restrict_eq_pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass`,
  `transport_supportedClass_eq_chartNormalProjectionCoclass_closedPoint`: the two code paths
  agree; the conclusion of `cycle-class-germ` at this chart, by path 2.
* `closedPointChart_mem_maximalAtlas`, `closedPointChart_support`,
  `mem_closedPointChart_source`, `mem_smoothSupportAmbientOpen_closedPoint`: the chart meets the
  four hypotheses of `cycle-class-germ`.
* `chartNormalProjectionCoclass_ne_zero_of_mem`, `chartNormalProjectionCoclass_closedPointChart_ne_zero`:
  non-vacuity, the right side of the rung is nonzero on every admissible `W`.
* `normalClass_toPoint_eq_localClassOfChart`, `normalizedCoclass_toPoint_eq_chartNormalProjectionCoclass`:
  the computation behind the rung, for an abstract chart `c` and a translated chart `e` of it.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology.Singular Topology
open scoped Manifold ContDiff

namespace HodgeLadder.Tests.CycleClassGermPoint

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Normalization

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The linear identification `ℂ⁰ × ℂ^d ≃ ℂ^d` of the chart `closedPointChart`. -/
abbrev closedPointChartLinear :
    ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ) :=
  ContinuousLinearEquiv.uniqueProd ℂ (Fin (dim X.left) → ℂ) (Fin 0 → ℂ)

/-- The chart of `adaptedChart_closedPoint` at `y₀`: upstream's `chartAt y₀` (which is
`localChart X (dim X.left) y₀`), translated by `-(chartAt y₀ y₀)`, then read in `ℂ⁰ × ℂ^d`. -/
def closedPointChart (y₀ : ComplexPoint X) :
    OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)) :=
  ((chartAt (Fin (dim X.left) → ℂ) y₀).trans
      (Homeomorph.addRight (-(chartAt (Fin (dim X.left) → ℂ) y₀ y₀))).toOpenPartialHomeomorph).trans
    (closedPointChartLinear X).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The source of `closedPointChart` is the source of `chartAt y₀`. -/
theorem closedPointChart_source (y₀ : ComplexPoint X) :
    (closedPointChart X y₀).source = (chartAt (Fin (dim X.left) → ℂ) y₀).source := by
  simp [closedPointChart]

/-- The normal coordinate of `closedPointChart` is `chartAt y₀ z - chartAt y₀ y₀`. -/
theorem closedPointChart_apply_snd (y₀ z : ComplexPoint X) :
    (closedPointChart X y₀ z).2 =
      chartAt (Fin (dim X.left) → ℂ) y₀ z + -(chartAt (Fin (dim X.left) → ℂ) y₀ y₀) := by
  simp [closedPointChart]

/-- The point `y₀` lies in the source of its chart. -/
theorem mem_closedPointChart_source (y₀ : ComplexPoint X) : y₀ ∈ (closedPointChart X y₀).source := by
  rw [closedPointChart_source]
  exact mem_chart_source _ y₀

/-- The scheme point under a complex point is closed, so it has coheight `dim X`. -/
theorem coheight_underlying (y₀ : ComplexPoint X) :
    Order.coheight y₀.underlying = dim X.left :=
  SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := X.hom) _
    (pointEquivClosedPoint X.hom ⟨y₀.left, Over.w y₀⟩).2

/-- The chart is holomorphic: followed by `closedPointChartLinear` it lies in Mathlib's maximal
analytic atlas of `X(ℂ)`. Hypothesis `he` of `cycle-class-germ`. -/
theorem closedPointChart_mem_maximalAtlas (y₀ : ComplexPoint X) :
    (closedPointChart X y₀).trans (closedPointChartLinear X).toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) := by
  apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource
    (e := (chartAt (Fin (dim X.left) → ℂ) y₀).trans
      (Homeomorph.addRight (-(chartAt (Fin (dim X.left) → ℂ) y₀ y₀))).toOpenPartialHomeomorph)
  · constructor
    · simp [closedPointChart]
    · intro z _
      simp [closedPointChart]
  · exact trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y₀) (translate_mem _)

/-- In the chart, the support of the closed point is the zero set of the normal coordinate.
Hypothesis `hS` of `cycle-class-germ`. -/
theorem closedPointChart_support (y₀ : ComplexPoint X) :
    ∀ z ∈ (closedPointChart X y₀).source,
      z ∈ (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)) ↔
        (closedPointChart X y₀ z).2 = 0 := by
  have hclosed : IsClosed {y₀.underlying} :=
    (pointEquivClosedPoint X.hom ⟨y₀.left, Over.w y₀⟩).2
  intro z hz
  rw [closedPointChart_source] at hz
  have hy₀ : y₀ ∈ (chartAt (Fin (dim X.left) → ℂ) y₀).source := mem_chart_source _ y₀
  change z.underlying ∈ closure {y₀.underlying} ↔ _
  rw [hclosed.closure_eq, Set.mem_singleton_iff, closedPointChart_apply_snd, add_neg_eq_zero]
  constructor
  · intro h
    rw [underlying_injective_of_locallyOfFiniteType h]
  · intro h
    rw [(chartAt (Fin (dim X.left) → ℂ) y₀).injOn hz hy₀ h]

/-- `y₀` lies in `X ∖ Z_sing`, which is all of `X(ℂ)` for a closed point. Hypothesis `hyU` of
`cycle-class-germ`. -/
theorem mem_smoothSupportAmbientOpen_closedPoint (y₀ : ComplexPoint X) :
    y₀ ∈ cycleComponentSmoothSupportAmbientOpen X y₀.underlying := by
  rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension X _
    (coheight_underlying X y₀)]
  trivial

/-- Path 2 at every closed point (coheight `dim X`) and every complex point `z` of the component:
upstream's singular transport at `⊤` of the supported cycle class, the left side of
`cycle-class-germ`, is the old point coclass `analyticComponentPointRelativeCoclass`, built from
`analyticPointLocalCoclass`. Exact, no sign. From upstream's
`cycleComponentSupportedInjectiveClass_point_normalization` and
`analyticComponentPointSupportedInjectiveCoclass_relative`. -/
theorem transport_supportedClass_eq_pointRelativeCoclass (x : X.left)
    (hx : Order.coheight x = dim X.left)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :
    complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
        ⊤ (2 * dim X.left)
        (rationalSupportAddEquivSupportedInjectiveHomology X
          (cycleComponentAnalyticClosedSupport X x) (2 * dim X.left)
          (cycleComponentSupportedInjectiveClass X x hx)) =
      analyticComponentPointRelativeCoclass X x (dim X.left) z := by
  rw [cycleComponentSupportedInjectiveClass_point_normalization X x (dim X.left) z hx,
    AddEquiv.apply_symm_apply, analyticComponentPointSupportedInjectiveCoclass_relative]

section Abstract

/-! ### The computation for an abstract chart

`c` is a chart of `M` with values in `ℂ^d` and `y₀ ∈ c.source`; `e` is a chart with values in
`ℂ⁰ × ℂ^d` whose source lies in that of `c` and whose normal coordinate is `c - c y₀`. -/

variable {M : Type} [TopologicalSpace M] {d : ℕ}
  (c : OpenPartialHomeomorph M (Fin d → ℂ)) (y₀ : M) (hy₀ : y₀ ∈ c.source)
  (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ)))
  (hsrc : e.source ⊆ c.source) (he : ∀ w ∈ e.source, (e w).2 = c w + -(c y₀))
  (hy : y₀ ∈ e.source)

include he hy in
/-- The normal coordinate of `e` vanishes at `y₀`. -/
theorem normal_eq_zero_of_translate : (e y₀).2 = 0 := by rw [he y₀ hy, add_neg_cancel]

include he in
/-- On the normal fibre of the flattened neighbourhood of `e` at `y₀`, the chart `c` reads the
radial compression of the fibre coordinate, translated by `c y₀`. -/
theorem chart_flattenedSupportHomeomorph (v : Fin d → ℂ) :
    c (flattenedSupportHomeomorph (Fin 0 → ℂ) d e y₀ hy ((0 : Fin 0 → ℂ), v) : M) =
      OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
        (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy) v + c y₀ := by
  have hw := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e y₀ hy
    (flattenedSupportHomeomorph (Fin 0 → ℂ) d e y₀ hy ((0 : Fin 0 → ℂ), v)).2
  have h1 := he _ hw
  rw [flattenedSupportHomeomorph_coordinates] at h1
  have h0 : e y₀ = ((e y₀).1, (0 : Fin d → ℂ)) :=
    Prod.ext rfl (normal_eq_zero_of_translate c y₀ e he hy)
  rw [h0, univBall_zero_tangent_normal _ _ _ _ (flattenedSupportRadius_pos _ _ e y₀ hy)] at h1
  rw [h1, neg_add_cancel_right]

/-- The normal fibre of the flattened neighbourhood, read in the target of `c`: radial
compression followed by translation by `c y₀`. -/
def flattenedTargetPairMap :
    puncturedPair ℂ d ⟶ neighborhoodPointComplementPair c.target (c y₀) :=
  let r := flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy
  let R := OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r
  have hmem (w : Fin d → ℂ) : R w + c y₀ ∈ c.target := by
    rw [← chart_flattenedSupportHomeomorph c y₀ e he hy w]
    exact c.map_source (hsrc (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e y₀ hy
      (flattenedSupportHomeomorph (Fin 0 → ℂ) d e y₀ hy ((0 : Fin 0 → ℂ), w)).2))
  have hne (w : Fin d → ℂ) (hw : w ≠ 0) : R w + c y₀ ≠ c y₀ := by
    intro h
    apply hw
    apply injective_complexUnivBall d 0 r
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    simpa using h
  have hcont : Continuous (fun w => R w + c y₀) :=
    (continuous_complexUnivBall d 0 r).add continuous_const
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨R w + c y₀, hmem w⟩, hcont.subtype_mk hmem⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨R w.1 + c y₀, hmem w.1⟩, hne w.1 w.2⟩,
      ((hcont.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩) rfl

/-- In ambient coordinates `flattenedTargetPairMap` is the centred radial map followed by the
translation by `c y₀`. -/
theorem flattenedTargetPairMap_comp_inclusion :
    flattenedTargetPairMap c y₀ e hsrc he hy ≫
        neighborhoodPointComplementPairMap c.target (c y₀) =
      centeredComplexEmbeddingPair d
        (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy))
        (continuous_complexUnivBall d 0 _) (injective_complexUnivBall d 0 _) 0 ≫
      translationPointComplementPairMap (Fin d → ℂ) (c y₀) := by
  have h (w : Fin d → ℂ) :
      OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy) w + c y₀ =
        (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy) (w + 0) -
          OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
            (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy) 0) + c y₀ := by
    simp only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero]
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    exact Subtype.ext (h w.1)
  · ext w
    exact h w

/-- The radial target map followed by the inverse of `c` carries the standard complex class to
`localClassOfChart` of `c`, with coefficient 1. -/
theorem flattenedTargetPairMap_localClass :
    relativeHomologyMap ℚ (2 * d)
      (flattenedTargetPairMap c y₀ e hsrc he hy ≫ chartTargetInverseAtSourcePairMap d c y₀)
      (standardComplexLocalClass ℚ d) = localClassOfChart d c y₀ hy₀ := by
  apply chartTargetPointPairMap_localClass
  rw [flattenedTargetPairMap_comp_inclusion, relativeHomologyMap_comp, LinearMap.comp_apply,
    centeredComplexUnivBall_preserves_standardComplexLocalClass d 0 _
      (flattenedSupportRadius_pos _ _ e y₀ hy) 0]

variable (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (hyS : y₀ ∈ S)

/-- The normal fibre, the flattening pair isomorphism and the inclusion into `(M, M ∖ {y₀})`
compose to the radial target map followed by the inverse of `c`. -/
theorem normalFiber_toPoint :
    normalSliceSection (Fin 0 → ℂ) d ≫
      (flattenedSupportPairIso (Fin 0 → ℂ) d e y₀ hy S hS
        (normal_eq_zero_of_translate c y₀ e he hy)).hom ≫
      neighborhoodSupportToPointPairMap
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d e y₀ hy : Set M) S y₀ hyS =
      flattenedTargetPairMap c y₀ e hsrc he hy ≫ chartTargetInverseAtSourcePairMap d c y₀ := by
  have h (w : Fin d → ℂ) :
      (flattenedSupportHomeomorph (Fin 0 → ℂ) d e y₀ hy ((0 : Fin 0 → ℂ), w) : M) =
        c.symm (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (flattenedSupportRadius (Fin 0 → ℂ) d e y₀ hy) w + c y₀) := by
    rw [← chart_flattenedSupportHomeomorph c y₀ e he hy w, c.left_inv]
    exact hsrc (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e y₀ hy
      (flattenedSupportHomeomorph (Fin 0 → ℂ) d e y₀ hy ((0 : Fin 0 → ℂ), w)).2)
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    exact Subtype.ext (h w.1)
  · ext w
    exact h w

include hsrc in
/-- The normal class of the flattened neighbourhood of `e` goes to `localClassOfChart` of `c`
under the inclusion into `(M, M ∖ {y₀})`. Exact, coefficient 1. -/
theorem normalClass_toPoint_eq_localClassOfChart :
    relativeHomologyMap ℚ (2 * d)
      (neighborhoodSupportToPointPairMap
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d e y₀ hy : Set M) S y₀ hyS)
      (flattenedSupportNormalClass (Fin 0 → ℂ) d e y₀ hy S hS
        (normal_eq_zero_of_translate c y₀ e he hy)) =
      localClassOfChart d c y₀ hy₀ := by
  rw [flattenedSupportNormalClass_eq_normalFiber, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, Category.assoc, normalFiber_toPoint c y₀ e hsrc he hy S hS hyS]
  exact flattenedTargetPairMap_localClass c y₀ hy₀ e hsrc he hy

include hsrc he in
/-- The normalized dual of `localClassOfChart` of `c`, pulled back to the flattened
neighbourhood of `e`, is the chart coclass of `e` there. Exact, no sign, no scalar. -/
theorem normalizedCoclass_toPoint_eq_chartNormalProjectionCoclass
    (hne : localClassOfChart d c y₀ hy₀ ≠ 0) :
    relativeCohomologyMap ℚ (2 * d)
      (neighborhoodSupportToPointPairMap
        (flattenedSupportNeighborhood (Fin 0 → ℂ) d e y₀ hy : Set M) S y₀ hyS)
      (normalizedRelativeCoclass (localClassOfChart d c y₀ hy₀) hne) =
    chartNormalProjectionCoclass (Fin 0 → ℂ) d e S hS
      (flattenedSupportNeighborhood (Fin 0 → ℂ) d e y₀ hy)
      (flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e y₀ hy) := by
  apply chartNormalProjectionCoclass_unique (Fin 0 → ℂ) d e S hS y₀ hy
    (normal_eq_zero_of_translate c y₀ e he hy)
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    normalClass_toPoint_eq_localClassOfChart c y₀ hy₀ e hsrc he hy S hS hyS,
    normalizedRelativeCoclass_pairing_self]

end Abstract

set_option backward.isDefEq.respectTransparency false in
/-- A chart coclass is nonzero on every open `W` of the source that meets the support. -/
theorem chartNormalProjectionCoclass_ne_zero_of_mem {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (W : Opens M) (hW : (W : Set M) ⊆ e.source)
    (y : M) (hyW : y ∈ W) (hy : y ∈ e.source) (h0 : (e y).2 = 0) :
    chartNormalProjectionCoclass E c e S hS W hW ≠ 0 := by
  intro hz
  let er := e.restrOpen W W.isOpen
  have hyr : y ∈ er.source := ⟨hy, hyW⟩
  have hSr : ∀ z ∈ er.source, z ∈ S ↔ (er z).2 = 0 := fun z hz => hS z hz.1
  have hF := flattenedSupportNeighborhood_subset_source E c er y hyr
  have hFW : (flattenedSupportNeighborhood E c er y hyr : Set M) ⊆ (W : Set M) :=
    fun _ hz => (hF hz).2
  have h1 := chartNormalProjectionCoclass_apply_normalClass E c er S hSr y hyr h0
  have h2 : chartNormalProjectionCoclass E c er S hSr
      (flattenedSupportNeighborhood E c er y hyr) hF =
      relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hFW S)
        (chartNormalProjectionCoclass E c e S hS W hW) := by
    rw [chartNormalProjectionCoclass_restrict]
    rfl
  rw [h2, hz, map_zero, map_zero] at h1
  exact zero_ne_one ((LinearMap.zero_apply _).symm.trans h1)

/-- Non-vacuity: the right side of the rung is nonzero on every open `W ∋ y₀` inside the chart
source. -/
theorem chartNormalProjectionCoclass_closedPointChart_ne_zero (y₀ : ComplexPoint X)
    (W : Opens (ComplexPoint X))
    (hW : (W : Set (ComplexPoint X)) ⊆ (closedPointChart X y₀).source) (hyW : y₀ ∈ W) :
    chartNormalProjectionCoclass (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀)
      (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X))
      (closedPointChart_support X y₀) W hW ≠ 0 :=
  chartNormalProjectionCoclass_ne_zero_of_mem _ _ _ _ _ W hW y₀ hyW
    (mem_closedPointChart_source X y₀) (by rw [closedPointChart_apply_snd, add_neg_cancel])

/-- The cross-check (rung `cycle-class-germ-point`). At the chart `closedPointChart X y₀`, the old
point coclass of the closed point `y₀.underlying` restricts on an open `W ∋ y₀` inside the chart
source to upstream's `chartNormalProjectionCoclass` of the chart. Exact: no sign, no scalar.

Both sides are normalized against the complex orientation of `ℂ^d` with consecutive
`(Re, Im)` pairs (conventions rows "Complex orientation of ℂ^p" and "Fundamental-class
normalization", "Point local coclass"): the left side is dual to `localClassOfChart` of
`localChart X d y₀`, the right
side is the pullback along `w ↦ chartAt y₀ w - chartAt y₀ y₀` of the class dual to
`standardComplexLocalClass`. -/
theorem pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass (y₀ : ComplexPoint X)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left y₀.underlying ≫ X.hom))) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ (closedPointChart X y₀).source),
      y₀ ∈ W ∧
      relativeCohomologyMap ℚ (2 * dim X.left)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)))
          (analyticComponentPointRelativeCoclass X y₀.underlying (dim X.left) z) =
        chartNormalProjectionCoclass (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀)
          (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X))
          (closedPointChart_support X y₀) W hW := by
  have hy := mem_closedPointChart_source X y₀
  have hyS : y₀ ∈ cycleComponentSupport X y₀.underlying :=
    show y₀.underlying ∈ closure {y₀.underlying} from subset_closure rfl
  have hz : cycleComponentMap X y₀.underlying z = y₀ := by
    have h := cycleComponentSupport_eq_singleton_of_coheight_eq_dimension X (dim X.left)
      y₀.underlying (coheight_underlying X y₀) z
    rw [h] at hyS
    exact hyS.symm
  refine ⟨flattenedSupportNeighborhood (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀) y₀ hy,
    flattenedSupportNeighborhood_subset_source _ _ _ y₀ hy,
    mem_flattenedSupportNeighborhood _ _ _ y₀ hy, ?_⟩
  change relativeCohomologyMap ℚ (2 * dim X.left)
      (neighborhoodSupportInclusionPairMap
        (W := (flattenedSupportNeighborhood (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀) y₀ hy :
          Set (ComplexPoint X)))
        (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
        (cycleComponentSupport X y₀.underlying))
      (relativeCohomologyMap ℚ (2 * dim X.left)
        (neighborhoodSupportToPointPairMap ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
          (cycleComponentSupport X y₀.underlying) (cycleComponentMap X y₀.underlying z)
          (range_cycleComponentMap_subset X y₀.underlying ⟨z, rfl⟩))
        (analyticPointLocalCoclass X (dim X.left) (cycleComponentMap X y₀.underlying z))) = _
  erw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  generalize range_cycleComponentMap_subset X y₀.underlying ⟨z, rfl⟩ = hw
  generalize cycleComponentMap X y₀.underlying z = w at hw hz ⊢
  subst hz
  exact normalizedCoclass_toPoint_eq_chartNormalProjectionCoclass
    (chartAt (Fin (dim X.left) → ℂ) w) w (mem_chart_source _ w) (closedPointChart X w)
    (closedPointChart_source X w).le (fun v _ => closedPointChart_apply_snd X w v) hy
    (cycleComponentSupport X w.underlying) (closedPointChart_support X w) hw
    (analyticPointLocalHomologyClass_ne_zero X (dim X.left) w)

/-- The two code paths agree at the closed point. On an open `W ∋ y₀` inside the chart source,
the restriction of `T [Z]` (the left side of `cycle-class-germ`) equals the restriction of the old
point coclass (path 2), and that equals `chartNormalProjectionCoclass` of the chart (the right
side of `cycle-class-germ`). Exact, no sign. -/
theorem transport_restrict_eq_pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass
    (y₀ : ComplexPoint X)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left y₀.underlying ≫ X.hom))) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ (closedPointChart X y₀).source),
      y₀ ∈ W ∧
      relativeCohomologyMap ℚ (2 * dim X.left)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X
            (cycleComponentAnalyticClosedSupport X y₀.underlying) ⊤ (2 * dim X.left)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X y₀.underlying) (2 * dim X.left)
              (cycleComponentSupportedInjectiveClass X y₀.underlying (coheight_underlying X y₀)))) =
        relativeCohomologyMap ℚ (2 * dim X.left)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)))
          (analyticComponentPointRelativeCoclass X y₀.underlying (dim X.left) z) ∧
      relativeCohomologyMap ℚ (2 * dim X.left)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)))
          (analyticComponentPointRelativeCoclass X y₀.underlying (dim X.left) z) =
        chartNormalProjectionCoclass (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀)
          (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X))
          (closedPointChart_support X y₀) W hW := by
  obtain ⟨W, hW, hyW, h⟩ := pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass X y₀ z
  exact ⟨W, hW, hyW, by rw [transport_supportedClass_eq_pointRelativeCoclass X _ _ z], h⟩

/-- The conclusion of `transport_supportedClass_eq_chartNormalProjectionCoclass`
(`cycle-class-germ`) at the closed point `y₀.underlying`, the chart `closedPointChart X y₀` and
`y = y₀`, obtained by path 2 alone. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_closedPoint
    (y₀ : ComplexPoint X) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ (closedPointChart X y₀).source),
      y₀ ∈ W ∧
      relativeCohomologyMap ℚ (2 * dim X.left)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X
            (cycleComponentAnalyticClosedSupport X y₀.underlying) ⊤ (2 * dim X.left)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X y₀.underlying) (2 * dim X.left)
              (cycleComponentSupportedInjectiveClass X y₀.underlying (coheight_underlying X y₀)))) =
        chartNormalProjectionCoclass (Fin 0 → ℂ) (dim X.left) (closedPointChart X y₀)
          (cycleComponentAnalyticClosedSupport X y₀.underlying : Set (ComplexPoint X))
          (closedPointChart_support X y₀) W hW := by
  have hy₀ : y₀ ∈ cycleComponentSupport X y₀.underlying :=
    show y₀.underlying ∈ closure {y₀.underlying} from subset_closure rfl
  obtain ⟨z, -⟩ := (range_cycleComponentMap X y₀.underlying).ge hy₀
  obtain ⟨W, hW, hyW, h1, h2⟩ :=
    transport_restrict_eq_pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass X y₀ z
  exact ⟨W, hW, hyW, h1.trans h2⟩

end HodgeLadder.Tests.CycleClassGermPoint

-- Independence guard (red team on `cycle-class-germ-point`): this module does not see
-- `cycle-class-germ` or `normalization-singular`, and the rung's proof does not use the chart
-- step of `cycle-class-germ`. A docstring cannot precede `run_cmd`.
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for m in [`HodgeLadder.Normalization.Germ, `HodgeLadder.Normalization.Singular] do
    if (env.getModuleIdx? m).isSome then
      throwError "cycle-class-germ-point must not import {m}"
  let forbidden : List Name :=
    [`AlgebraicTopology.Singular.exists_open_chartNormalProjectionCoclass_eq,
     `AlgebraicTopology.Singular.exists_open_complexDifferentiable_localClass_invariance,
     `AlgebraicGeometry.ComplexPoint.smoothClosedSupportCoclassStalk_eq_chartGerm,
     `HodgeLadder.Normalization.analyticAt_transition_of_factor,
     `HodgeLadder.Normalization.analyticAt_transition_of_mem_maximalAtlas]
  for f in forbidden do
    unless env.contains f do throwError "independence guard is stale: {f}"
  let rec go (fuel : Nat) (todo : List Name) (seen : NameSet) : NameSet :=
    match fuel, todo with
    | 0, _ | _, [] => seen
    | fuel + 1, n :: rest =>
      if seen.contains n then go fuel rest seen else
      match env.find? n with
      | some ci => go fuel ((ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList ++ rest)
          (seen.insert n)
      | none => go fuel rest (seen.insert n)
  let s := go 1000000
    [`HodgeLadder.Tests.CycleClassGermPoint.pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass] {}
  for f in forbidden do
    if s.contains f then throwError "cycle-class-germ-point uses {f}"
