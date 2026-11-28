module

public import HodgeLadder.Local.ClassPullback
public import HodgeLadder.Tests.P1p1Fibres
public import HodgeLadder.Normalization.GermNoReg

/-!
# The chart coclass of `∞` pulled back along the first projection of ℙ¹ × ℙ¹

Instance of rung `local-class-pullback-submersion` at `pr₁ : ℙ¹ × ℙ¹ → ℙ¹`, the first use named by
`fibre-class-pullback` (`pr₁*[∞] = [{∞} × ℙ¹]`).

Charts. On ℙ¹, `lineAdaptedChart` is the chart `x₀ ≠ 0` (`lineChart`, coordinate `x₁ / x₀`) with
an empty tangent block: values in `ℂ^0 × ℂ^1`. On ℙ¹ × ℙ¹, `p1p1FstChart` is the product chart
`p1p1Chart` (first factor first) followed by `fstSplit : ℂ² ≃ ℂ^1 × ℂ^1`,
`(v₀, v₁) ↦ ((v₁), (v₀))`: tangent block the second coordinate, normal block the first. In these
charts `pr₁` is the coordinate projection `(v₁, v₀) ↦ (·, v₀)`, and the two normal coordinates
agree by `rfl` up to `p1p1Chart_apply_zero`.

Both charts are holomorphic in the sense of `cycle-class-germ`: followed by a `ℂ`-linear equivalence
onto `ℂ^d` they lie in the maximal analytic atlas (`lineAdaptedChart_holomorphic`,
`p1p1FstChart_holomorphic`). `fstSplit` enters only as the witness `L = fstSplit.symm` of hypothesis
`he` of `cycle-class-germ`; the coclass of `p1p1FstChart` reads only its normal coordinate, which is
`lineChart ∘ pr₁` (`p1p1FstChart_apply_snd`), so the reordering contributes no sign (row "Pullback
of local classes along a chart projection" of `docs/conventions.md`). `cycle-class-germ` states `he`
over `Fin (dim X.left) → ℂ`; these lemmas state it over `Fin 1 → ℂ` and `Fin 2 → ℂ`, and feed it
after `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` in a statement generalized
over `d`.

## Main definitions

* `HodgeLadder.Tests.lineAdaptedChart`, `HodgeLadder.Tests.fstSplit`,
  `HodgeLadder.Tests.p1p1FstChart`

## Main results

* `HodgeLadder.Tests.mem_infty_support_iff`, `HodgeLadder.Tests.mem_p1p1FibreFst_support_iff'`:
  both charts are adapted (`{∞}` and `{∞} × ℙ¹` are the zero sets of the normal coordinates).
* `HodgeLadder.Tests.map_fst_mem_infty_support_iff`: `pr₁⁻¹ {∞} = {∞} × ℙ¹` on complex points.
* `HodgeLadder.Tests.p1p1Fst_chartNormalProjectionCoclass_pullback`: the pullback along `pr₁` of
  the chart coclass of `{∞}` is the chart coclass of `{∞} × ℙ¹`. Sign `+`, exact.
* `HodgeLadder.Tests.lineAdaptedChart_holomorphic`, `HodgeLadder.Tests.p1p1FstChart_holomorphic`,
  `HodgeLadder.Tests.p1p1CornerPoint_mem_p1p1FstChart_source`: the hypotheses `he`, `hy` of
  `cycle-class-germ` for the two charts (the corner `(∞, ∞)` lies in the source).
* `HodgeLadder.Tests.p1p1Fst_chartNormalProjectionCoclass_ne_zero`: non-vacuity, both chart
  coclasses are nonzero near the corner and near `∞`.
* `HodgeLadder.Tests.mapsTo_fst_p1p1FstChart_source`,
  `HodgeLadder.Tests.p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero`: non-vacuity at
  one admissible pair, the two chart sources, where the identity equates nonzero classes.
* `HodgeLadder.Tests.transport_supportedClass_eq_chartNormalProjectionCoclass_source_of_dim`:
  `cycle-class-germ` (source form) with `he` over `Fin d → ℂ`, the `dim` substitution above.
* `HodgeLadder.Tests.infty_transport_eq_lineAdaptedChart_coclass`,
  `HodgeLadder.Tests.p1p1FibreFst_transport_eq_p1p1FstChart_coclass`: both charts fed to it, so
  on the chart sources each chart coclass is the restriction of the transported cycle class.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology AlgebraicTopology.Singular TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.LocalClassPullback

/-- The chart `x₀ ≠ 0` of ℙ¹ with an empty tangent block, values in `ℂ^0 × ℂ^1`. -/
def lineAdaptedChart :
    OpenPartialHomeomorph (ComplexPoint projectiveLine) ((Fin 0 → ℂ) × (Fin 1 → ℂ)) :=
  lineChart.trans (ContinuousLinearEquiv.uniqueProd ℂ (Fin 1 → ℂ)
    (Fin 0 → ℂ)).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The source of `lineAdaptedChart` is the source of `lineChart`. -/
@[simp] theorem lineAdaptedChart_source : lineAdaptedChart.source = lineChart.source := by
  simp [lineAdaptedChart]

/-- The normal coordinate of `lineAdaptedChart` is `lineChart`. -/
theorem lineAdaptedChart_apply_snd (b : ComplexPoint projectiveLine) :
    (lineAdaptedChart b).2 = lineChart b := rfl

/-- The splitting `ℂ² ≃ ℂ^1 × ℂ^1`, `(v₀, v₁) ↦ ((v₁), (v₀))`: tangent block the second
coordinate, normal block the first. A coordinate permutation, `ℂ`-linear. -/
def fstSplit : (Fin 2 → ℂ) ≃L[ℂ] ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => (fun _ => v 1, fun _ => v 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => ![p.2 0, p.1 0]
      left_inv := fun v => funext fun i => by fin_cases i <;> rfl
      right_inv := fun p => Prod.ext (funext fun i => by fin_cases i; rfl)
        (funext fun i => by fin_cases i; rfl) }

/-- The product chart of ℙ¹ × ℙ¹ split by `fstSplit`, values in `ℂ^1 × ℂ^1`: normal coordinate
`x₁ / x₀ ∘ pr₁`, tangent coordinate `x₁ / x₀ ∘ pr₂`. -/
def p1p1FstChart : OpenPartialHomeomorph (ComplexPoint p1p1) ((Fin 1 → ℂ) × (Fin 1 → ℂ)) :=
  p1p1Chart.trans fstSplit.toHomeomorph.toOpenPartialHomeomorph

/-- The source of `p1p1FstChart` is the source of `p1p1Chart`. -/
@[simp] theorem p1p1FstChart_source : p1p1FstChart.source = p1p1Chart.source := by
  simp [p1p1FstChart]

/-- The normal coordinate of `p1p1FstChart` is the chart of the first projection. -/
theorem p1p1FstChart_apply_snd (z : ComplexPoint p1p1) :
    (p1p1FstChart z).2 = lineChart (Point.map prod.fst z) := by
  funext i
  fin_cases i
  exact p1p1Chart_apply_zero z

/-- The complex support of `∞` in ℙ¹ is the set of complex points over `∞`. -/
theorem mem_infty_support_iff (b : ComplexPoint projectiveLine) :
    b ∈ (cycleComponentAnalyticClosedSupport projectiveLine infty :
        Set (ComplexPoint projectiveLine)) ↔ b.underlying = infty := by
  have hclosed : IsClosed {inftyPoint.underlying} :=
    (pointEquivClosedPoint projectiveLine.hom ⟨inftyPoint.left, Over.w inftyPoint⟩).2
  rw [inftyPoint_underlying] at hclosed
  change b.underlying ∈ closure {infty} ↔ _
  rw [hclosed.closure_eq, Set.mem_singleton_iff]

/-- `lineAdaptedChart` is adapted to `{∞}`. -/
theorem lineAdaptedChart_adapted :
    ∀ b ∈ lineAdaptedChart.source,
      b ∈ (cycleComponentAnalyticClosedSupport projectiveLine infty :
          Set (ComplexPoint projectiveLine)) ↔ (lineAdaptedChart b).2 = 0 := by
  intro b hb
  rw [lineAdaptedChart_source] at hb
  rw [mem_infty_support_iff, underlying_eq_infty_iff b hb, lineAdaptedChart_apply_snd]
  exact ⟨fun h => funext fun i => by fin_cases i; exact h, fun h => congrFun h 0⟩

/-- On complex points, `pr₁⁻¹ {∞} = {∞} × ℙ¹`. -/
theorem map_fst_mem_infty_support_iff (z : ComplexPoint p1p1) :
    Point.map prod.fst z ∈ (cycleComponentAnalyticClosedSupport projectiveLine infty :
        Set (ComplexPoint projectiveLine)) ↔
      z ∈ (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst : Set (ComplexPoint p1p1)) := by
  rw [mem_infty_support_iff, SetLike.mem_coe, mem_p1p1FibreFst_support_iff_fst]

/-- `p1p1FstChart` is adapted to `{∞} × ℙ¹`. -/
theorem mem_p1p1FibreFst_support_iff' :
    ∀ z ∈ p1p1FstChart.source,
      z ∈ (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst : Set (ComplexPoint p1p1)) ↔
        (p1p1FstChart z).2 = 0 := by
  intro z hz
  rw [p1p1FstChart_source] at hz
  rw [SetLike.mem_coe, mem_p1p1FibreFst_support_iff z hz]
  exact ⟨fun h => funext fun i => by fin_cases i; exact h, fun h => congrFun h 0⟩

/-- **`pr₁` pulls the chart coclass of `{∞}` back to the chart coclass of `{∞} × ℙ¹`, sign `+`,
exact.** For `W' ⊆ (ℙ¹ × ℙ¹)(ℂ)` inside the product chart source, mapped by `pr₁` into
`W ⊆ ℙ¹(ℂ)` inside the chart `x₀ ≠ 0`, the pullback along `pr₁` of
`chartNormalProjectionCoclass` of `lineAdaptedChart`, `{∞}`, `W` is
`chartNormalProjectionCoclass` of `p1p1FstChart`, `{∞} × ℙ¹`, `W'`, in
`H²(W', W' ∖ ({∞} × ℙ¹); ℚ)`. -/
theorem p1p1Fst_chartNormalProjectionCoclass_pullback
    (W : Set (ComplexPoint projectiveLine)) (hW : W ⊆ lineAdaptedChart.source)
    (W' : Set (ComplexPoint p1p1)) (hW' : W' ⊆ p1p1FstChart.source)
    (hWW : Set.MapsTo (Point.map prod.fst) W' W) :
    relativeCohomologyMap ℚ (2 * 1)
        (neighborhoodSupportPullbackPairMap (Point.map prod.fst) (Point.continuous_map _) hWW
          (fun z _ h => (map_fst_mem_infty_support_iff z).mp h))
        (chartNormalProjectionCoclass (Fin 0 → ℂ) 1 lineAdaptedChart
          (cycleComponentAnalyticClosedSupport projectiveLine infty) lineAdaptedChart_adapted
          W hW) =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 p1p1FstChart
        (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst) mem_p1p1FibreFst_support_iff'
        W' hW' :=
  chartNormalProjectionCoclass_pullback _ _ _ _ _ _ _ _ _ _ _ _ hWW _
    (fun z _ => (p1p1FstChart_apply_snd z).symm)

/-- `lineAdaptedChart` is holomorphic: followed by `ℂ^0 × ℂ^1 ≃ ℂ^1` it is `lineChart`, in the
maximal analytic atlas (hypothesis `he` of `cycle-class-germ`). -/
theorem lineAdaptedChart_holomorphic :
    lineAdaptedChart.trans (ContinuousLinearEquiv.uniqueProd ℂ (Fin 1 → ℂ)
        (Fin 0 → ℂ)).toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin 1 → ℂ) ω (ComplexPoint projectiveLine) := by
  apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource (e := lineChart)
  · constructor
    · simp [lineAdaptedChart]
    · intro z _
      simp [lineAdaptedChart]
  · exact lineChart_mem_maximalAtlas

/-- `p1p1FstChart` is holomorphic: followed by `fstSplit.symm` it is `p1p1Chart`, in the maximal
analytic atlas (hypothesis `he` of `cycle-class-germ`). -/
theorem p1p1FstChart_holomorphic :
    p1p1FstChart.trans fstSplit.symm.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint p1p1) := by
  apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource (e := p1p1Chart)
  · constructor
    · simp [p1p1FstChart]
    · intro z _
      simp [p1p1FstChart]
  · exact p1p1Chart_mem_maximalAtlas

/-- Non-vacuity: the corner `(∞, ∞)` lies in the source of `p1p1FstChart` and on `{∞} × ℙ¹`,
and `inftyPoint` in the source of `lineAdaptedChart`. -/
theorem p1p1CornerPoint_mem_p1p1FstChart_source :
    p1p1CornerPoint ∈ p1p1FstChart.source ∧
      p1p1CornerPoint ∈ (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst :
        Set (ComplexPoint p1p1)) ∧
      inftyPoint ∈ lineAdaptedChart.source := by
  refine ⟨by rw [p1p1FstChart_source]; exact p1p1CornerPoint_mem_source, ?_, by
    rw [lineAdaptedChart_source]; exact inftyPoint_mem_source⟩
  rw [SetLike.mem_coe, mem_p1p1FibreFst_support_iff_fst, map_fst_p1p1CornerPoint,
    inftyPoint_underlying]

/-- Non-vacuity of the identity: on upstream's flattened neighborhood of the corner `(∞, ∞)` in
`p1p1FstChart`, the chart coclass of `{∞} × ℙ¹` (the right side of
`p1p1Fst_chartNormalProjectionCoclass_pullback`) is nonzero; on the flattened neighborhood of `∞`
in `lineAdaptedChart`, the chart coclass of `{∞}` (the class pulled back) is nonzero. -/
theorem p1p1Fst_chartNormalProjectionCoclass_ne_zero :
    chartNormalProjectionCoclass (Fin 1 → ℂ) 1 p1p1FstChart
        (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst) mem_p1p1FibreFst_support_iff'
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 p1p1FstChart p1p1CornerPoint
          p1p1CornerPoint_mem_p1p1FstChart_source.1)
        (flattenedSupportNeighborhood_subset_source _ _ _ _ _) ≠ 0 ∧
      chartNormalProjectionCoclass (Fin 0 → ℂ) 1 lineAdaptedChart
        (cycleComponentAnalyticClosedSupport projectiveLine infty) lineAdaptedChart_adapted
        (flattenedSupportNeighborhood (Fin 0 → ℂ) 1 lineAdaptedChart inftyPoint
          p1p1CornerPoint_mem_p1p1FstChart_source.2.2)
        (flattenedSupportNeighborhood_subset_source _ _ _ _ _) ≠ 0 := by
  have h := p1p1CornerPoint_mem_p1p1FstChart_source
  refine ⟨chartNormalProjectionCoclass_flattened_ne_zero _ _ _ _ _ ?_,
    chartNormalProjectionCoclass_flattened_ne_zero _ _ _ _ _ ?_⟩
  · exact (mem_p1p1FibreFst_support_iff' _ h.1).mp h.2.1
  · refine (lineAdaptedChart_adapted _ h.2.2).mp ?_
    rw [mem_infty_support_iff, inftyPoint_underlying]

/-- `pr₁` maps the source of `p1p1FstChart` into the source of `lineAdaptedChart`. -/
theorem mapsTo_fst_p1p1FstChart_source :
    Set.MapsTo (Point.map prod.fst) p1p1FstChart.source lineAdaptedChart.source := by
  intro z hz
  rw [p1p1FstChart_source, mem_p1p1Chart_source_iff] at hz
  rw [lineAdaptedChart_source]
  exact hz.1

/-- Non-vacuity of `p1p1Fst_chartNormalProjectionCoclass_pullback` at one admissible pair, the two
chart sources: the pullback along `pr₁` of the chart coclass of `{∞}` is nonzero, so the identity
there is an equality of nonzero classes and separates `+` from `-` over `ℚ`. -/
theorem p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero :
    relativeCohomologyMap ℚ (2 * 1)
        (neighborhoodSupportPullbackPairMap (Point.map prod.fst) (Point.continuous_map _)
          mapsTo_fst_p1p1FstChart_source (fun z _ h => (map_fst_mem_infty_support_iff z).mp h))
        (chartNormalProjectionCoclass (Fin 0 → ℂ) 1 lineAdaptedChart
          (cycleComponentAnalyticClosedSupport projectiveLine infty) lineAdaptedChart_adapted
          lineAdaptedChart.source subset_rfl) ≠ 0 := by
  rw [p1p1Fst_chartNormalProjectionCoclass_pullback (hW' := subset_rfl)]
  intro hz
  apply p1p1Fst_chartNormalProjectionCoclass_ne_zero.1
  rw [← chartNormalProjectionCoclass_restrict (Fin 1 → ℂ) 1 p1p1FstChart _
    mem_p1p1FibreFst_support_iff' (flattenedSupportNeighborhood_subset_source _ _ _ _ _) subset_rfl,
    hz, map_zero]

/-! ### Feeding the charts to `cycle-class-germ` -/

/-- `cycle-class-germ` in its source form
(`transport_supportedClass_eq_chartNormalProjectionCoclass_source`, no smooth-locus hypothesis)
with the holomorphy hypothesis `he` stated over `Fin d → ℂ` for any `d` certifying smoothness of
relative dimension, in place of `Fin (dim X.left) → ℂ`: the restriction to `e.source` of the
transport of `[Z]` is the chart coclass of `e`. Exact, no sign; `d = dim X.left` by upstream's
`SmoothOfRelativeDimension.dim_eq`. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_source_of_dim
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom] (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin d → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    relativeCohomologyMap ℚ (2 * p)
        (neighborhoodSupportInclusionPairMap
          (W := e.source)
          (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
          ⊤ (2 * p)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)
            (cycleComponentSupportedInjectiveClass X x hx))) =
      chartNormalProjectionCoclass E p e
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS e.source
          subset_rfl := by
  obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d
  exact HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass_source
    X x hx e L he hS

/-- On ℙ¹, the restriction to the chart `x₀ ≠ 0` of the transport of the supported class
`[∞]` is the chart coclass of `lineAdaptedChart`. Exact, no sign. -/
theorem infty_transport_eq_lineAdaptedChart_coclass :
    relativeCohomologyMap ℚ (2 * 1)
        (neighborhoodSupportInclusionPairMap
          (W := lineAdaptedChart.source)
          (V := ((⊤ : Opens (ComplexPoint projectiveLine)) : Set (ComplexPoint projectiveLine)))
          (fun _ _ => trivial)
          (cycleComponentAnalyticClosedSupport projectiveLine infty :
            Set (ComplexPoint projectiveLine)))
        (complexSupportInjectiveSectionCohomologyEquiv projectiveLine
          (cycleComponentAnalyticClosedSupport projectiveLine infty) ⊤ (2 * 1)
          (rationalSupportAddEquivSupportedInjectiveHomology projectiveLine
            (cycleComponentAnalyticClosedSupport projectiveLine infty) (2 * 1)
            (cycleComponentSupportedInjectiveClass projectiveLine infty
              (by rw [Nat.cast_one]; exact coheight_infty)))) =
      chartNormalProjectionCoclass (Fin 0 → ℂ) 1 lineAdaptedChart
        (cycleComponentAnalyticClosedSupport projectiveLine infty) lineAdaptedChart_adapted
        lineAdaptedChart.source subset_rfl :=
  transport_supportedClass_eq_chartNormalProjectionCoclass_source_of_dim projectiveLine (d := 1)
    infty _ lineAdaptedChart _ lineAdaptedChart_holomorphic lineAdaptedChart_adapted

/-- On ℙ¹ × ℙ¹, the restriction to the product chart source of the transport of the supported
class `[{∞} × ℙ¹]` is the chart coclass of `p1p1FstChart`. Exact, no sign. With
`p1p1Fst_chartNormalProjectionCoclass_pullback` and
`HodgeLadder.LocalClassPullback.restrict_pullback_eq_chartNormalProjectionCoclass` this is the
local identity `pr₁*[∞] = [{∞} × ℙ¹]` on that chart source, read through the transports. -/
theorem p1p1FibreFst_transport_eq_p1p1FstChart_coclass :
    relativeCohomologyMap ℚ (2 * 1)
        (neighborhoodSupportInclusionPairMap
          (W := p1p1FstChart.source)
          (V := ((⊤ : Opens (ComplexPoint p1p1)) : Set (ComplexPoint p1p1)))
          (fun _ _ => trivial)
          (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst : Set (ComplexPoint p1p1)))
        (complexSupportInjectiveSectionCohomologyEquiv p1p1
          (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst) ⊤ (2 * 1)
          (rationalSupportAddEquivSupportedInjectiveHomology p1p1
            (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst) (2 * 1)
            (cycleComponentSupportedInjectiveClass p1p1 p1p1FibreFst coheight_p1p1FibreFst))) =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 p1p1FstChart
        (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst) mem_p1p1FibreFst_support_iff'
        p1p1FstChart.source subset_rfl :=
  transport_supportedClass_eq_chartNormalProjectionCoclass_source_of_dim p1p1 (d := 2)
    p1p1FibreFst _ p1p1FstChart _ p1p1FstChart_holomorphic mem_p1p1FibreFst_support_iff'

end HodgeLadder.Tests
