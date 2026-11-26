module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Chart step: the inclusion of an open subscheme is a biholomorphism onto its image

Rung `open-subscheme-chart-analytic` (foundation for `cycle-class-germ`, red team finding 15).
Upstream gives the complex points of every smooth complex scheme a charted space from its own
étale coordinates (`localChart`), chosen with `Classical.choice`; for an open subscheme `U ⊆ X` the
charts of `U(ℂ)` and of `X(ℂ)` are chosen independently. This file shows that the two analytic
structures agree: a chart of the maximal analytic atlas of `U(ℂ)`, extended along the open
embedding `U(ℂ) → X(ℂ)`, lies in the maximal analytic atlas of `X(ℂ)`.

The coordinates of `localChart` are evaluations (`Point.evaluate`) of regular sections. The
inclusion `ι` is holomorphic because a section of `X` evaluated at `ι q` is its pullback evaluated
at `q` (upstream's `Point.evaluate_map`); its local inverse is holomorphic because a section of `U`
is a section of `X` over the image open (upstream's `evaluate_openEquiv`). Upstream's
`analyticAt_localChart_symm_evaluate` makes both evaluations analytic.

The file also holds general facts about analytic charts used by `cycle-class-germ` and its
non-vacuity witnesses: translations are in the analytic groupoid, the maximal atlas is stable
under composition with the groupoid, and transitions between holomorphic charts in product form
are analytic.

## Main results

* `HodgeLadder.Normalization.contMDiff_map_openInclusion`,
  `HodgeLadder.Normalization.contMDiffAt_map_openInclusion_symm`: `ι` and its local inverse are
  holomorphic.
* `HodgeLadder.Normalization.lift_mem_maximalAtlas_openScheme`: the chart step.
* `HodgeLadder.Normalization.lift_mem_maximalAtlas_smoothSupportAmbient`: its instance at
  `X ∖ Z_sing`, along the map upstream uses to transport the cycle class.
* `HodgeLadder.Normalization.translate_mem`, `HodgeLadder.Normalization.trans_mem_maximalAtlas`,
  `HodgeLadder.Normalization.analyticAt_transition_of_mem_maximalAtlas`,
  `HodgeLadder.Normalization.analyticAt_transition_of_factor`: analytic charts.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- A map between manifolds modelled on `ℂ`-vector spaces with their identity models is analytic
at a point when it is continuous there and analytic in the charts at the point. -/
theorem contMDiffAt_of_analyticAt_chart {F F' M M' : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace M]
    [ChartedSpace F M] [TopologicalSpace M'] [ChartedSpace F' M'] {f : M → M'} {x : M}
    (hc : ContinuousAt f x)
    (ha : AnalyticAt ℂ (fun v => chartAt F' (f x) (f ((chartAt F x).symm v))) (chartAt F x x)) :
    ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F') ω f x := by
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Set.range_id, Function.comp_def, id]
  exact ha.contDiffAt.contDiffWithinAt

/-- A translation of a complex normed space is in the analytic groupoid. -/
theorem translate_mem {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (v : F) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(ℂ, F) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa using ((contDiff_id.add contDiff_const : ContDiff ℂ ω fun x : F => x + v)).contDiffOn
  · simpa [Homeomorph.addRight_symm] using
      ((contDiff_id.add contDiff_const : ContDiff ℂ ω fun x : F => x + -v)).contDiffOn

/-- A chart of the maximal analytic atlas followed by an element of the analytic groupoid of the
model space is again in the maximal analytic atlas. -/
theorem trans_mem_maximalAtlas {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℂ, F) ω M]
    {c : OpenPartialHomeomorph M F} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, F) ω M)
    {T : OpenPartialHomeomorph F F} (hT : T ∈ contDiffGroupoid ω 𝓘(ℂ, F)) :
    c.trans T ∈ IsManifold.maximalAtlas 𝓘(ℂ, F) ω M := by
  intro e' he'
  have he'' := (contDiffGroupoid ω 𝓘(ℂ, F)).subset_maximalAtlas he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ, F)).trans ((contDiffGroupoid ω 𝓘(ℂ, F)).symm hT)
      (StructureGroupoid.compatible_of_mem_maximalAtlas hc he'')
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℂ, F)).trans
      (StructureGroupoid.compatible_of_mem_maximalAtlas he'' hc) hT

/-- An element of the analytic groupoid of a complex normed space is analytic at every point of
its source. -/
theorem analyticAt_of_mem_contDiffGroupoid {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {T : OpenPartialHomeomorph F F} (hT : T ∈ contDiffGroupoid ω 𝓘(ℂ, F))
    {v : F} (hv : v ∈ T.source) : AnalyticAt ℂ T v := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hT
  have h : ContDiffOn ℂ ω T T.source := by simpa using hT.1
  exact (h.contDiffAt (T.open_source.mem_nhds hv)).analyticAt

/-- Two charts of a complex manifold that become charts of the maximal analytic atlas after
`ℂ`-linear identifications of their model spaces have analytic transitions. -/
theorem analyticAt_transition_of_mem_maximalAtlas {F G H M : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold 𝓘(ℂ, H) ω M]
    {e : OpenPartialHomeomorph M F} {f : OpenPartialHomeomorph M G} (Le : F ≃L[ℂ] H)
    (Lf : G ≃L[ℂ] H)
    (he : e.trans Le.toHomeomorph.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, H) ω M)
    (hf : f.trans Lf.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, H) ω M)
    {y : M} (hye : y ∈ e.source) (hyf : y ∈ f.source) :
    AnalyticAt ℂ (e.symm.trans f) (e y) := by
  set T := (e.trans Le.toHomeomorph.toOpenPartialHomeomorph).symm.trans
    (f.trans Lf.toHomeomorph.toOpenPartialHomeomorph)
  have hT : T ∈ contDiffGroupoid ω 𝓘(ℂ, H) := IsManifold.compatible_of_mem_maximalAtlas he hf
  have hmem : Le (e y) ∈ T.source := by
    simp [T, e.map_source hye, e.left_inv hye, hyf]
  have hTa := analyticAt_of_mem_contDiffGroupoid hT hmem
  have hcomp : AnalyticAt ℂ (fun v => Lf.symm (T (Le v))) (e y) :=
    Lf.symm.toContinuousLinearMap.analyticAt _ |>.comp
      (hTa.comp (Le.toContinuousLinearMap.analyticAt _))
  apply hcomp.congr
  have hnhds : e.target ∩ e.symm ⁻¹' f.source ∈ 𝓝 (e y) :=
    (e.isOpen_inter_preimage_symm f.open_source).mem_nhds
      ⟨e.map_source hye, by simpa [e.left_inv hye] using hyf⟩
  filter_upwards [hnhds] with v hv
  simp [T]

/-- Transitions from a holomorphic chart `e` to a chart `f = A ∘ λ`, where `λ` is in the maximal
analytic atlas and `A` is analytic in both directions at the relevant points, are analytic in both
directions. -/
theorem analyticAt_transition_of_factor {F G H M : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold 𝓘(ℂ, H) ω M]
    {e : OpenPartialHomeomorph M F} (Le : F ≃L[ℂ] H)
    (he : e.trans Le.toHomeomorph.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, H) ω M)
    {l : OpenPartialHomeomorph M H} (hl : l ∈ IsManifold.maximalAtlas 𝓘(ℂ, H) ω M)
    (A : OpenPartialHomeomorph H G) (f : OpenPartialHomeomorph M G)
    (hf : ∀ w ∈ f.source, w ∈ l.source ∧ l w ∈ A.source ∧ f w = A (l w))
    (hfs : ∀ v, f.symm v = l.symm (A.symm v))
    {y : M} (hye : y ∈ e.source) (hyf : y ∈ f.source)
    (hA : AnalyticAt ℂ A (l y)) (hA' : AnalyticAt ℂ A.symm (f y)) :
    AnalyticAt ℂ (e.symm.trans f) (e y) ∧
      AnalyticAt ℂ (e.symm.trans f).symm ((e.symm.trans f) (e y)) := by
  set τ := (e.trans Le.toHomeomorph.toOpenPartialHomeomorph).symm.trans l
  have hτ : τ ∈ contDiffGroupoid ω 𝓘(ℂ, H) := IsManifold.compatible_of_mem_maximalAtlas he hl
  obtain ⟨hyl, hlyA, hfy⟩ := hf y hyf
  constructor
  · have hmem : Le (e y) ∈ τ.source := by
      simp [τ, e.map_source hye, e.left_inv hye, hyl]
    have hτy : τ (Le (e y)) = l y := by simp [τ, e.left_inv hye]
    have hτa := analyticAt_of_mem_contDiffGroupoid hτ hmem
    have hcomp : AnalyticAt ℂ (fun v => A (τ (Le v))) (e y) := by
      refine AnalyticAt.comp (g := A) ?_ (hτa.comp (Le.toContinuousLinearMap.analyticAt _))
      simpa [hτy] using hA
    apply hcomp.congr
    have hnhds : e.target ∩ e.symm ⁻¹' f.source ∈ 𝓝 (e y) :=
      (e.isOpen_inter_preimage_symm f.open_source).mem_nhds
        ⟨e.map_source hye, by simpa [e.left_inv hye] using hyf⟩
    filter_upwards [hnhds] with v hv
    obtain ⟨_, _, hfv⟩ := hf _ hv.2
    simp [τ, hfv]
  · have hpt : (e.symm.trans f) (e y) = f y := by simp [e.left_inv hye]
    rw [hpt]
    have hAy : A.symm (f y) = l y := by rw [hfy, A.left_inv hlyA]
    have hmem : l y ∈ τ.symm.source := by
      simp [τ, l.map_source hyl, l.left_inv hyl, hye]
    have hτa := analyticAt_of_mem_contDiffGroupoid ((contDiffGroupoid ω 𝓘(ℂ, H)).symm hτ) hmem
    have hcomp : AnalyticAt ℂ (fun v => Le.symm (τ.symm (A.symm v))) (f y) := by
      refine Le.symm.toContinuousLinearMap.analyticAt _ |>.comp ?_
      refine AnalyticAt.comp (g := τ.symm) ?_ hA'
      simpa [hAy] using hτa
    apply hcomp.congr
    filter_upwards with v
    simp [τ, hfs]

section OpenScheme

variable (X : Over (Spec ↧ℂ)) {d : ℕ} [SmoothOfRelativeDimension d X.hom] (U : X.left.Opens)
  [SmoothOfRelativeDimension d (openScheme X U).hom]

/-- The inclusion of an open subscheme is holomorphic on complex points. -/
theorem contMDiff_map_openInclusion :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (Point.map (openInclusion X U) : ComplexPoint (openScheme X U) → ComplexPoint X) := by
  intro z
  set ι : ComplexPoint (openScheme X U) → ComplexPoint X := Point.map (openInclusion X U)
  have hιc : Continuous ι := (isOpenEmbedding_map_open X U).continuous
  set c := localChart X d (ι z)
  set c' := localChart (openScheme X U) d z
  apply contMDiffAt_of_analyticAt_chart hιc.continuousAt
  change AnalyticAt ℂ (fun v => c (ι (c'.symm v))) (c' z)
  have hz : z ∈ c'.source := mem_localChart_source _ d z
  have hw : c' z ∈ c'.target := c'.map_source hz
  refine AnalyticAt.pi fun i => ?_
  let D := ComplexPoint.localEtaleCoordinates X d (ι z)
  let V := D.ambientCoordinateOpen
  let s := D.ambientCoordinateSection i
  have hV : c'.symm (c' z) ∈ Point.overOpen ((openInclusion X U).left ⁻¹ᵁ V) := by
    rw [c'.left_inv hz, ← Point.mem_overOpen_map_iff]
    have hmem := ComplexPoint.mem_localEtaleCoordinates X d (ι z)
    simp only [V, D, Scheme.Opens.ι_image_top]
    exact hmem
  have ha := analyticAt_localChart_symm_evaluate (openScheme X U) d z hw _
    ((openInclusion X U).left.app V s) hV
  apply ha.congr
  have hcont : ContinuousAt (fun v => ι (c'.symm v)) (c' z) :=
    hιc.continuousAt.comp (c'.continuousAt_symm hw)
  have hsrc : (fun v => ι (c'.symm v)) ⁻¹' c.source ∈ 𝓝 (c' z) := by
    apply hcont
    show c.source ∈ 𝓝 (ι (c'.symm (c' z)))
    rw [c'.left_inv hz]
    exact c.open_source.mem_nhds (mem_localChart_source X d (ι z))
  filter_upwards [hsrc] with v hv
  rw [localChart_apply_component_eq_evaluate X d (ι z) _ hv i]
  exact (Point.evaluate_map (openInclusion X U) V s (c'.symm v)).symm

/-- The local inverse of the inclusion of an open subscheme is holomorphic at every point of the
image. -/
theorem contMDiffAt_map_openInclusion_symm [Nonempty (ComplexPoint (openScheme X U))]
    (z : ComplexPoint (openScheme X U)) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      ((isOpenEmbedding_map_open X U).toOpenPartialHomeomorph
        (Point.map (openInclusion X U))).symm
      (Point.map (openInclusion X U) z) := by
  set ι : ComplexPoint (openScheme X U) → ComplexPoint X := Point.map (openInclusion X U)
  have hι : IsOpenEmbedding ι := isOpenEmbedding_map_open X U
  set g := (hι.toOpenPartialHomeomorph ι).symm
  set w := ι z
  have hgw : g w = z := hι.toOpenPartialHomeomorph_left_inv
  have hwt : w ∈ (hι.toOpenPartialHomeomorph ι).target := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]; exact ⟨z, rfl⟩
  have hgc : ContinuousAt g w := (hι.toOpenPartialHomeomorph ι).continuousAt_symm hwt
  have hιgw : ι (g w) = w := by rw [hgw]
  apply contMDiffAt_of_analyticAt_chart hgc
  set c := localChart X d w
  set c' := localChart (openScheme X U) d (g w)
  change AnalyticAt ℂ (fun v => c' (g (c.symm v))) (c w)
  have hw : w ∈ c.source := mem_localChart_source X d w
  have hcw : c w ∈ c.target := c.map_source hw
  refine AnalyticAt.pi fun i => ?_
  let D := ComplexPoint.localEtaleCoordinates (openScheme X U) d (g w)
  let V' := D.ambientCoordinateOpen
  let t := D.ambientCoordinateSection i
  have hV : c.symm (c w) ∈ Point.overOpen (U.ι ''ᵁ V') := by
    rw [c.left_inv hw, ← hιgw]
    have hmem := ComplexPoint.mem_localEtaleCoordinates (openScheme X U) d (g w)
    have hq : g w ∈ Point.overOpen V' := by
      simp only [V', D, Scheme.Opens.ι_image_top]
      exact hmem
    show (Point.map (openInclusion X U) (g w)).underlying ∈ U.ι ''ᵁ V'
    rw [Point.underlying_map]
    exact ⟨(g w).underlying, hq, rfl⟩
  have ha := analyticAt_localChart_symm_evaluate X d w hcw _ ((U.ι.appIso V').inv t) hV
  apply ha.congr
  have hcs : ContinuousAt c.symm (c w) := c.continuousAt_symm hcw
  have h1 : c.symm ⁻¹' (hι.toOpenPartialHomeomorph ι).target ∈ 𝓝 (c w) := by
    apply hcs
    rw [c.left_inv hw]
    exact (hι.toOpenPartialHomeomorph ι).open_target.mem_nhds hwt
  have h2 : (fun v => g (c.symm v)) ⁻¹' c'.source ∈ 𝓝 (c w) := by
    have hcont : ContinuousAt (fun v => g (c.symm v)) (c w) := by
      apply ContinuousAt.comp _ hcs
      rw [c.left_inv hw]; exact hgc
    apply hcont
    show c'.source ∈ 𝓝 (g (c.symm (c w)))
    rw [c.left_inv hw]
    exact c'.open_source.mem_nhds (mem_localChart_source _ d (g w))
  filter_upwards [h1, h2] with v hv1 hv2
  rw [localChart_apply_component_eq_evaluate (openScheme X U) d (g w) _ hv2 i]
  have hr : ι (g (c.symm v)) = c.symm v :=
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv ι hι (by
      rw [IsOpenEmbedding.toOpenPartialHomeomorph_target] at hv1; exact hv1)
  rw [← evaluate_openEquiv X U t (g (c.symm v))]
  change _ = Point.evaluate _ _ (ι (g (c.symm v)))
  rw [hr]

/-- Chart step of `cycle-class-germ`. Let `X` be smooth of relative dimension `d` over `ℂ` and
`U` an open subscheme. A chart in the maximal analytic atlas of `U(ℂ)` (upstream's charted space
on the open subscheme, built from its own étale coordinates), extended along upstream's open
embedding `U(ℂ) → X(ℂ)`, lies in the maximal analytic atlas of `X(ℂ)`. In words: the inclusion of
an open subscheme is a biholomorphism onto its image for upstream's complex structures. The
instance hypothesis on `openScheme X U` holds for every `X` and `U` (`smoothOfRelativeDimension_comp
0 d U.ι X.hom`); it is an argument so that this file adds no instance. -/
theorem lift_mem_maximalAtlas_openScheme
    {ψ : OpenPartialHomeomorph (ComplexPoint (openScheme X U)) (Fin d → ℂ)}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint (openScheme X U))) :
    ψ.lift_openEmbedding (isOpenEmbedding_map_open X U) ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X) := by
  set ι : ComplexPoint (openScheme X U) → ComplexPoint X := Point.map (openInclusion X U)
  have hι : IsOpenEmbedding ι := isOpenEmbedding_map_open X U
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · rcases isEmpty_or_nonempty (ComplexPoint (openScheme X U)) with hE | hne
    · rintro w ⟨q, _, _⟩
      exact (IsEmpty.false q).elim
    · rintro w ⟨z, hz, rfl⟩
      set g := (hι.toOpenPartialHomeomorph ι).symm
      have hgz : g (ι z) = z := hι.toOpenPartialHomeomorph_left_inv
      have h1 : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω ψ (g (ι z)) := by
        rw [hgz]
        exact (contMDiffOn_of_mem_maximalAtlas hψ).contMDiffAt (ψ.open_source.mem_nhds hz)
      have h3 : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (ψ ∘ g) (ι z) :=
        h1.comp _ (contMDiffAt_map_openInclusion_symm X U z)
      refine (h3.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [hι.isOpen_range.mem_nhds ⟨z, rfl⟩] with w' hw'
      obtain ⟨q, rfl⟩ := hw'
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply, Function.comp_apply,
        hι.toOpenPartialHomeomorph_left_inv]
  · rw [OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target]
    exact (contMDiff_map_openInclusion X U).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas hψ)

end OpenScheme

/-- The chart step at the open subscheme `X ∖ Z_sing` that carries upstream's flattening charts,
along the map `cycleComponentSmoothClosedLiftAmbientMap` that upstream uses to transport the
coclass section to `X(ℂ)`. -/
theorem lift_mem_maximalAtlas_smoothSupportAmbient (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    {ψ : OpenPartialHomeomorph (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))
      (Fin (dim X.left) → ℂ)}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
      (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))) :
    ψ.lift_openEmbedding (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x) ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) :=
  lift_mem_maximalAtlas_openScheme X (cycleComponentSmoothLocusAmbientOpen X x) hψ

end HodgeLadder.Normalization
