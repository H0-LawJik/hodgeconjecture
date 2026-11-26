module

public import HodgeLadder.Normalization.ChartStep
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace

import Mathlib.Analysis.Analytic.Polynomial

/-!
# Algebraic affine charts are holomorphic charts

Rung `affine-chart-analytic` (foundation for `p2-lines-transversal` and
`p1p1-fibres-transversal`, red team finding 12 on `cycle-class-multiplicative`). Let `X` be smooth
of relative dimension `d` over `ℂ`, `U ⊆ X` an open subscheme and `e : U ≅ 𝔸^d` an isomorphism
over `Spec ℂ`. The algebraic coordinates of `𝔸^d` (upstream's `affineSpaceEquiv`, the values of
the coordinate functions `AffineSpace.coord`) transported along `e` give a homeomorphism
`U(ℂ) ≃ₜ ℂ^d`; extended along upstream's open embedding `U(ℂ) → X(ℂ)` it is a chart `affineChart`
of `X(ℂ)`. The rung: this chart lies in Mathlib's maximal analytic atlas of `X(ℂ)` for upstream's
charted space, whose charts `localChart` come from étale coordinates chosen with
`Classical.choice`. Equivalently (`affineChart_compatible_localChart`), its transitions with every
`localChart` are holomorphic in both directions.

Proof. The chart is holomorphic because its coordinates are evaluations of regular functions on
`U` (`affineChart_apply_eq_evaluate`), analytic in every `localChart` by upstream's
`analyticAt_localChart_symm_evaluate`. Its inverse is holomorphic because the coordinates of
`localChart` are evaluations of regular functions on `X`; pulled back to `𝔸^d` they are locally
quotients of polynomials (`analyticAt_evaluate_affineSpaceEquiv_symm`). Mathlib's
`OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn` concludes.

Convention: coordinate `m` of `affineChart` is the value of `AffineSpace.coord m` pulled back
along `e`; no conjugation enters (rows "Holomorphic adapted chart" and "Algebraic affine chart and
the standard chart of ℙⁿ" of `docs/conventions.md`). The standard charts of ℙⁿ are in
`HodgeLadder.Tests.ProjectiveChart`.

## Main definitions

* `HodgeLadder.Normalization.affineCoordinates`, `HodgeLadder.Normalization.affineChart`,
  `HodgeLadder.Normalization.affineCoordinateSection`
* `HodgeLadder.Normalization.openImmersionAffineIso`,
  `HodgeLadder.Normalization.openImmersionChart`

## Main results

* `HodgeLadder.Normalization.affineChart_mem_maximalAtlas`: the rung.
* `HodgeLadder.Normalization.affineChart_compatible_localChart`: compatibility with every
  `localChart`.
* `HodgeLadder.Normalization.analyticAt_evaluate_affineSpaceEquiv_symm`: regular functions on
  opens of `𝔸ⁿ` are analytic in the affine coordinates.
* `HodgeLadder.Normalization.affineChart_apply_map`, `affineChart_apply_eq_evaluate`,
  `affineChart_source`, `affineChart_target`, `openImmersionChart_symm`,
  `openImmersionChart_mem_maximalAtlas`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

/-- Evaluation of a regular function on an open `V` of `𝔸ⁿ`, read in the affine coordinates, is
complex analytic at every point of `V`: near the point it is a quotient of polynomials with
nonvanishing denominator (upstream's `exists_evaluate_basicOpen_eq_div`). Proof from the red team
verdict on this rung. -/
theorem analyticAt_evaluate_affineSpaceEquiv_symm {n : ℕ}
    (V : (complexAffineSpace (Fin n)).Opens) (t : Γ(complexAffineSpace (Fin n), V))
    {v₀ : Fin n → ℂ} (hv₀ : (affineSpaceEquiv (Fin n)).symm v₀ ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate V t ((affineSpaceEquiv (Fin n)).symm v)) v₀ := by
  have hpoly : ∀ p : MvPolynomial (Fin n) ℂ,
      AnalyticAt ℂ (fun v : Fin n → ℂ ↦ MvPolynomial.eval v p) v₀ := fun p =>
    AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (Fin n → ℂ)) p v₀ trivial
  obtain ⟨f, hfV, hvf⟩ := (isAffineOpen_top (complexAffineSpace (Fin n))).exists_basicOpen_le
    ⟨((affineSpaceEquiv (Fin n)).symm v₀).underlying, hv₀⟩ trivial
  let t' := (complexAffineSpace (Fin n)).presheaf.map (homOfLE hfV).op t
  obtain ⟨k, a, h⟩ := Point.exists_evaluate_basicOpen_eq_div
    (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
    (isAffineOpen_top (complexAffineSpace (Fin n))) f t'
  have hN : (affineSpaceEquiv (Fin n)).symm ⁻¹'
      Point.overOpen ((complexAffineSpace (Fin n)).basicOpen f) ∈ 𝓝 v₀ :=
    (isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hvf
  have hf0 : MvPolynomial.eval v₀ (affineGlobalPolynomial f) ≠ 0 := by
    rw [← evaluate_affineSpaceEquiv_symm_top]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) (U := ⊤) f _ trivial).mp hvf
  have hrat : AnalyticAt ℂ (fun v ↦ MvPolynomial.eval v (affineGlobalPolynomial a) /
      MvPolynomial.eval v (affineGlobalPolynomial f) ^ k) v₀ :=
    (hpoly _).div ((hpoly _).pow k) (pow_ne_zero k hf0)
  apply hrat.congr
  filter_upwards [hN] with v hv
  rw [Point.evaluate_res (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) hfV t _ hv]
  erw [h _ hv]
  rw [evaluate_affineSpaceEquiv_symm_top, evaluate_affineSpaceEquiv_symm_top]

section Affine

variable (X : Over (Spec ↧ℂ)) {d : ℕ} (U : X.left.Opens)
  (e : openScheme X U ≅ Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ))

/-- The algebraic coordinates of an open subscheme `U` with an isomorphism `e : U ≅ 𝔸^d` over
`Spec ℂ`: the complex points of `U` go to those of `𝔸^d` along `e`, then to `ℂ^d` by the values of
the coordinate functions (upstream's `affineSpaceHomeomorph`). -/
def affineCoordinates : ComplexPoint (openScheme X U) ≃ₜ (Fin d → ℂ) :=
  (Point.isoMapHomeomorph e).trans (affineSpaceHomeomorph (Fin d))

/-- The algebraic affine chart of `X(ℂ)` given by `U ≅ 𝔸^d`: `affineCoordinates` extended along
upstream's open embedding `U(ℂ) → X(ℂ)`. -/
def affineChart : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  (affineCoordinates X U e).toOpenPartialHomeomorph.lift_openEmbedding
    (isOpenEmbedding_map_open X U)

/-- On the image of `U(ℂ)` the affine chart is the coordinate vector of the point of `𝔸^d`. -/
theorem affineChart_apply_map (q : ComplexPoint (openScheme X U)) :
    affineChart X U e (Point.map (openInclusion X U) q) =
      affineSpaceEquiv (Fin d) (Point.map e.hom q) := by
  rw [affineChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

/-- The source of the affine chart is the image of `U(ℂ)`. -/
theorem affineChart_source :
    (affineChart X U e).source = Set.range (Point.map (openInclusion X U)) := by
  rw [affineChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.image_univ]

/-- The target of the affine chart is all of `ℂ^d`. -/
theorem affineChart_target : (affineChart X U e).target = Set.univ := by
  rw [affineChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    Homeomorph.toOpenPartialHomeomorph_target]

/-- Coordinate `m` of the affine chart as a regular function on the open `U` of `X`: the
coordinate function `AffineSpace.coord m` pulled back along `e`, moved from `U` to `X`. -/
def affineCoordinateSection (m : Fin d) : Γ(X.left, U.ι ''ᵁ (e.hom.left ⁻¹ᵁ ⊤)) :=
  (U.ι.appIso _).inv (e.hom.left.app ⊤ (AffineSpace.coord (Spec ↧ℂ) m))

/-- On its source, coordinate `m` of the affine chart is evaluation of
`affineCoordinateSection m`. -/
theorem affineChart_apply_eq_evaluate (x : ComplexPoint X) (hx : x ∈ (affineChart X U e).source)
    (m : Fin d) :
    affineChart X U e x m =
      Point.evaluate (U.ι ''ᵁ (e.hom.left ⁻¹ᵁ ⊤)) (affineCoordinateSection X U e m) x := by
  rw [affineChart_source] at hx
  obtain ⟨q, rfl⟩ := hx
  rw [affineChart_apply_map, affineSpaceEquiv_apply, affineCoordinateSection,
    evaluate_openEquiv X U]
  rw [← evaluate_top_eq_appTop, Point.evaluate_map]

/-- Rung `affine-chart-analytic`. Let `X` be smooth of relative dimension `d` over `ℂ`, `U` an
open subscheme and `e : U ≅ 𝔸^d` an isomorphism over `Spec ℂ`. The algebraic chart of `X(ℂ)`
given by `e` (coordinate `m` is the value of `AffineSpace.coord m` pulled back along `e`) lies in
the maximal analytic atlas of `X(ℂ)` for upstream's charted space, built from the étale
coordinates `localChart`. -/
theorem affineChart_mem_maximalAtlas [SmoothOfRelativeDimension d X.hom] :
    affineChart X U e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X) := by
  set φ := affineChart X U e
  set ι : ComplexPoint (openScheme X U) → ComplexPoint X := Point.map (openInclusion X U)
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · -- the chart is holomorphic: its coordinates are regular functions on `U`
    intro w hw
    have hwc : ContinuousAt φ w := φ.continuousAt hw
    refine (contMDiffAt_of_analyticAt_chart hwc ?_).contMDiffWithinAt
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
    set c := localChart X d w
    change AnalyticAt ℂ (fun v => φ (c.symm v)) (c w)
    have hw' : w ∈ c.source := mem_localChart_source X d w
    have hcw : c w ∈ c.target := c.map_source hw'
    refine AnalyticAt.pi fun m => ?_
    have hV : c.symm (c w) ∈ Point.overOpen (U.ι ''ᵁ (e.hom.left ⁻¹ᵁ ⊤)) := by
      rw [c.left_inv hw']
      rw [affineChart_source] at hw
      obtain ⟨q, rfl⟩ := hw
      show (Point.map (openInclusion X U) q).underlying ∈ U.ι ''ᵁ (e.hom.left ⁻¹ᵁ ⊤)
      rw [Point.underlying_map]
      exact ⟨q.underlying, trivial, rfl⟩
    have ha := analyticAt_localChart_symm_evaluate X d w hcw _
      (affineCoordinateSection X U e m) hV
    apply ha.congr
    have hsrc : c.symm ⁻¹' φ.source ∈ 𝓝 (c w) := by
      apply c.continuousAt_symm hcw
      rw [c.left_inv hw']
      exact φ.open_source.mem_nhds hw
    filter_upwards [hsrc] with v hv
    exact (affineChart_apply_eq_evaluate X U e _ hv m).symm
  · -- the inverse is holomorphic: upstream's coordinates are regular functions on `𝔸^d`
    intro v hv
    have hvc : ContinuousAt φ.symm v := φ.continuousAt_symm hv
    refine (contMDiffAt_of_analyticAt_chart hvc ?_).contMDiffWithinAt
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      id]
    set c := localChart X d (φ.symm v)
    change AnalyticAt ℂ (fun u => c (φ.symm u)) v
    have hs : φ.symm v ∈ c.source := mem_localChart_source X d _
    refine AnalyticAt.pi fun k => ?_
    let D := localEtaleCoordinates X d (φ.symm v)
    have hsymm : ∀ u, φ.symm u = ι (Point.map e.inv ((affineSpaceEquiv (Fin d)).symm u)) :=
      fun u => rfl
    have hV : φ.symm v ∈ Point.overOpen D.ambientCoordinateOpen := by
      have hmem := mem_coordinateNeighborhood_of_mem_localChart_source X d (φ.symm v) _ hs
      simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
        using hmem
    have hV1 : Point.map e.inv ((affineSpaceEquiv (Fin d)).symm v) ∈
        Point.overOpen ((openInclusion X U).left ⁻¹ᵁ D.ambientCoordinateOpen) :=
      (Point.mem_overOpen_map_iff (openInclusion X U) _ _).mp hV
    have hV2 := (Point.mem_overOpen_map_iff e.inv _ _).mp hV1
    have ha := analyticAt_evaluate_affineSpaceEquiv_symm _
      (e.inv.left.app _ ((openInclusion X U).left.app _ (D.ambientCoordinateSection k))) hV2
    apply ha.congr
    have hsrc : φ.symm ⁻¹' c.source ∈ 𝓝 v := hvc (c.open_source.mem_nhds hs)
    filter_upwards [hsrc] with u hu
    rw [localChart_apply_component_eq_evaluate X d (φ.symm v) _ hu k, hsymm u,
      Point.evaluate_map, Point.evaluate_map]

/-- Compatibility with upstream's charts: the transitions between the affine chart and every
`localChart` are in the analytic groupoid, in both directions. -/
theorem affineChart_compatible_localChart [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    (affineChart X U e).symm.trans (localChart X d z) ∈ contDiffGroupoid ω 𝓘(ℂ, Fin d → ℂ) ∧
      (localChart X d z).symm.trans (affineChart X U e) ∈
        contDiffGroupoid ω 𝓘(ℂ, Fin d → ℂ) :=
  ⟨IsManifold.compatible_of_mem_maximalAtlas (affineChart_mem_maximalAtlas X U e)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) z),
    IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) z)
      (affineChart_mem_maximalAtlas X U e)⟩

end Affine

section OpenImmersion

/-- An open immersion `j : 𝔸^d ⟶ X` over `Spec ℂ` identifies its range with `𝔸^d`. -/
def openImmersionAffineIso (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left] :
    openScheme X j.left.opensRange ≅ Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) :=
  Over.isoMk j.left.isoOpensRange.symm (by
    change j.left.isoOpensRange.inv ≫ (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) =
      j.left.opensRange.ι ≫ X.hom
    have hw : j.left ≫ X.hom = complexAffineSpace (Fin d) ↘ Spec ↧ℂ := Over.w j
    calc _ = j.left.isoOpensRange.inv ≫ j.left ≫ X.hom := by rw [hw]
      _ = _ := by rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])

/-- The affine chart of an open immersion `j : 𝔸^d ⟶ X` over `Spec ℂ`. -/
def openImmersionChart (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left] :
    OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  affineChart X j.left.opensRange (openImmersionAffineIso X j)

/-- The inverse of the chart of `j` is `j` on complex points, after the affine coordinates. -/
theorem openImmersionChart_symm (X : Over (Spec ↧ℂ)) {d : ℕ}
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left]
    (v : Fin d → ℂ) :
    (openImmersionChart X j).symm v = Point.map j ((affineSpaceEquiv (Fin d)).symm v) := by
  apply Over.OverMorphism.ext
  change ((affineSpaceEquiv (Fin d)).symm v).left ≫ j.left.isoOpensRange.hom ≫
    j.left.opensRange.ι = ((affineSpaceEquiv (Fin d)).symm v).left ≫ j.left
  rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- The affine chart of an open immersion `j : 𝔸^d ⟶ X` over `Spec ℂ` lies in the maximal
analytic atlas of `X(ℂ)` (the rung, at `U = range j`). -/
theorem openImmersionChart_mem_maximalAtlas (X : Over (Spec ↧ℂ)) {d : ℕ}
    [SmoothOfRelativeDimension d X.hom]
    (j : Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ) ⟶ X) [IsOpenImmersion j.left] :
    openImmersionChart X j ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X) :=
  affineChart_mem_maximalAtlas X _ _

end OpenImmersion

end HodgeLadder.Normalization
