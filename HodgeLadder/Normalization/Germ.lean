module

public import HodgeLadder.Normalization.Singular
public import HodgeLadder.Normalization.ChartStep
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing
public import Other.AlgebraicGeometry.Cycle.Component.PointBoundary
public import Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Germs of the supported cycle class in adapted holomorphic charts

Rung `cycle-class-germ` (front `cycle-class-multiplicative`, step 5 of the sketch).

Let `x` be a point of coheight `p` of a smooth integral projective `X` over `ℂ`, with
`Z = cycleComponentAnalyticClosedSupport X x` and `U = cycleComponentSmoothSupportAmbientOpen X x`
(the complement of `Z_sing(ℂ)`). Write `T α` for upstream's singular transport of a supported
class at `⊤`, `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2p)` after
`rationalSupportAddEquivSupportedInjectiveHomology`, an element of `H^{2p}(X, X ∖ Z; ℚ)` on
`neighborhoodSupportComplementPair`.

The main theorem: for every holomorphic chart `e` of `X(ℂ)` with values in `E × ℂ^p` in which
`Z` is the zero set of the normal coordinate, and every `y ∈ e.source ∩ U`, there is an open
`W ∋ y` inside `e.source` on which the restriction of `T [Z]` equals upstream's
`chartNormalProjectionCoclass` of `e`. The identity is exact: no sign, no scalar. "Holomorphic"
means that `e` followed by some continuous `ℂ`-linear equivalence `E × ℂ^p ≃ ℂ^d` lies in
Mathlib's maximal analytic atlas of `X(ℂ)` (upstream's charted space from `localChart`).

Route. Equal germs give equal restrictions on a small open (`exists_restrict_eq_of_germ_eq`). The
germ of `T [Z]` at `y ∈ Z ∩ U` is the germ of upstream's normalized coclass section
(`coclassSection_eq_singular`), which upstream glues on `(X ∖ Z_sing)(ℂ)` from flattening-chart
coclasses and moves to `X(ℂ)` along an open embedding. The moved coclass is the coclass of the
lifted flattening chart (`chartNormalProjectionCoclass_pairImage`); the lifted chart and `e` have
analytic transitions by the chart step (`HodgeLadder/Normalization/ChartStep.lean`), so
upstream's `exists_open_chartNormalProjectionCoclass_eq` makes their coclasses agree near `y`.
Off `Z` both germs vanish.

## Main results

* `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass`: the rung.
* `HodgeLadder.Normalization.germ_coclassSection_eq`: the same identity at the level of germs of
  upstream's normalized coclass section.
* `HodgeLadder.Normalization.normalization_supportedInjectiveClass_ne_zero`,
  `HodgeLadder.Normalization.normalization_genericPoint_ne_zero`,
  `HodgeLadder.Normalization.toSheaf_transport_supportedClass_ne_zero`,
  `HodgeLadder.Normalization.chartNormalProjectionCoclass_germ_ne_zero`: non-vacuity of both sides.
* `HodgeLadder.Normalization.coclassSection_eq_singular`: upstream's normalized coclass section
  is the sheafified restriction to `U` of `T [Z]`.
* `HodgeLadder.Normalization.adaptedChart_closedPoint`, `adaptedChart_genericPoint`: the
  hypotheses of the rung can be met, all four in positive codimension on every `X`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology.Singular Topology Filter
open scoped Manifold ContDiff

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint


variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Non-vacuity (red team on `normalization-singular`, change E). Upstream's normalization
isomorphism `N` sends the supported cycle class of every component to a nonzero section: `N [Z]`
is upstream's coclass section (`cycleComponentSupportedInjectiveClass_normalization`), which is
nonzero (`cycleComponentSmoothSupportCoclassSection_ne_zero`, upstream `Other`). -/
theorem normalization_supportedInjectiveClass_ne_zero (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom
      (cycleComponentSupportedInjectiveClass X x hx) ≠ 0 := fun h =>
  cycleComponentSmoothSupportCoclassSection_ne_zero X x hx
    ((cycleComponentSupportedInjectiveClass_normalization X x hx).symm.trans h)

/-- Non-vacuity at the generic point, the case change E names: `N [X] ≠ 0`. -/
theorem normalization_genericPoint_ne_zero :
    (cycleComponentSupportedClassNormalizationIso X (genericPoint X.left)
        (coheight_genericPoint_eq_zero X)).toAddMonoidHom
      (cycleComponentSupportedInjectiveClass X (genericPoint X.left)
        (coheight_genericPoint_eq_zero X)) ≠ 0 :=
  normalization_supportedInjectiveClass_ne_zero X _ _

/-- Upstream's normalized coclass section of `Z` in singular form (RT7 of the red team on
`normalization-singular`): it is the sheafification unit at `U = X ∖ Z_sing` applied to the
restriction, from `(X, X ∖ Z)` to `(U, U ∖ Z)`, of upstream's singular transport at `⊤` of the
supported cycle class. Exact, no sign. -/
theorem coclassSection_eq_singular (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    cycleComponentSmoothSupportCoclassSection X x hx =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
        (relativeCohomologyMap ℚ (2 * p)
          (neighborhoodSupportInclusionPairMap
            (W := (cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
            ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p)
              (cycleComponentSupportedInjectiveClass X x hx)))) :=
  (cycleComponentSupportedInjectiveClass_normalization X x hx).symm.trans
    (normalization_singular X x hx _)

/-- Non-vacuity in singular form: the sheafified restriction to `U` of the transported supported
cycle class is nonzero, for every component. So the left side of the main statement is not zero
on all small opens. -/
theorem toSheaf_transport_supportedClass_ne_zero (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) :
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
        (relativeCohomologyMap ℚ (2 * p)
          (neighborhoodSupportInclusionPairMap
            (W := (cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
            ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p)
              (cycleComponentSupportedInjectiveClass X x hx)))) ≠ 0 := fun h =>
  cycleComponentSmoothSupportCoclassSection_ne_zero X x hx
    ((coclassSection_eq_singular X x hx).trans h)

/-- The chart hypotheses `he`, `hS`, `hy` of
`transport_supportedClass_eq_chartNormalProjectionCoclass` at the generic point (`p = 0`,
`Z = X(ℂ)`), at every `y`: the chart `chartAt y` followed by the inverse of `(ℂ^d) × ℂ^0 ≃ ℂ^d`.
Here `hyU` needs `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`, which is
not at the pin (rung `cycle-class-multiplicative-codim-zero`); `adaptedChart_closedPoint` meets
all four hypotheses in positive codimension. -/
theorem adaptedChart_genericPoint (y : ComplexPoint X) :
    let L := ContinuousLinearEquiv.prodUnique ℂ (Fin (dim X.left) → ℂ) (Fin 0 → ℂ)
    let e := (chartAt (Fin (dim X.left) → ℂ) y).trans
      L.symm.toHomeomorph.toOpenPartialHomeomorph
    (e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X)) ∧
    (∀ z ∈ e.source, z ∈ (cycleComponentAnalyticClosedSupport X (genericPoint X.left) :
        Set (ComplexPoint X)) ↔ (e z).2 = 0) ∧ y ∈ e.source := by
  intro L e
  refine ⟨?_, ?_, ?_⟩
  · apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource
      (e := chartAt (Fin (dim X.left) → ℂ) y)
    · constructor
      · simp [e]
      · intro z _
        simp [e, L]
    · exact IsManifold.chart_mem_maximalAtlas y
  · intro z _
    rw [cycleComponentAnalyticClosedSupport_genericPoint_eq_top]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩
  · simp [e]

/-- Non-vacuity in positive codimension (red team on `cycle-class-germ`, change B): on every `X`
and at every complex point `y₀`, with `x` the closed point under `y₀` (coheight `dim X`) and `e`
the chart `chartAt y₀` translated so that `y₀` goes to `0`, all four hypotheses `he`, `hS`, `hy`,
`hyU` of `transport_supportedClass_eq_chartNormalProjectionCoclass` hold. -/
theorem adaptedChart_closedPoint (y₀ : ComplexPoint X) :
    ∃ (x : X.left) (_ : Order.coheight x = dim X.left)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)))
      (L : ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ)),
      e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
        IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) ∧
      (∀ z ∈ e.source,
        z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) ∧
      y₀ ∈ e.source ∧ y₀ ∈ cycleComponentSmoothSupportAmbientOpen X x := by
  have hclosed : IsClosed {y₀.underlying} :=
    (pointEquivClosedPoint X.hom ⟨y₀.left, Over.w y₀⟩).2
  have hx : Order.coheight y₀.underlying = dim X.left :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := X.hom) _ hclosed
  let c := chartAt (Fin (dim X.left) → ℂ) y₀
  let T := (Homeomorph.addRight (-(c y₀))).toOpenPartialHomeomorph
  let L := ContinuousLinearEquiv.uniqueProd ℂ (Fin (dim X.left) → ℂ) (Fin 0 → ℂ)
  let e := (c.trans T).trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsrc : e.source = c.source := by simp [e, T]
  refine ⟨y₀.underlying, hx, e, L, ?_, ?_, ?_, ?_⟩
  · apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource (e := c.trans T)
    · constructor
      · simp [e, T]
      · intro z _
        simp [e, L, T]
    · exact trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y₀) (translate_mem _)
  · intro z hz
    rw [hsrc] at hz
    have hy₀ : y₀ ∈ c.source := mem_chart_source _ y₀
    change z.underlying ∈ closure {y₀.underlying} ↔ _
    rw [hclosed.closure_eq, Set.mem_singleton_iff]
    have : (e z).2 = c z + -(c y₀) := by simp [e, L, T]
    rw [this, add_neg_eq_zero]
    constructor
    · intro h
      rw [underlying_injective_of_locallyOfFiniteType h]
    · intro h
      rw [c.injOn hz hy₀ h]
  · rw [hsrc]; exact mem_chart_source _ y₀
  · rw [cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension X _ hx]
    trivial

set_option backward.isDefEq.respectTransparency false in
/-- Non-vacuity of the right side (red team on `cycle-class-germ`, change F): at a point `y` of the
chart source on the support, the germ of `chartNormalProjectionCoclass` is nonzero. -/
theorem chartNormalProjectionCoclass_germ_ne_zero {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (y : M) (hy : y ∈ e.source) (h0 : (e y).2 = 0) :
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * c) ⟨e.source, e.open_source⟩ y hy
      (chartNormalProjectionCoclass E c e S hS e.source subset_rfl) ≠ 0 := by
  intro h
  obtain ⟨W, hWU, hyW, hz⟩ :=
    (supportRelativeCohomologyGerm_eq_zero_iff (TopCat.of M) S (2 * c) _ y hy _).mp h
  have hWs : (W : Set M) ⊆ e.source := hWU
  have hz' : chartNormalProjectionCoclass E c e S hS W hWs = 0 := by
    rw [← chartNormalProjectionCoclass_restrict E c e S hS hWs subset_rfl]
    exact hz
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
        (chartNormalProjectionCoclass E c e S hS W hWs) := by
    rw [chartNormalProjectionCoclass_restrict]
    rfl
  rw [h2, hz', map_zero, map_zero] at h1
  exact zero_ne_one ((LinearMap.zero_apply _).symm.trans h1)

/-- The germ map of a support relative cohomology presheaf is additive. -/
theorem supportRelativeCohomologyGerm_sub {Y : TopCat.{0}} (S : Set Y) (n : ℕ) (V : Opens Y)
    (y : Y) (hy : y ∈ V)
    (a b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) S) n) :
    supportRelativeCohomologyGerm Y S n V y hy (a - b) =
      supportRelativeCohomologyGerm Y S n V y hy a -
        supportRelativeCohomologyGerm Y S n V y hy b := by
  simp only [supportRelativeCohomologyGerm]
  erw [map_sub, map_sub]

/-- Equal germs at `y` of two relative classes on opens `V`, `W₀` around `y` (red team RT3): the
restrictions agree on some open `W ∋ y` inside both. -/
theorem exists_restrict_eq_of_germ_eq {Y : TopCat.{0}} (S : Set Y) (n : ℕ) {V W₀ : Opens Y}
    (y : Y) (hyV : y ∈ V) (hy : y ∈ W₀)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) S) n)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (W₀ : Set Y) S) n)
    (h : supportRelativeCohomologyGerm Y S n V y hyV a =
      supportRelativeCohomologyGerm Y S n W₀ y hy b) :
    ∃ (W : Opens Y) (hWV : W ≤ V) (hW₀ : W ≤ W₀), y ∈ W ∧
      relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (W := (W : Set Y)) (V := (V : Set Y)) hWV S) a =
        relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (W := (W : Set Y)) (V := (W₀ : Set Y)) hW₀ S) b := by
  have h1 : V ⊓ W₀ ≤ V := inf_le_left
  have h2 : V ⊓ W₀ ≤ W₀ := inf_le_right
  have hyI : y ∈ V ⊓ W₀ := ⟨hyV, hy⟩
  have hz : supportRelativeCohomologyGerm Y S n (V ⊓ W₀) y hyI
      (relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (W := ((V ⊓ W₀ : Opens Y) : Set Y))
            (V := (V : Set Y)) h1 S) a -
        relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (W := ((V ⊓ W₀ : Opens Y) : Set Y))
            (V := (W₀ : Set Y)) h2 S) b) = 0 := by
    rw [supportRelativeCohomologyGerm_sub, supportRelativeCohomologyGerm_restrict,
      supportRelativeCohomologyGerm_restrict, h, sub_self]
  obtain ⟨W, hWI, hyW, hW⟩ :=
    (supportRelativeCohomologyGerm_eq_zero_iff Y S n _ y hyI _).mp hz
  refine ⟨W, hWI.trans h1, hWI.trans h2, hyW, ?_⟩
  rw [map_sub, sub_eq_zero] at hW
  simp only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp] at hW
  exact hW

/-- Pulling the normal-projection coclass of a chart back along the pair homeomorphism of an open
embedding gives the normal-projection coclass of the chart extended along the embedding. -/
theorem chartNormalProjectionCoclass_pairImage {Y X : TopCat.{0}} (f : Y ⟶ X)
    (hf : IsOpenEmbedding f) (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℕ}
    (φ : OpenPartialHomeomorph Y (E × (Fin c → ℂ))) (hφ : ∀ y ∈ φ.source, y ∈ B ↔ (φ y).2 = 0)
    (hφ' : ∀ w ∈ (φ.lift_openEmbedding hf).source, w ∈ S ↔ ((φ.lift_openEmbedding hf) w).2 = 0)
    (O : Opens Y) (hO : (O : Set Y) ⊆ φ.source)
    (hO' : f '' (O : Set Y) ⊆ (φ.lift_openEmbedding hf).source) :
    relativeCohomologyMap ℚ (2 * c)
        (neighborhoodSupportPairImageIso f hf.isEmbedding (O : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).inv
        (chartNormalProjectionCoclass E c φ B hφ O hO) =
      chartNormalProjectionCoclass E c (φ.lift_openEmbedding hf) S hφ' (f '' (O : Set Y)) hO' := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 2
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    obtain ⟨⟨_, q, hq, rfl⟩, hw⟩ := w
    change (φ ((hf.isEmbedding.homeomorphImage (O : Set Y)).symm ⟨f q, q, hq, rfl⟩).1).2 =
      (φ.lift_openEmbedding hf (f q)).2
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    congr 3
    exact congrArg Subtype.val ((Homeomorph.symm_apply_eq _).mpr rfl :
      (hf.isEmbedding.homeomorphImage (O : Set Y)).symm _ = ⟨q, hq⟩)
  · ext w
    obtain ⟨_, q, hq, rfl⟩ := w
    change (φ ((hf.isEmbedding.homeomorphImage (O : Set Y)).symm ⟨f q, q, hq, rfl⟩).1).2 =
      (φ.lift_openEmbedding hf (f q)).2
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    congr 3
    exact congrArg Subtype.val ((Homeomorph.symm_apply_eq _).mpr rfl :
      (hf.isEmbedding.homeomorphImage (O : Set Y)).symm _ = ⟨q, hq⟩)

section Core

/-- Core of `cycle-class-germ`, before the degree identification. Upstream's glued coclass section
on `(X ∖ Z_sing)(ℂ)` (dimension `m` of `Z_reg`), transported to `X(ℂ)`, has at `y ∈ Z ∩ U` the germ of
`chartNormalProjectionCoclass` of every holomorphic adapted chart `e`. Route: upstream's stalk is
the germ of a flattening-chart coclass (`smoothClosedSupportCoclassStalk_eq_chartGerm`); the open
transport sends it to the coclass of the lifted chart (`supportRelativeCohomologySheafOpenIso_unit_apply`,
`chartNormalProjectionCoclass_pairImage`); the lifted chart and `e` have analytic transitions (chart
step, `analyticAt_transition_of_factor`), so their coclasses agree near `y`
(`exists_open_chartNormalProjectionCoclass_eq`). -/
theorem germ_smoothSupportSection_eq (x : X.left) (m : ℕ) (hm : m ≤ dim X.left)
    [SmoothOfRelativeDimension m (cycleComponentSmoothLocusOver X x).hom]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin (dim X.left - m) → ℂ)))
    (L : (E × (Fin (dim X.left - m) → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source, z ∈ cycleComponentSupport X x ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (hyZ : y ∈ cycleComponentSupport X x) :
    (𝓗_[cycleComponentSupport X x]^(2 * (dim X.left - m))
        (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
        (cycleComponentSmoothSupportAmbientOpen X x) y hyU
      (supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
        (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
        (cycleComponentSupport X x)
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (cycleComponentSmoothClosedLiftAmbientMap_support X x)
        (2 * (dim X.left - m)) (cycleComponentSmoothSupportAmbientOpen X x)
        (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
        (smoothClosedSupportCoclassSection (cycleComponentSmoothLocusAmbientOpenOver X x)
          (cycleComponentSmoothLocusOver X x) (cycleComponentSmoothLocusClosedLiftOver X x)
          m (dim X.left))) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * (dim X.left - m)) ⟨e.source, e.open_source⟩ y hy
        (chartNormalProjectionCoclass E (dim X.left - m) e (cycleComponentSupport X x) hS
          e.source subset_rfl) := by
  set X' := cycleComponentSmoothLocusAmbientOpenOver X x
  set Y := cycleComponentSmoothLocusOver X x
  set i := cycleComponentSmoothLocusClosedLiftOver X x
  set ιT := cycleComponentSmoothClosedLiftAmbientMap X x
  have hι := cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x
  set B := Set.range (Point.map i)
  have hB : ιT ⁻¹' cycleComponentSupport X x = B := cycleComponentSmoothClosedLiftAmbientMap_support X x
  have hU : hι.functor.obj ⊤ = cycleComponentSmoothSupportAmbientOpen X x := cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x
  set σ := smoothClosedSupportCoclassSection X' Y i m (dim X.left)
  -- the point upstairs
  have hyU' : y ∈ hι.functor.obj ⊤ := hU ▸ hyU
  obtain ⟨y', -, hy'⟩ := hyU'
  have hy'B : y' ∈ B := by rw [← hB]; change ιT y' ∈ cycleComponentSupport X x; rw [hy']; exact hyZ
  obtain ⟨z0, hz0⟩ := hy'B
  set f0 := closedImmersionHolomorphicFlatteningChart X' Y i m (dim X.left) z0
  set O' := smoothClosedSupportChartOpen X' Y i m (dim X.left) z0
  have hy'O' : y' ∈ O' := hz0 ▸ mem_smoothClosedSupportChartOpen X' Y i m (dim X.left) z0
  set F' := 𝓗_[B]^(2 * (dim X.left - m))(TopCat.of (ComplexPoint X'); ℚ)
  set c0 := smoothClosedSupportChartCoclass X' Y i m (dim X.left) z0 O' (le_refl _)
  have hgerm' : F'.presheaf.germ ⊤ y' trivial σ =
      F'.presheaf.germ O' y' hy'O'
        ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X')) B (2 * (dim X.left - m))).app (op O') c0) := by
    have h1 := smoothClosedSupportCoclassSection_germ X' Y i m (dim X.left) y'
    have h2 := smoothClosedSupportCoclassStalk_eq_chartGerm X' Y i m (dim X.left) z0 y' hy'O'
    exact h1.trans h2
  obtain ⟨O'', hy'O'', i1, i2, hO''⟩ := F'.presheaf.germ_eq y' (show y' ∈ (⊤ : Opens (ComplexPoint X')) from trivial) hy'O' _ _ hgerm'
  have hO''f0 : (O'' : Set (ComplexPoint X')) ⊆ f0.source := leOfHom i2
  have hσO'' : F'.presheaf.map (homOfLE (show O'' ≤ ⊤ from le_top)).op σ =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X')) B (2 * (dim X.left - m))).app (op O'')
        (smoothClosedSupportChartCoclass X' Y i m (dim X.left) z0 O'' hO''f0) := by
    rw [show homOfLE (show O'' ≤ ⊤ from le_top) = i1 from Subsingleton.elim _ _, hO'']
    have h := ConcreteCategory.congr_hom
      ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X')) B (2 * (dim X.left - m))).naturality i2.op) c0
    refine h.symm.trans (congrArg (fun a =>
      ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X')) B
        (2 * (dim X.left - m))).app (op O'')) a) ?_)
    rw [show i2 = homOfLE (leOfHom i2) from Subsingleton.elim _ _]
    exact smoothClosedSupportChartCoclass_restrict X' Y i m (dim X.left) z0 (leOfHom i2) (le_refl _)
  have hV : hι.functor.obj O'' ≤ cycleComponentSmoothSupportAmbientOpen X x :=
    hU ▸ (hι.functor.map (homOfLE (show O'' ≤ ⊤ from le_top))).le
  have hyO'' : y ∈ hι.functor.obj O'' := ⟨y', hy'O'', hy'⟩
  have hres := supportRelativeCohomologySectionOnOpen_restrict ιT hι (cycleComponentSupport X x) B
    hB (2 * (dim X.left - m)) _ hU σ O'' hV
  refine ((𝓗_[cycleComponentSupport X x]^(2 * (dim X.left - m))
    (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ_res_apply (homOfLE hV) y hyO'' _).symm.trans ?_
  erw [hres]
  erw [hσO'']
  rw [supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]
  set f1 := f0.lift_openEmbedding hι
  have hS1 : ∀ w ∈ f1.source, w ∈ cycleComponentSupport X x ↔ (f1 w).2 = 0 := by
    rintro w ⟨q, hq, rfl⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply,
      ← closedImmersionHolomorphicFlatteningChart_mem_range_iff X' Y i m (dim X.left) z0 q hq]
    change q ∈ ιT ⁻¹' cycleComponentSupport X x ↔ q ∈ B
    rw [hB]
  have hO' : ιT '' (O'' : Set (ComplexPoint X')) ⊆ f1.source := Set.image_mono hO''f0
  have hpull := chartNormalProjectionCoclass_pairImage ιT hι (cycleComponentSupport X x) B hB f0
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X' Y i m (dim X.left) z0) hS1 O''
    hO''f0 hO'
  erw [hpull]
  change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
    (2 * (dim X.left - m)) (hι.functor.obj O'') y hyO''
    (chartNormalProjectionCoclass (Fin m → ℂ) (dim X.left - m) f1 (cycleComponentSupport X x) hS1
      (ιT '' (O'' : Set (ComplexPoint X'))) hO') = _
  -- the tangential factor of `e`
  have hfinE : FiniteDimensional ℂ E := by
    have : FiniteDimensional ℂ (E × (Fin (dim X.left - m) → ℂ)) :=
      L.symm.toLinearEquiv.finiteDimensional
    exact Module.Finite.of_injective (LinearMap.inl ℂ E (Fin (dim X.left - m) → ℂ))
      LinearMap.inl_injective
  have hrank : Module.finrank ℂ E = Module.finrank ℂ (Fin m → ℂ) := by
    have h := L.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    rw [Module.finrank_fin_fun]
    omega
  set P := (ContinuousLinearEquiv.ofFinrankEq hrank).prodCongr
    (ContinuousLinearEquiv.refl ℂ (Fin (dim X.left - m) → ℂ))
  set e₁ := e.trans P.toHomeomorph.toOpenPartialHomeomorph
  set Le₁ := P.symm.trans L
  have hsrc₁ : e₁.source = e.source := by simp [e₁]
  have hsnd₁ : ∀ z, (e₁ z).2 = (e z).2 := fun z => by simp [e₁, P]
  have he₁ : e₁.trans Le₁.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) := by
    apply StructureGroupoid.mem_maximalAtlas_of_eqOnSource
      (e := e.trans L.toHomeomorph.toOpenPartialHomeomorph)
    · constructor
      · simp [e₁, Le₁]
      · intro z _
        simp [e₁, Le₁]
    · exact he
  have hS₁ : ∀ z ∈ e₁.source, z ∈ cycleComponentSupport X x ↔ (e₁ z).2 = 0 := by
    intro z hz
    rw [hsnd₁]
    exact hS z (hsrc₁ ▸ hz)
  have hy₁ : y ∈ e₁.source := hsrc₁ ▸ hy
  have h0 : (e₁ y).2 = 0 := by rw [hsnd₁]; exact (hS y hy).mp hyZ
  subst hy'
  set l := (localChart X' (dim X.left) (Point.map i z0)).lift_openEmbedding hι
  have hl : l ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) :=
    lift_mem_maximalAtlas_smoothSupportAmbient X x
      (IsManifold.chart_mem_maximalAtlas (Point.map i z0))
  set A := closedImmersionNormalCoordinateChange X' Y i m (dim X.left) z0
  have hf : ∀ w ∈ f1.source, w ∈ l.source ∧ l w ∈ A.source ∧ f1 w = A (l w) := by
    rintro w ⟨q, hq, rfl⟩
    refine ⟨⟨q, hq.1.1, rfl⟩, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.lift_openEmbedding_apply]; exact hq.1.2.1
    · rw [OpenPartialHomeomorph.lift_openEmbedding_apply,
        OpenPartialHomeomorph.lift_openEmbedding_apply]
      rfl
  have hfs : ∀ v, f1.symm v = l.symm (A.symm v) := fun v => rfl
  have hbi := (OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy'O'.1.2
  have hA : AnalyticAt ℂ A (l (ιT y')) := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]; exact hbi.2.1
  have hA' : AnalyticAt ℂ A.symm (f1 (ιT y')) := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]; exact hbi.2.2
  have hyf1 : ιT y' ∈ f1.source := ⟨y', hy'O', rfl⟩
  obtain ⟨ht, hti⟩ := analyticAt_transition_of_factor Le₁ he₁ hl A f1 hf hfs hy₁ hyf1 hA hA'
  obtain ⟨W, hW1, hW2, hyW, heq⟩ := exists_open_chartNormalProjectionCoclass_eq (dim X.left - m)
    e₁ f1 (cycleComponentSupport X x) hS₁ hS1 (ιT y') hy₁ h0 hyf1 ht hti
  have hW'e : W ⊓ hι.functor.obj O'' ≤ ⟨e.source, e.open_source⟩ :=
    fun z hz => by have := hW1 hz.1; rwa [hsrc₁] at this
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of (ComplexPoint X))
    (cycleComponentSupport X x) (2 * (dim X.left - m)) (W := W ⊓ hι.functor.obj O'')
    inf_le_right hW'e (ιT y') ⟨hyW, hyO''⟩
  refine (chartNormalProjectionCoclass_restrict (Fin m → ℂ) _ f1 _ hS1
    (W := ((W ⊓ hι.functor.obj O'' : Opens (ComplexPoint X)) : Set (ComplexPoint X)))
    (fun z hz => hz.2) hO').trans ?_
  refine Eq.trans ?_ (chartNormalProjectionCoclass_restrict E _ e _ hS
    (W := ((W ⊓ hι.functor.obj O'' : Opens (ComplexPoint X)) : Set (ComplexPoint X)))
    hW'e subset_rfl).symm
  have h := congrArg (relativeCohomologyMap ℚ (2 * (dim X.left - m))
    (neighborhoodSupportInclusionPairMap
      (W := ((W ⊓ hι.functor.obj O'' : Opens (ComplexPoint X)) : Set (ComplexPoint X)))
      (V := (W : Set (ComplexPoint X))) (fun _ hz => hz.1) (cycleComponentSupport X x))) heq
  have h1 := chartNormalProjectionCoclass_restrict (Fin m → ℂ) _ e₁ _ hS₁
    (W := ((W ⊓ hι.functor.obj O'' : Opens (ComplexPoint X)) : Set (ComplexPoint X)))
    (V := (W : Set (ComplexPoint X))) (fun _ hz => hz.1) hW1
  have h2 := chartNormalProjectionCoclass_restrict (Fin m → ℂ) _ f1 _ hS1
    (W := ((W ⊓ hι.functor.obj O'' : Opens (ComplexPoint X)) : Set (ComplexPoint X)))
    (V := (W : Set (ComplexPoint X))) (fun _ hz => hz.1) hW2
  exact h2.symm.trans (h.symm.trans h1)

/-- The germ at `y ∈ Z ∩ U` of upstream's normalized coclass section is the germ of
`chartNormalProjectionCoclass` of every holomorphic adapted chart. The degree identification
`dim X - (dim X - p) = p` inside `cycleComponentSmoothClosedLiftCoclassSection` is removed by `subst`
on a statement generalized over the degree. -/
theorem germ_coclassSection_eq (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source, z ∈ cycleComponentSupport X x ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (hyZ : y ∈ cycleComponentSupport X x) :
    (𝓗_[cycleComponentSupport X x]^(2 * p)
        (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
        (cycleComponentSmoothSupportAmbientOpen X x) y hyU
      (cycleComponentSmoothSupportCoclassSection X x hx) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * p) ⟨e.source, e.open_source⟩ y hy
        (chartNormalProjectionCoclass E p e (cycleComponentSupport X x) hS
          e.source subset_rfl) := by
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have key : ∀ (a b : ℕ) (h : a = b)
      (τ : (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * a)
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
          (op ⊤)),
      (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin a → ℂ)))
        (L : (E × (Fin a → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
        (_ : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
          IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
        (hS : ∀ z ∈ e.source, z ∈ cycleComponentSupport X x ↔ (e z).2 = 0)
        (y : ComplexPoint X) (hy : y ∈ e.source)
        (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
        (_ : y ∈ cycleComponentSupport X x),
        (𝓗_[cycleComponentSupport X x]^(2 * a)
            (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
            (cycleComponentSmoothSupportAmbientOpen X x) y hyU
          (supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
            (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
            (cycleComponentSupport X x)
            (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
            (cycleComponentSmoothClosedLiftAmbientMap_support X x)
            (2 * a) (cycleComponentSmoothSupportAmbientOpen X x)
            (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) τ) =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
            (2 * a) ⟨e.source, e.open_source⟩ y hy
            (chartNormalProjectionCoclass E a e (cycleComponentSupport X x) hS
              e.source subset_rfl)) →
      (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin b → ℂ)))
        (L : (E × (Fin b → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
        (_ : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
          IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
        (hS : ∀ z ∈ e.source, z ∈ cycleComponentSupport X x ↔ (e z).2 = 0)
        (y : ComplexPoint X) (hy : y ∈ e.source)
        (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
        (_ : y ∈ cycleComponentSupport X x),
        (𝓗_[cycleComponentSupport X x]^(2 * b)
            (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
            (cycleComponentSmoothSupportAmbientOpen X x) y hyU
          (supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
            (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
            (cycleComponentSupport X x)
            (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
            (cycleComponentSmoothClosedLiftAmbientMap_support X x)
            (2 * b) (cycleComponentSmoothSupportAmbientOpen X x)
            (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) (h ▸ τ)) =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
            (2 * b) ⟨e.source, e.open_source⟩ y hy
            (chartNormalProjectionCoclass E b e (cycleComponentSupport X x) hS
              e.source subset_rfl)) := by
    intro a b h τ H
    subst h
    exact H
  exact key _ _ (cycleComponentSmoothClosedLift_codimension X x hx) _
    (fun e L he hS y hy hyU hyZ => germ_smoothSupportSection_eq X x (dim X.left - p)
      (Nat.sub_le _ _) e L he hS y hy hyU hyZ) e L he hS y hy hyU hyZ

end Core

/-- Rung `cycle-class-germ`. Let `Z` be the closed analytic support of `x` (coheight `p`) and
`U = X ∖ Z_sing`. Let `e` be a chart of `X(ℂ)` with values in `E × ℂ^p`, holomorphic in the sense
that `e` followed by a continuous `ℂ`-linear equivalence `L : E × ℂ^p ≃ ℂ^d` is in Mathlib's
maximal analytic atlas of `X(ℂ)`, and adapted to `Z`: on `e.source`, `Z` is the zero set of the
normal coordinate `(e ·).2`. Then every `y ∈ e.source ∩ U` has an open neighborhood `W ⊆ e.source`
on which the restriction of upstream's singular transport of the supported cycle class `[Z]` is
upstream's `chartNormalProjectionCoclass` of `e`: the pullback along the normal projection of the
class pairing to `1` with the complex orientation class of `(ℂ^p, ℂ^p ∖ 0)`. The identity is exact,
with no sign and no scalar; it holds for every such chart, and the choice of `L` does not matter.

Conventions (`docs/conventions.md`): rows "Complex orientation of ℂ^p", "Fundamental-class
normalization", "Normalization iso against the singular transport" and "Holomorphic adapted
chart". Without holomorphy the identity fails for odd `p` (a conjugated normal coordinate changes
the right side by `(-1)^p`).

The hypothesis `hyU` is automatic for `y ∉ Z`, since `Z_sing ⊆ Z`. For `y ∈ Z` it follows from
`he` and `hS` (the reduced closure is regular where its analytic germ is a submanifold), an
implication not at the pin (rung `analytic-smooth-locus`). -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ e.source), y ∈ W ∧
      relativeCohomologyMap ℚ (2 * p)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
            ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p)
              (cycleComponentSupportedInjectiveClass X x hx))) =
        chartNormalProjectionCoclass E p e
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS W hW := by
  have hgerm : supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p) ⊤ y trivial
      (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
        ⊤ (2 * p)
        (rationalSupportAddEquivSupportedInjectiveHomology X
          (cycleComponentAnalyticClosedSupport X x) (2 * p)
          (cycleComponentSupportedInjectiveClass X x hx))) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
        ⟨e.source, e.open_source⟩ y hy
        (chartNormalProjectionCoclass E p e
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS e.source
          subset_rfl) := by
    by_cases hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))
    · refine (supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
        (U := cycleComponentSmoothSupportAmbientOpen X x) (V := ⊤) le_top y hyU _).symm.trans ?_
      refine (congrArg ((𝓗_[cycleComponentSupport X x]^(2 * p)
        (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
        (cycleComponentSmoothSupportAmbientOpen X x) y hyU)
          (coclassSection_eq_singular X x hx).symm).trans ?_
      exact germ_coclassSection_eq X x hx e L he hS y hy hyU hyZ
    · exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
          (cycleComponentAnalyticClosedSupport X x).isClosed ⊤ y trivial hyZ _).trans
        (supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ y hy hyZ _).symm
  obtain ⟨W, _, hWe, hyW, heqW⟩ := exists_restrict_eq_of_germ_eq
    (Y := TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p) (V := ⊤)
    (W₀ := ⟨e.source, e.open_source⟩) y trivial hy _ _ hgerm
  exact ⟨W, hWe, hyW, heqW.trans (chartNormalProjectionCoclass_restrict E p e _ hS hWe subset_rfl)⟩


end HodgeLadder.Normalization
