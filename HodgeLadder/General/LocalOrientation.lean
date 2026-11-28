module

public import Other.AlgebraicGeometry.ComplexPoint.LocalOrientationNeighborhood
public import Other.AlgebraicTopology.Sheaf.HomologySection
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Point independence of the complex local orientation

General lemmas kept local (decision 0011), used by rung `p2-fundamental-class-every-point`. Let `X`
be a smooth complex scheme of relative dimension `d` with `X(ℂ)` Hausdorff. The coefficient of a
relative class against upstream's `complexLocalOrientation` is locally constant; on a preconnected
`X(ℂ)`, a class of `H₂d(X(ℂ); ℚ)` whose image at one point is the complex local orientation has
image the complex local orientation at every point.

The argument goes through the singular homology sheaf in place of an injectivity statement for
`Hₙ(X, X ∖ N) → Hₙ(X, X ∖ z)`:

1. A relative class `c ∈ H₂d(X, X ∖ U; ℚ)` on an open `U` gives a section of upstream's homology
   sheaf `singularChainHomologySheaf` over `U`, whose germ at `z ∈ U` is, under upstream's stalk
   identification, the restriction of `c` to `H₂d(X, X ∖ z; ℚ)`
   (upstream's `relativeHomologyToHomologySheafSection_germ`).
2. Every element of `H₂d(X, X ∖ y; ℚ)` is `q • complexLocalOrientation X d y` for a unique `q`
   (upstream's `span_complexLocalOrientation_eq_top` and `localClassOfChart_ne_zero`).
3. If `c` restricts to `q • o_y` at `y`, its section and the section of
   `q • complexLocalOrientationNeighborhoodClass X d y` have equal germs at `y`, hence agree on an
   open `W ∋ y` (Mathlib's `TopCat.Presheaf.germ_eq`), and the second restricts to `q • o_z` at
   every `z` of its neighborhood (upstream's `complexLocalOrientationNeighborhoodClass_restrict`).
   So the coefficient of `c` at `z` is locally constant.
4. On a preconnected space a locally constant coefficient is constant; it is `1` at one point, so
   `1` everywhere.
5. The projection `Hₙ(X) → Hₙ(X, X ∖ y)` factors through `Hₙ(X, X ∖ X)` by the naturality of
   upstream's `relativeChainProjection`, which puts a class of `Hₙ(X)` in step 4.

No sign or normalization enters: the only scalar is the coefficient of step 2, proved equal to `1`
at every point. A transition between charts reversing orientation would contradict step 3; upstream
excludes it by its chart coherence `localClassOfChart_localChart_eq` (row "Coherence of the complex
local orientation" of `docs/conventions.md`).

## Main results

* `HodgeLadder.LocalOrientation.relativeHomologyProjection_eq_complexLocalOrientation_of_eq`: point
  independence of a class of `H₂d(X(ℂ); ℚ)` on a Hausdorff preconnected `X(ℂ)`.
* `HodgeLadder.LocalOrientation.restrict_top_eq_complexLocalOrientation`: the same for a class of
  `H₂d(X(ℂ), X(ℂ) ∖ X(ℂ); ℚ)`.
* `HodgeLadder.LocalOrientation.eventually_restrict_eq_smul`: the coefficient of a relative class
  against the complex local orientation is locally constant.
* `HodgeLadder.LocalOrientation.homologySheafStalkIso_germ_section`: germs of homology-sheaf
  sections are restrictions, for any Hausdorff space.
* `HodgeLadder.LocalOrientation.exists_eq_smul_complexLocalOrientation`,
  `smul_complexLocalOrientation_injective`: the coefficient exists and is unique.
* `HodgeLadder.LocalOrientation.relativeHomologyProjection_pointComplementPair_eq`: the projection
  to the point pair factors through the pair `(X, ∅)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLadder.LocalOrientation

/-- The germ at `z ∈ U` of the homology-sheaf section of a relative class `c` on `U`, read
through upstream's stalk identification, is the restriction of `c` to the point pair at `z`.
Element form of upstream's `relativeHomologyToHomologySheafSection_germ`, for any Hausdorff
space `Y`. -/
theorem homologySheafStalkIso_germ_section (Y : TopCat.{0}) [T2Space Y] (n : ℕ) (U : Opens Y)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := Y) (U : Set Y)ᶜ) n) (z : Y) (hz : z ∈ U) :
    (singularChainHomologySheafStalkIso ℚ Y z n).hom
      ((singularChainHomologySheaf ℚ Y n).presheaf.germ U z hz
        (relativeHomologyToHomologySheafSection ℚ Y U n c)) =
      relativeHomologyMap ℚ n (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hz)) c := by
  have h := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ Y U z hz n) c
  simp only [ConcreteCategory.comp_apply] at h
  exact h

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

variable [SmoothOfRelativeDimension d X.hom]

/-- **The coefficient is locally constant.** If a relative class `c` on an open `U` restricts to
`q • complexLocalOrientation X d y` at `y ∈ U`, then on some open `W` with `y ∈ W ≤ U` it restricts
to `q • complexLocalOrientation X d z` at every `z ∈ W`. The comparison is with upstream's
neighborhood class `complexLocalOrientationNeighborhoodClass X d y`, through the germs of the
singular homology sheaf. -/
theorem eventually_restrict_eq_smul [T2Space (ComplexPoint X)] (U : Opens (ComplexPoint X))
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (U : Set (ComplexPoint X))ᶜ) (2 * d)) (y : ComplexPoint X) (hy : y ∈ U) (q : ℚ)
    (hq : relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of (ComplexPoint X))
          (Set.singleton_subset_iff.mpr hy)) c = q • complexLocalOrientation X d y) :
    ∃ W : Opens (ComplexPoint X), y ∈ W ∧ ∃ hWU : W ≤ U, ∀ (z : ComplexPoint X) (hz : z ∈ W),
      relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of (ComplexPoint X))
          (Set.singleton_subset_iff.mpr (hWU hz))) c = q • complexLocalOrientation X d z := by
  let F := (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) (2 * d)).presheaf
  let N := complexLocalOrientationNeighborhood X d y
  have hyN : y ∈ N := mem_complexLocalOrientationNeighborhood X d y
  let s := relativeHomologyToHomologySheafSection ℚ (TopCat.of (ComplexPoint X)) U (2 * d) c
  let s' := relativeHomologyToHomologySheafSection ℚ (TopCat.of (ComplexPoint X)) N (2 * d)
    (q • complexLocalOrientationNeighborhoodClass X d y)
  have key : ∀ (z : ComplexPoint X) (hz : z ∈ N),
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X)) z (2 * d)).hom
        (F.germ N z hz s') = q • complexLocalOrientation X d z := by
    intro z hz
    rw [homologySheafStalkIso_germ_section, map_smul,
      complexLocalOrientationNeighborhoodClass_restrict X d y z hz]
  have hinj : ∀ z : ComplexPoint X, Function.Injective
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X)) z (2 * d)).hom :=
    fun z ↦ ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).injective
  have hgerm : F.germ U y hy s = F.germ N y hyN s' := by
    apply hinj y
    rw [key, homologySheafStalkIso_germ_section, hq]
  obtain ⟨W, hyW, iU, iN, hW⟩ := TopCat.Presheaf.germ_eq F y hy hyN s s' hgerm
  refine ⟨W, hyW, iU.le, fun z hz ↦ ?_⟩
  rw [← homologySheafStalkIso_germ_section (TopCat.of (ComplexPoint X)) (2 * d) U c z (iU.le hz), ← key z (iN.le hz),
    ← TopCat.Presheaf.germ_res_apply F iU z hz, ← TopCat.Presheaf.germ_res_apply F iN z hz]
  exact congrArg _ (congrArg _ hW)

/-- Every class of `H₂d(X, X ∖ y; ℚ)` is a rational multiple of the complex local orientation
(upstream's `span_complexLocalOrientation_eq_top`). -/
theorem exists_eq_smul_complexLocalOrientation [T1Space (ComplexPoint X)] (y : ComplexPoint X)
    (a : RelativeHomology ℚ (pointComplementPair y) (2 * d)) :
    ∃ q : ℚ, a = q • complexLocalOrientation X d y := by
  have ha : a ∈ Submodule.span ℚ {complexLocalOrientation X d y} := by
    rw [span_complexLocalOrientation_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨q, hq.symm⟩

/-- The coefficient against the complex local orientation is unique, since the orientation is
nonzero (upstream's `localClassOfChart_ne_zero`). -/
theorem smul_complexLocalOrientation_injective [T1Space (ComplexPoint X)] (y : ComplexPoint X) :
    Function.Injective (fun q : ℚ ↦ q • complexLocalOrientation X d y) :=
  smul_left_injective ℚ (localClassOfChart_ne_zero d (localChart X d y) y
    (mem_localChart_source X d y))

/-- **Point independence for a global relative class.** On a preconnected `X(ℂ)`, a class of
`H₂d(X, X ∖ X; ℚ)` that restricts to the complex local orientation at one point restricts to it
at every point. -/
theorem restrict_top_eq_complexLocalOrientation [T2Space (ComplexPoint X)]
    [PreconnectedSpace (ComplexPoint X)]
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) (2 * d))
    (x : ComplexPoint X)
    (hx : relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of (ComplexPoint X))
          (Set.singleton_subset_iff.mpr (Set.mem_univ x))) c = complexLocalOrientation X d x)
    (y : ComplexPoint X) :
    relativeHomologyMap ℚ (2 * d)
        (supportInclusionPairMap (TopCat.of (ComplexPoint X))
          (Set.singleton_subset_iff.mpr (Set.mem_univ y))) c = complexLocalOrientation X d y := by
  choose f hf using fun z : ComplexPoint X ↦ exists_eq_smul_complexLocalOrientation X d z
    (relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (ComplexPoint X))
        (Set.singleton_subset_iff.mpr (Set.mem_univ z))) c)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨W, hzW, hWU, hW⟩ := eventually_restrict_eq_smul X d ⊤ c z (Set.mem_univ z) (f z)
      (hf z)
    filter_upwards [W.isOpen.mem_nhds hzW] with w hw
    exact smul_complexLocalOrientation_injective X d w ((hf w).symm.trans (hW w hw))
  have hfx : f x = 1 :=
    smul_complexLocalOrientation_injective X d x ((hf x).symm.trans (hx.trans (one_smul _ _).symm))
  rw [hf y, hloc.apply_eq_of_preconnectedSpace y x, hfx, one_smul]

omit [SmoothOfRelativeDimension d X.hom] in
/-- The projection `Hₙ(X) → Hₙ(X, X ∖ y)` is the projection `Hₙ(X) → Hₙ(X, X ∖ X)` followed by
the support inclusion `{y} ⊆ X` (naturality of upstream's `relativeChainProjection`; the map of
pairs is the identity on `X`). -/
theorem relativeHomologyProjection_pointComplementPair_eq (n : ℕ)
    (μ : Homology ℚ (TopCat.of (ComplexPoint X)) n) (y : ComplexPoint X) :
    (relativeHomologyProjection ℚ (pointComplementPair y) n).hom μ =
      relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of (ComplexPoint X))
          (Set.singleton_subset_iff.mpr (Set.mem_univ y)))
        ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
          ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) n).hom μ) := by
  have h := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
    (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (Set.mem_univ y)))
  have hfst : TopPair.Hom.fst (supportInclusionPairMap (TopCat.of (ComplexPoint X))
      (Set.singleton_subset_iff.mpr (Set.mem_univ y))) = 𝟙 _ := rfl
  erw [hfst, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have := congrArg (fun φ ↦ (HomologicalComplex.homologyMap φ n : ModuleCat.Hom _ _).hom μ) h
  simp only [HomologicalComplex.homologyMap_comp] at this
  exact this.symm

/-- **Point independence of the fundamental class.** On a smooth complex `X` of relative
dimension `d` with `X(ℂ)` Hausdorff and preconnected, a class of `H₂d(X(ℂ); ℚ)` whose image in
`H₂d(X(ℂ), X(ℂ) ∖ x; ℚ)` is `complexLocalOrientation X d x` at one point `x` has image
`complexLocalOrientation X d y` at every point `y`. -/
theorem relativeHomologyProjection_eq_complexLocalOrientation_of_eq [T2Space (ComplexPoint X)]
    [PreconnectedSpace (ComplexPoint X)]
    (μ : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d)) (x : ComplexPoint X)
    (hx : (relativeHomologyProjection ℚ (pointComplementPair x) (2 * d)).hom μ =
      complexLocalOrientation X d x) (y : ComplexPoint X) :
    (relativeHomologyProjection ℚ (pointComplementPair y) (2 * d)).hom μ =
      complexLocalOrientation X d y := by
  rw [relativeHomologyProjection_pointComplementPair_eq] at hx ⊢
  exact restrict_top_eq_complexLocalOrientation X d _ x hx y

end HodgeLadder.LocalOrientation
