module

public import HodgeLadder.Cup.SingularUnit
public import HodgeLadder.Cup.SupportedPairForget
public import HodgeLadder.Cup.RelCupNaturality
public import LefschetzPort.AlgebraicTopology.LinearDualConnecting
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
public import HodgeLadder.Normalization.Germ
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison
public import Other.AlgebraicGeometry.Cohomology.RationalDegreeZero
public import Other.AlgebraicGeometry.Cycle.Component.CoclassNonzero
public import Other.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-!
# The class of `X` is the unit

Rung `fundamental-class-unit` (front `cup`, decision 0010, the smallest falsification test of
`cycle-class-multiplicative`). For a smooth integral projective `X` over `ℂ`, upstream's cycle
class of the generic point, `[X] ∈ H⁰(X; ℚ)`, is the unit `one X` of the ladder's Yoneda cup
product. The identity is exact: no sign, no scalar.

Route. `H⁰(X; ℚ)` is a line on the connected `X(ℂ)`, so `[X] = c • one X` with `c ≠ 0`
(upstream `rationalCohomologyClass_surjective`, `cycleComponentSheafClass_genericPoint_ne_zero`).
Under upstream's comparison `Ψ` with singular cohomology, `one X` goes to the class `oneSing` of
the constant `0`-cocycle `1` (from `cup_singular_comparison` at `p = 0` and the singular unit
laws, `HodgeLadder.Cup.SingularUnit`). Take a point `y` of `X(ℂ) ∖ Z_sing(ℂ)` for `Z` the reduced
closure of the generic point, and the chart `chartAt y` (`adaptedChart_genericPoint`). On a
neighbourhood `W` of `y` the restriction of `Ψ [X]` is the underlying absolute class of upstream's
degree-`0` normal projection coclass (`cycle-class-germ`, `supported-pair-forget`), and that class
is `oneSing W`:
at `c = 0` the coclass is pulled back from the point `ℂ⁰ ≅ ℝ⁰`, where upstream's standard local
class is the point with coefficient `1`. So `oneSing W = c • oneSing W`, `oneSing W ≠ 0`, and
`c = 1`.

## Main results

* `HodgeLadder.Tests.cycleComponentSheafClass_genericPoint_eq_one`: the rung.
* `HodgeLadder.Tests.cycleComponentSheafClass_genericPoint_ne_neg_one`: the sign test `[X] ≠ −1`.
* `HodgeLadder.Tests.exists_cycleComponentSheafClass_genericPoint_eq_smul_one`: `[X] = c • 1`,
  `c ≠ 0`.
* `HodgeLadder.Tests.exists_mem_cycleComponentSmoothSupportAmbientOpen`: `X(ℂ) ∖ Z_sing(ℂ)` has a
  point, for every component `Z`.
* `HodgeLadder.Tests.forgetRel_eq_oneSing_of_standardLocalClass_zero`: on `ℝ⁰`, a class taking
  the value `1` on upstream's standard local class forgets to `oneSing`.
* `HodgeLadder.Tests.forgetRel_chartNormalProjectionCoclass_zero`: the degree-`0` normal
  projection coclass forgets to `oneSing`.

The singular unit `oneSing`, its laws, `Ψ (one X) = oneSing` and `one X = fieldCohomologyUnit ℚ X`
are in `HodgeLadder.Cup.SingularUnit` (rung `singular-unit`).
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Cup HodgeLadder.Normalization

namespace HodgeLadder.Tests

/-! ### The unit on the sheaf side -/

/-- **`[X]` is a nonzero multiple of the unit.** `H⁰(X; ℚ)` is spanned by upstream's unit on the
connected `X(ℂ)`, and `[X] ≠ 0` upstream. -/
theorem exists_cycleComponentSheafClass_genericPoint_eq_smul_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℚ, c ≠ 0 ∧
      cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
        c • (one X : H^(2 * 0)(X; ℚ)) := by
  let _ : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let _ : ConnectedSpace (ComplexPoint X) := ComplexPoint.connectedSpace X
  obtain ⟨q, hq⟩ := rationalCohomologyClass_surjective X
    (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
  refine ⟨q, ?_, ?_⟩
  · rintro rfl
    exact cycleComponentSheafClass_genericPoint_ne_zero X
      (hq.symm.trans (fieldCohomologyClass_zero ℚ X))
  · rw [← hq, one_eq_fieldCohomologyUnit]
    simpa [fieldCohomologyUnit] using fieldCohomologyClass_mul ℚ X q 1

section Variety

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The smooth ambient open `X(ℂ) ∖ Z_sing(ℂ)` of every component has a point: the image of a
complex point of the component's smooth locus (upstream
`cycleComponentSmoothLocusOver_nonempty`). -/
theorem exists_mem_cycleComponentSmoothSupportAmbientOpen (x : X.left) :
    ∃ y : ComplexPoint X, y ∈ cycleComponentSmoothSupportAmbientOpen X x := by
  obtain ⟨z⟩ := cycleComponentSmoothLocusOver_nonempty X x
  let g : cycleComponentSmoothLocusOver X x ⟶ X :=
    Over.homMk ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x) rfl
  refine ⟨Point.map g z, ?_⟩
  rintro ⟨w, hw, hwz⟩
  have hinj := (cycleComponentι X.left x).isClosedEmbedding.injective
  rw [Point.underlying_map] at hwz
  have h := hinj hwz
  apply hw
  rw [h]
  exact (Point.underlying z).2

end Variety

/-- **On the point `ℝ⁰`, a degree-`0` class normalized on the standard local class forgets to
the unit.** Upstream's `standardLocalClass ℚ 0` is the class of the unique singular point with
coefficient `1` (`standardAmbientClassZero_projection`), and the constant cocycle `1` takes the
value `1` there; `H₀(ℝ⁰; ℚ)` is a line (`span_standardLocalClass_zero_eq_top`, whose
nonvanishing input is the augmentation `standardLocalClass_zero_epsilon`). This is where the sign
of `[X]` is decided; `docs/conventions.md`, row "Degree-zero orientation and the unit". -/
theorem forgetRel_eq_oneSing_of_standardLocalClass_zero
    (γ : RelativeCohomology ℚ (puncturedPair ℝ 0) 0)
    (hγ : relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ 0) 0 γ
      (standardLocalClass ℚ 0) = 1) :
    forgetRel (puncturedPair ℝ 0) 0 γ = oneSing (TopCat.of (Fin 0 → ℝ)) := by
  apply (cohomologyEquivDualHomology ℚ (puncturedPair ℝ 0).fst 0).injective
  have hspan : Submodule.span ℚ {standardAmbientClassZero} = ⊤ := by
    have h := span_standardLocalClass_zero_eq_top
    rw [← standardAmbientClassZero_projection] at h
    let eL := standardRelativeHomologyProjectionZeroIso.toLinearEquiv
    have h' := congrArg (Submodule.map eL.symm.toLinearMap) h
    rw [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h'
    convert h'
    exact (eL.symm_apply_apply _).symm
  refine LinearMap.ext_on hspan ?_
  rintro _ rfl
  refine (cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ (puncturedPair ℝ 0) 0 γ
    standardAmbientClassZero).trans ?_
  refine ((congrArg (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ 0) 0 γ)
    standardAmbientClassZero_projection).trans hγ).trans ?_
  symm
  set K := SingularChainComplex ℚ (puncturedPair ℝ 0).fst
  set c := (TopCat.of (Fin 0 → ℝ)).constSingularCocycle ℚ (𝟙 (𝟙_ (ModuleCat.{0} ℚ)))
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (dualIsoYoneda K).inv 0) c
  refine (congrArg (fun t => HomologicalComplex.linearDualHomologyEquiv K 0 t
    (K.homologyπ 0 (standardAmbientCycleZero.hom 1))) hπ).trans ?_
  erw [HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (dualIsoYoneda K).inv 0) c
  have h2 := ConcreteCategory.congr_hom (show standardAmbientCycleZero ≫ K.iCycles 0 =
    standardAmbientSimplexChain ℚ 0 from HomologicalComplex.liftCycles_i _ _ _ _ _) 1
  have h3 := TopCat.iCycles_constSingularCocycle (TopCat.of (Fin 0 → ℝ)) ℚ
    (𝟙 (𝟙_ (ModuleCat.{0} ℚ)))
  erw [h1, h2]
  change ConcreteCategory.hom (show (((TopCat.toSSet.obj (TopCat.of (Fin 0 → ℝ))).chainComplex
      (𝟙_ (ModuleCat.{0} ℚ))).X 0 ⟶ 𝟙_ (ModuleCat.{0} ℚ)) from
      ((TopCat.of (Fin 0 → ℝ)).singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
        (𝟙_ (ModuleCat.{0} ℚ))).iCycles 0 c)
      (ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of (Fin 0 → ℝ))).ιChainComplex
        (R := 𝟙_ (ModuleCat.{0} ℚ)) (standardSingularSimplex 0)) 1) = 1
  rw [h3, ← ConcreteCategory.comp_apply]
  dsimp only
  erw [SSet.ιChainComplex_constCochain (TopCat.toSSet.obj (TopCat.of (Fin 0 → ℝ)))
    (𝟙 (𝟙_ (ModuleCat.{0} ℚ))) (standardSingularSimplex 0)]
  rfl

/-- **The degree-`0` normal projection coclass forgets to the unit.** At `c = 0` the normal
projection is the map to the point `ℂ⁰`; upstream's normalized class on `(ℂ⁰, ∅)` is moved to
`(ℝ⁰, ∅)` along `standardComplexRealPairIso 0`, where
`forgetRel_eq_oneSing_of_standardLocalClass_zero` applies. -/
theorem forgetRel_chartNormalProjectionCoclass_zero {M : Type} [TopologicalSpace M]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph M (E × (Fin 0 → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (W : Set M) (hW : W ⊆ e.source) :
    forgetRel (neighborhoodSupportComplementPair W S) (2 * 0)
        (chartNormalProjectionCoclass E 0 e S hS W hW) =
      (oneSing (TopCat.of W) : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of W) (2 * 0)) := by
  rw [chartNormalProjectionCoclass, forgetRel_relativeCohomologyMap]
  set N := normalizedRelativeCoclass (standardComplexLocalClass ℚ 0)
    (standardComplexLocalClass_ne_zero_for_chart 0)
  set iso := standardComplexRealPairIso 0
  set γ := relativeCohomologyMap ℚ 0 iso.inv N
  have hN : N = relativeCohomologyMap ℚ 0 iso.hom γ :=
    (relativeCohomologyMap_inv_hom_apply iso.symm 0 N).symm
  have hγ : relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ 0) 0 γ
      (standardLocalClass ℚ 0) = 1 := by
    rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap]
    have : relativeHomologyMap ℚ 0 iso.inv (standardLocalClass ℚ 0) =
        standardComplexLocalClass ℚ 0 := rfl
    rw [this]
    exact (congrArg (fun φ => φ (standardComplexLocalClass ℚ 0))
      (relativeCohomologyEquivDualHomology_normalizedRelativeCoclass _ _)).trans
      (normalizedDual_apply_self _ _)
  have h1 : forgetRel (puncturedPair ℂ 0) (2 * 0) N = oneSing (TopCat.of (Fin 0 → ℂ)) := by
    rw [hN, forgetRel_relativeCohomologyMap, forgetRel_eq_oneSing_of_standardLocalClass_zero γ hγ]
    exact cohomologyMap_oneSing _
  rw [h1]
  exact cohomologyMap_oneSing _

/-- **The class of `X` is the unit** (rung `fundamental-class-unit`): for a smooth integral
projective `X` over `ℂ`, upstream's cycle class of the generic point is the unit of the ladder's
cup product in `H⁰(X; ℚ)`. Exact, sign `+`, no scalar. Conventions: rows "Degree-zero orientation
and the unit", "Fundamental-class normalization" (`docs/conventions.md`). -/
theorem cycleComponentSheafClass_genericPoint_eq_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
      (one X : H^(2 * 0)(X; ℚ)) := by
  let _ : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  obtain ⟨c, -, hc⟩ := exists_cycleComponentSheafClass_genericPoint_eq_smul_one X
  rw [hc]
  suffices h1 : c = 1 by rw [h1, one_smul]
  set g := genericPoint X.left
  set Z := cycleComponentAnalyticClosedSupport X g
  set S := cycleComponentSupportedInjectiveClass X g (coheight_genericPoint_eq_zero X)
  set TS := complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2 * 0)
    (rationalSupportAddEquivSupportedInjectiveHomology X Z (2 * 0) S)
  -- a point of `X(ℂ) ∖ X_sing(ℂ)` and the chart `chartAt y` at it
  obtain ⟨y, hyU⟩ := exists_mem_cycleComponentSmoothSupportAmbientOpen X g
  obtain ⟨he, hS, hy⟩ := adaptedChart_genericPoint X y
  obtain ⟨W, hW, hyW, hWeq⟩ := transport_supportedClass_eq_chartNormalProjectionCoclass X g
    (coheight_genericPoint_eq_zero X) _ _ he hS y hy hyU
  -- forget the subspace on both sides of the germ identity
  have hB := congrArg (forgetRel (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
    (Z : Set (ComplexPoint X))) (2 * 0)) hWeq
  rw [forgetRel_relativeCohomologyMap, forgetRel_chartNormalProjectionCoclass_zero] at hB
  -- `Ψ [X]` is the pullback of `forgetRel (T S)` along the identity `X(ℂ) ≅ ⊤`
  have hA : rationalCohomologyAddEquivSingularCohomology X (2 * 0)
      (cycleComponentSheafClass X g (coheight_genericPoint_eq_zero X)) =
      cohomologyMap ℚ (2 * 0) (TopPair.Hom.fst (ofSubsetIsoNeighborhoodTop Z).hom)
        (forgetRel (neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X)) :
          Set (ComplexPoint X)) (Z : Set (ComplexPoint X))) (2 * 0) TS) := by
    rw [cycleComponentSheafClass, ← forgetRel_supportedEquivPair, supportedEquivPair_eq_transport,
      forgetRel_relativeCohomologyMap]
    rfl
  let ι : TopCat.of (W : Set (ComplexPoint X)) ⟶ TopCat.of (ComplexPoint X) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hC : cohomologyMap ℚ 0 ι (rationalCohomologyAddEquivSingularCohomology X (2 * 0)
      (cycleComponentSheafClass X g (coheight_genericPoint_eq_zero X))) =
      oneSing (TopCat.of (W : Set (ComplexPoint X))) := by
    rw [hA]
    exact (LinearMap.congr_fun (cohomologyMap_comp ℚ 0 ι
      (TopPair.Hom.fst (ofSubsetIsoNeighborhoodTop Z).hom)) _).symm.trans hB
  rw [hc, map_rat_smul, rationalCohomologyAddEquivSingularCohomology_one, map_smul,
    cohomologyMap_oneSing] at hC
  have : Nonempty (W : Set (ComplexPoint X)) := ⟨⟨y, hyW⟩⟩
  have h2 : (c - 1) • oneSing (TopCat.of (W : Set (ComplexPoint X))) = 0 := by
    rw [sub_smul, one_smul, hC, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (oneSing_ne_zero _))

/-- Sign test for `fundamental-class-unit`: `[X] ≠ −1`. -/
theorem cycleComponentSheafClass_genericPoint_ne_neg_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) ≠
      -(one X : H^(2 * 0)(X; ℚ)) := by
  rw [cycleComponentSheafClass_genericPoint_eq_one]
  intro h
  have h2 : (2 : ℚ) • (one X : H^(2 * 0)(X; ℚ)) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · have : Nonempty (ComplexPoint X) :=
      ⟨(exists_mem_cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left)).choose⟩
    rw [one_eq_fieldCohomologyUnit] at h3
    exact rationalCohomologyUnit_ne_zero X h3

end HodgeLadder.Tests