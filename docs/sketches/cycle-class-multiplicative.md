# Sketch: `cycle-class-multiplicative`

Date: 2026-11-26. Front `cup`, decisions 0008, 0009 and 0010, rung 6, and the front's kill criterion. Red team: pass with changes (`docs/sketches/cycle-class-multiplicative.redteam.md`), implemented below. Local input: `docs/sketches/local-class-product.md`. This is a plan. Nothing in it is checked, and each identity below is a target.

## Statement

**Plain words.** Let X be smooth, integral and projective over ℂ, of dimension d, and Z, W, T integral subvarieties of codimensions a, b, a + b with T(ℂ) = Z(ℂ) ∩ W(ℂ). Suppose Z and W meet transversally along T: every point of T(ℂ) lies in Z_reg and W_reg and has a holomorphic chart in which Z is {first a coordinates = 0} and W is {next b coordinates = 0}. Then [Z] ∪ [W] = [T] in H^{2(a+b)}(X; ℚ), with sign +, for upstream's cycle classes `cycleComponentSheafClass` and the ladder's Yoneda cup `HodgeLadder.Cup.cup`. Degrees are even, so factor order does not matter (`cup_gradedComm`).

**Literature.** For X nonsingular the cycle map A^*(X) → H^{2*}(X) is a ring homomorphism, and a transversal intersection has multiplicity one [`Fulton1998` Cor. 19.2 and §8.2; numbering unverified]. Cohomology with supports and its products [`Iversen1986`, `Bredon1997`; chapters unverified]. Test cases, in the order of decision 0010: codimension zero on every X (`cycle-class-multiplicative-codim-zero`); the coordinate lines L₀ = {x₀ = 0}, L₁ = {x₁ = 0} on ℙ², meeting in [0 : 0 : 1] (`cycle-class-multiplicative-p2`); then the two fibres {∞} × ℙ¹ and ℙ¹ × {∞} on ℙ¹ × ℙ¹, meeting in (∞, ∞), the case decision 0009 named first (`cycle-class-multiplicative-p1p1`).

**Proposed Lean.** Elaborated with `lake env lean` on a scratch file inside the worktree (deleted), and instantiated at the level of instances on the ladder's `HodgeLadder.Tests.projectiveLine`:

```lean
theorem cycleComponentSheafClass_cup_of_transversal
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    (x w t : X.left) {a b : ℕ} (hx : Order.coheight x = a) (hw : Order.coheight w = b)
    (ht : Order.coheight t = a + b) (hd : a + b ≤ d)
    (hT : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) =
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ∩
        cycleComponentAnalyticClosedSupport X w)
    (hxreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x)
    (hwreg : (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X w)
    (htr : ∀ y ∈ (cycleComponentAnalyticClosedSupport X t : Set (ComplexPoint X)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X), y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport X x ↔ ∀ i : Fin a, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport X w ↔ ∀ j : Fin b, φ z ⟨a + j, by omega⟩ = 0)) :
    cup (cycleComponentSheafClass X x hx) (cycleComponentSheafClass X w hw) (2 * (a + b))
        (by ring) =
      cycleComponentSheafClass X t ht
```

The chart condition uses upstream's charted-space instance on X(ℂ) (`localChart`) and Mathlib's maximal analytic atlas; it is the literature's transversality in local holomorphic coordinates. `hxreg`, `hwreg` are stated because upstream's normalization lives on X(ℂ) ∖ Z_sing(ℂ), and the analytic-implies-algebraic smoothness needed to drop them is not at the pin. Red-team result on the hypotheses: at a = b = 0 and x = w = t = the generic point, `hT` and `htr` hold on every X (scratch S5, from upstream's `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`, Mathlib's `IsManifold.chart_mem_maximalAtlas` and `mem_chart_source`); `hxreg` needs one lemma missing at the pin, `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`, proved inside `cycle-class-multiplicative-codim-zero`. On ℙ² and ℙ¹ × ℙ¹ two more items are needed: the algebraic affine chart lies in Mathlib's maximal atlas, measured against upstream's `localChart` (`affine-chart-analytic`), and the intersection point lies off the singular locus of each component's reduced closure (`p2-lines-transversal`, `p1p1-fibres-transversal`). Several components, [Z] ∪ [W] = Σ [T_i] (line and conic in ℙ²), is the next case of the literature; it would be a new rung, and this one is unchanged by it.

## Why the ladder needs it

It is the kill criterion of front `cup`: products of algebraic classes are the reason to have a product. `cup-positive-degree-test` (closes the vacuity gap of the ring laws) and every product of cycle classes in M2 and M3 go through it.

## Proof idea

1. Singular side. With `cup_singular_comparison` (sign (−1)^{(2a)(2b)} = 1), Ψ([Z] ∪ [W]) = cupSing (Ψ[Z]) (Ψ[W]).
2. Supported lifts. Ψ[Z] = forgetRel (Φ_X α_Z) on (X, X ∖ Z), from `supported_forget_compat` moved to `TopPair.ofSubset` by `supportedEquivPair` (rung `cup-comparison-supported-pair`); α_Z = `cycleComponentSupportedInjectiveClass`.
3. Relative product. By `triad-relative-cup`, cupSing (forgetRel a) (forgetRel b) = forgetRel (relCup2 a b) with relCup2 a b ∈ H^{2(a+b)}(X, (X ∖ Z) ∪ (X ∖ W)) = H^{2(a+b)}(X, X ∖ T), by `hT` through `unionComplIso` below, which is the identity on points and so carries no sign.
4. Normalization on the singular side. Upstream's normalization iso N_T sends γ to the sheafified restriction to U_T = X ∖ T_sing of upstream's transport of γ (`normalization-singular`, Lean text below). Upstream's transport agrees with Φ_X after the pair isomorphisms (`transport_eq_flasqueModel`, `ofSubsetIsoNeighborhoodUniv` below).
5. Germs. At y ∈ T(ℂ), shrink to a chart neighborhood inside Z_reg ∩ W_reg (`hxreg`, `hwreg`, `htr`). There the restriction of Φ_X α_Z is `chartNormalProjectionCoclass` for the chart derived from φ (`cycle-class-germ`: upstream's section is glued from charts, `smoothClosedSupportCoclassStalk_eq_chartGerm`, and any two analytic charts agree, `exists_open_chartNormalProjectionCoclass_eq`); likewise for W and T. A named step inside `cycle-class-germ`: move the chart φ of Mathlib's maximal atlas on X(ℂ) into upstream's E × (Fin c → ℂ) chart form on the complex points of the open subscheme X ∖ Z_sing, the form `chartNormalProjectionCoclass` takes. When T is a point (both first cases), upstream's `cycleComponentSupportedInjectiveClass_point_normalization` and `analyticComponentPointSupportedInjectiveCoclass_relative` (`Other`) give upstream's transport of α_T as an explicit relative coclass on (X, X ∖ T), so `cycle-class-germ` is needed there only for Z and W, and the point form cross-checks it at T.
6. Local product. By naturality of relCup2 and `local-class-product`, the restriction of relCup2 (Φ_X α_Z) (Φ_X α_W) is the chart coclass of T. Off T both sections vanish. So N_T (Φ_X⁻¹ (relCup2 …)) is upstream's normalized section, and `cycleComponentSupportedInjectiveClass_unique` gives Φ_X⁻¹ (relCup2 …) = α_T.
7. Forget the support of T and use injectivity of Ψ (an equivalence): [Z] ∪ [W] = [T].

Route (decision 0010). The product of the two supported lifts is formed on the singular side, by `relCup2`. The checked general-V formula Φ_V (α ∪ β) = (−1)^{pq} relCupSing (Φ_V α) (β|_V) (`cup-comparison-supported-open`) cannot replace this: it has one supported factor, so α_Z ∪ [W] lands in H_Z, and in degree 2(a + b) > 2a no purity makes a lift from H_Z to H_T unique. Steps 4 and 5 use V-generality only through restriction to small opens: upstream's naturality (`supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, `sectionCohomologyToSheafSection_restriction`, the last two in `Other`) and the checked `supported-open-naturality`, `supported-model-agreement-open`; `flasqueModelOpen` and `cohomologyMap_inclusion_singClass` are optional aids for `cycle-class-germ`.

### Glue statements

`normalization-singular` (elaborated 2026-11-26 with `lake env lean` against `Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization`; the checked module imports `Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization`; scratch file inside the worktree, deleted):

```lean
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

theorem normalization_singular (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (a : CycleComponentSupportedCohomology X x p) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
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
              (cycleComponentAnalyticClosedSupport X x) (2 * p) a)))
```

Here X carries `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`. In words: N applied to a is the sheafification unit at U = X ∖ Z_sing applied to the restriction from (X, X ∖ Z) to (U, U ∖ Z) of upstream's transport of a at ⊤. The checked route is `cycleComponentSupportedClassNormalizationIso_apply`, `openRestrictedLowestSectionCohomologyIso_hom`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` at U ≤ ⊤, and naturality of the sheafification unit `supportRelativeCohomologyToSheaf` (red team, `docs/sketches/normalization-singular.redteam.md`).

Pair identifications, both the identity on points (elaborated 2026-11-26; the `_fst_apply` lemmas are the content a prover checks):

```lean
noncomputable def ofSubsetIsoNeighborhoodUniv {Y : Type} [TopologicalSpace Y] (S : Set Y) :
    TopPair.ofSubset (X := TopCat.of Y) (Sᶜ : Set Y) ≅
      neighborhoodSupportComplementPair (Set.univ : Set Y) S :=
  TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)

theorem ofSubsetIsoNeighborhoodUniv_fst_apply {Y : Type} [TopologicalSpace Y] (S : Set Y) (y : Y) :
    (TopPair.Hom.fst (ofSubsetIsoNeighborhoodUniv S).hom y).1 = y

noncomputable def unionComplIso {Y : Type} [TopologicalSpace Y] {Z W T : Set Y}
    (hT : T = Z ∩ W) :
    TopPair.ofSubset (X := TopCat.of Y) (Zᶜ ∪ Wᶜ) ≅ TopPair.ofSubset (X := TopCat.of Y) Tᶜ :=
  TopPair.isoOfSubset (Homeomorph.refl Y) (fun y => by subst hT; simp [Set.compl_inter])

theorem unionComplIso_fst_apply {Y : Type} [TopologicalSpace Y] {Z W T : Set Y}
    (hT : T = Z ∩ W) (y : Y) : TopPair.Hom.fst (unionComplIso hT).hom y = y
```

`ofSubsetIsoNeighborhoodUniv` belongs to `supported-pair-forget`; `unionComplIso` to `cycle-class-multiplicative` itself.

## What exists (checked by `grep` at the pin)

| Source | Declarations |
|---|---|
| Mathlib | `IsManifold.maximalAtlas`, `IsManifold.chart_mem_maximalAtlas`, `mem_chart_source`; for ℙ¹ × ℙ¹: `AlgebraicGeometry.GeometricallyIntegral` and its pullback instances, `smooth_isStableUnderBaseChange` |
| upstream statement library | `cycleComponentSheafClass`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportAmbientOpen`, `complexSupportInjectiveSectionCohomologyEquiv`, `supportRelativeCohomologyToSheaf`, `supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, `smoothClosedSupportCoclassStalk_eq_chartGerm`, `exists_open_chartNormalProjectionCoclass_eq`, `closedImmersionHolomorphicFlatteningChart`, `localChart` |
| upstream `Other` (built in the shared cache; outside upstream's statement guard, so listed for pins and drift) | `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply` (`Cohomology/SupportSheafNormalization.lean`), `cycleComponentSupportedInjectiveClass_unique` (`Cycle/FundamentalClass.lean`), `sectionCohomologyToSheafSection_restriction` (`Sheaf/CohomologySectionRestriction.lean`), `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` (`Cycle/Component/PointClassNormalization.lean`), `openRestrictedLowestSectionCohomologyIso_hom` (`Sheaf/OpenRestrictedLowestCohomology.lean`) and `complexSupportInjectiveCohomologySheafIsoRelative_section` (`Cohomology/SupportSheafNormalization.lean`), both used by the checked `normalization-singular` (its full `Other` closure, 28 declarations in 9 files, is listed in `docs/sketches/normalization-singular.redteam.md` section 8), `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` (`Hodge/CodimensionZeroComparison.lean`), `cycleComponentSheafClass_genericPoint_ne_zero` (`Hodge/CodimensionZeroNonvanishing.lean`) Added by `cycle-class-germ` (checked): `supportRelativeCohomologyGerm_eq_zero_iff`, `supportRelativeCohomologySheafOpenIso_unit_apply`, `supportRelativeCohomologySectionOnOpen_restrict`, `cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSmoothSupportCoclassSection_ne_zero`, `cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension`, `underlying_injective_of_locallyOfFiniteType`. |
| this repository | `HodgeLadder.Cup.cup`, `one`, `cup_singular_comparison`, `cup_gradedComm`, `supported_forget_compat`, `supportedEquivPair`, `transport_eq_flasqueModel`, `pullbackCoh`; for ℙ¹: `HodgeLadder.Tests.projectiveLine`, `infty`, `openOne`, `complInftyHomeomorph`; for ℙ²: `HodgeLadder.Tests.smoothOfRelativeDimension_toSpec` (any n) |

The `Other` declarations above, with those listed in `docs/sketches/local-class-product.md` section "Pins and drift", form the drift list for the next pin bump. `cycleComponentSupportedInjectiveClass_unique` is immediate from its definition (red team finding 1); pin it by `rfl` where it is first used.

## What is missing

The local sub-rungs (companion sketch). For ℙ¹ × ℙ¹ at the pin: no product of varieties anywhere upstream or here; no Segre embedding, so no `IsProjective` instance for the product; no homeomorphism (X ×_ℂ Y)(ℂ) ≅ X(ℂ) × Y(ℂ) and no product charts; no pullback of cycle classes along a flat map (for pr₁*[pt] = [{pt} × ℙ¹]); no nonvanishing of a point class in H⁴. For ℙ² (first, decision 0010): integrality from three standard charts, H³ of the complement of a point, the chart x₂ ≠ 0 in the maximal atlas, the smooth-locus fact for each line; no product, Segre embedding or pullback. The last three inputs are shared with ℙ¹ × ℙ¹.

## Sub-rungs

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `fundamental-class-unit` | [X] = `one X` in H⁰(X; ℚ) (statement elaborated: `cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) = (one X : H^(2 * 0)(X; ℚ))`) | Z = X(ℂ): degree-0 local class pairs to 1 with a point; Ψ of `one` is the constant cocycle | `supported-forget-compat`, `one-is-kappa`, `cycle-class-germ` |
| `normalization-singular` | N_T γ = sheafified restriction to U_T of upstream's transport of γ (Lean text above) | `cycleComponentSupportedClassNormalizationIso_apply`, `openRestrictedLowestSectionCohomologyIso_hom`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` at U ≤ ⊤, and naturality of the sheafification unit `supportRelativeCohomologyToSheaf` | checked |
| `cycle-class-germ` | near y ∈ Z_reg, the transported α_Z equals `chartNormalProjectionCoclass` for every analytic chart adapted to Z; includes the named chart step (maximal atlas on X(ℂ) to upstream's E × (Fin c → ℂ) form on X ∖ Z_sing) | step 5; checked (`HodgeLadder.Normalization.Germ`) | `normalization-singular`, `open-subscheme-chart-analytic` |
| `open-subscheme-chart-analytic` | a chart of the maximal analytic atlas of U(ℂ), lifted to X(ℂ), is in the maximal analytic atlas of X(ℂ) | `Point.evaluate_map`, `evaluate_openEquiv`; checked (`HodgeLadder.Normalization.ChartStep`) | |
| `analytic-smooth-locus` | under a holomorphic chart adapted to Z, e.source ∩ Z lies in X ∖ Z_sing; removes `hyU` from `cycle-class-germ` | completion of the analytic and algebraic local rings of the reduced closure; not at the pin | `cycle-class-germ` |
| `cycle-class-germ-point` | `cycle-class-germ` at a closed point and the chart of `adaptedChart_closedPoint`, cross-checked against upstream's point normalization | `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative` (`Other`) | `cycle-class-germ` |
| `supported-pair-forget` | on (X, X ∖ Z): forgetRel ∘ `supportedEquivPair` = Ψ ∘ `forgetSupport`, and `supportedEquivPair` = upstream's transport after the pair isomorphisms (`ofSubsetIsoNeighborhoodUniv`), no sign | `supported_forget_compat`, `transport_eq_flasqueModel`, `topPairIso` | `supported-forget-compat`, `supported-model-agreement`, `cup-comparison-supported-pair` |
| `cycle-class-multiplicative` | the theorem above | steps 1 to 7 | `local-class-product`, `triad-relative-cup`, `triad-relative-cup-naturality`, `normalization-singular`, `cycle-class-germ`, `supported-pair-forget`, `cup-singular-comparison-absolute`, `cup-singular-comparison`, `supported-model-agreement`, `supported-forget-compat`, `supported-open-naturality`, `supported-model-agreement-open` |
| `cycle-class-multiplicative-codim-zero` | x = w = t = the generic point, a = b = 0 meet the hypotheses on every X, so [X] ∪ [X] = [X] | S5 for `hT`, `htr`; the missing lemma `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤` for `hxreg` | `cycle-class-multiplicative` |
| `affine-chart-analytic` | an open U ≅ 𝔸^d over Spec ℂ gives a chart of X(ℂ) in Mathlib's maximal analytic atlas, compatible with upstream's `localChart` | transition maps between algebraic and étale coordinates are regular, hence holomorphic | |
| `p2-witness` | ℙ² is integral, smooth of relative dimension two, projective | `smoothOfRelativeDimension_toSpec`; irreducibility from three charts | `projective-line-witness` |
| `p2-lines-transversal` | L₀, L₁, [0 : 0 : 1] have coheight 1, 1, 2, meet as required, the chart x₂ ≠ 0 satisfies `htr`, and the point is in the smooth locus of each line (`hxreg`, `hwreg`) | the chart x₂ ≠ 0 is 𝔸² with coordinates x₀/x₂, x₁/x₂; `cycleComponentι` of each line on that chart is a coordinate line | `p2-witness`, `affine-chart-analytic` |
| `p2-point-class-nonzero` | [[0 : 0 : 1]] ≠ 0 in H⁴(ℙ²; ℚ) | `forget-support-exact` with H³ of the complement zero | `p2-lines-transversal`, `forget-support-exact` |
| `cycle-class-multiplicative-p2` | [L₀] ∪ [L₁] = [[0 : 0 : 1]] on ℙ² | instance of the theorem; T a point (upstream's point normalization) | `cycle-class-multiplicative`, `p2-lines-transversal` |
| `cup-positive-degree-test-p2` | [L₀] ∪ [L₁] ≠ 0 in H⁴(ℙ²; ℚ) | the two rungs above | `cycle-class-multiplicative-p2`, `p2-point-class-nonzero` |
| `complex-points-prod` | Point ℂ (X ⨯ Y) ≃ₜ Point ℂ X × Point ℂ Y over Spec ℂ, with product charts in the maximal atlas | universal property; affine charts Hom(A ⊗ B, ℂ) | |
| `p1p1-witness` | ℙ¹ ×_ℂ ℙ¹ in `Over (Spec ℂ)` is integral, smooth of relative dimension 2, projective (Segre) | Mathlib base change; Segre closed immersion into ℙ³ | `projective-line-witness` |
| `p1p1-fibres-transversal` | {∞} × ℙ¹, ℙ¹ × {∞}, (∞, ∞) have coheight 1, 1, 2, the supports meet as required, the product chart of `openOne` satisfies `htr` (in the maximal atlas by `affine-chart-analytic`), and (∞, ∞) is in the smooth locus of each fibre (`hxreg`, `hwreg`) | product of the ℙ¹ chart; `cycleComponentι` computed on it | `p1p1-witness`, `complex-points-prod`, `projective-line-point`, `affine-chart-analytic` |
| `cycle-class-multiplicative-p1p1` | [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)] on ℙ¹ × ℙ¹ | instance of the theorem | `cycle-class-multiplicative`, `p1p1-fibres-transversal` |
| `supported-class-pullback` | pullback H^n_S(X; ℚ) → H^n_{f⁻¹ S}(Y; ℚ), compatible with `forgetSupport` and `pullbackCoh f` | the port's inverse image, as in `cup-pullback` | `cup-pullback` |
| `supported-pullback-transport` | through upstream's transport the supported pullback is `relativeCohomologyMap` along f, no sign | naturality of the transport in X | `supported-class-pullback`, `supported-pair-forget` |
| `local-class-pullback-submersion` | `chartNormalProjectionCoclass` of Z pulls back along a submersion in charts to that of the preimage | chart-level naturality | |
| `fibre-class-pullback` (foundation) | `pullbackCoh f [Z] = [f⁻¹ Z]` for f smooth and f⁻¹ Z integral of the same codimension; first use `pullbackCoh pr₁ [∞] = [{∞} × ℙ¹]`, applied in `cup-positive-degree-test` | the three rungs above and uniqueness (`cycleComponentSupportedInjectiveClass_unique`); [`Fulton1998` ch. 19; numbering unverified] | `supported-class-pullback`, `supported-pullback-transport`, `local-class-pullback-submersion`, `cycle-class-germ` |
| `p1p1-point-class-nonzero` | [(∞, ∞)] ≠ 0 in H⁴(ℙ¹ × ℙ¹; ℚ) | `forget-support-exact` with H³ of the complement zero | `p1p1-fibres-transversal`, `forget-support-exact` |

`cup-positive-degree-test-p2` follows from `cycle-class-multiplicative-p2` and `p2-point-class-nonzero`, and comes first (decision 0010). `cup-positive-degree-test` then follows from `cycle-class-multiplicative-p1p1`, `fibre-class-pullback` and `p1p1-point-class-nonzero`.

## Kill criterion and smallest falsification test

The front closes (decisions 0009, 0010) if `cycle-class-multiplicative` fails on upstream definitions. Concretely: if `local-class-cross-model` evaluates to a value other than 1, or `fundamental-class-unit` fails, and the discrepancy is traced to upstream's normalization after the ladder's own definitions (`relCup2`, the cap and cup order) are ruled out, the failing rung is marked `refuted` with the computed value, and its statement is left as it is. Work on a corrected normalization continues as a new rung under a new decision record; the refuted rung stays refuted. A computed −1 would mean [Z] ∪ [W] = −[T] for a, b ≥ 1 at the pin.

Smallest tests, in order: (1) `fundamental-class-unit`, the codimension-zero case: since [X] ≠ 0 upstream and H⁰ is a field for connected X, [X] ∪ [X] = [X] holds only if [X] = 1; `cycle-class-multiplicative-codim-zero` shows that the theorem's hypotheses can be met there. (2) `local-class-cross-model` at a = b = 1, the first sign-visible case, on ℂ² with no variety. (3) `cycle-class-multiplicative-p2` with `cup-positive-degree-test-p2`. (4) `cycle-class-multiplicative-p1p1`.

## Risks

1. `cross-orientation` and `real-affine-orientation` are the largest pieces: explicit shuffle simplices and a GL⁺ path that Mathlib lacks.
2. Upstream's triad and cap files are in library `Other`, unbuilt in the shared cache; first import builds them, and upstream does not guard them as statements of record. Build them once, from one worktree, before parallel work starts; pin them by `rfl` and keep them on the drift list (`docs/sketches/local-class-product.md`, "Pins and drift").
3. Pair spellings: (⊤, ⊤ ⊓ (X ∖ Z)), `TopPair.ofSubset`, `neighborhoodSupportComplementPair`; all identifications are identity on points, and each must be shown sign-free.
4. `hxreg`, `hwreg` may be implied by `htr` mathematically; the implication is not at the pin.

## Red-team changes (2026-11-26), as implemented

Verdict `docs/sketches/cycle-class-multiplicative.redteam.md`, pass with changes; the maintainer approved both open decisions as recommended.

| Change | Where it is now |
|---|---|
| A: singular-side two-support route; general-V formula off the critical path; kill-criterion wording | decision 0010; "Route" paragraph; "Kill criterion"; 0009 Consequences points to 0010 |
| B: Lean text of `normalization-singular` and the pair identifications | "Glue statements" |
| C: title of `cycle-class-multiplicative` without "first case: ℙ¹ × ℙ¹" | ledger, roadmap |
| D: `cycle-class-multiplicative-codim-zero`, `affine-chart-analytic`; smooth-locus and atlas items in `p1p1-fibres-transversal` | sub-rungs table, ledger, roadmap |
| E: `fibre-class-pullback` a foundation with sub-rungs `supported-class-pullback`, `supported-pullback-transport`, `local-class-pullback-submersion` | sub-rungs table, ledger, roadmap |
| F: upstream's point-class normalization for T | proof idea, step 5; "What exists"; note of `cycle-class-multiplicative-p2` |
| G: ℙ² first: `p2-witness`, `p2-lines-transversal`, `p2-point-class-nonzero`, `cycle-class-multiplicative-p2`, `cup-positive-degree-test-p2`; ℙ¹ × ℙ¹ kept, after | decision 0010, sub-rungs table, ledger, roadmap |
| H: `Other` declarations marked; pins and drift; build `Other` once | "What exists", "Risks" 2, companion sketch "Pins and drift" |
| I: hand computations as Lean lemmas inside named rungs | companion sketch and the ledger notes it lists |

## cycle-class-germ: statement

Date: 2026-11-26. Statement elaborated first with `sorry` bodies, red-teamed (`docs/sketches/cycle-class-germ.redteam.md`, pass with changes, none to the statements), then proved. Both statements are checked: the rung in module `HodgeLadder.Normalization.Germ` and the chart step, rung `open-subscheme-chart-analytic`, in module `HodgeLadder.Normalization.ChartStep`; both are imported from `HodgeLadder.lean`. Imports of `Germ`: `HodgeLadder.Normalization.Singular`, `HodgeLadder.Normalization.ChartStep`, `Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing`, `Other.AlgebraicGeometry.Cycle.Component.PointBoundary`, `Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion` and two Mathlib modules, all built in the shared cache.

Notation. X carries `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`; `x : X.left`, `hx : Order.coheight x = p`; Z = `cycleComponentAnalyticClosedSupport X x`; U = `cycleComponentSmoothSupportAmbientOpen X x` (X(ℂ) ∖ Z_sing(ℂ)); T α = `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2 * p) (rationalSupportAddEquivSupportedInjectiveHomology X Z (2 * p) α)`, upstream's transport at ⊤, the form `normalization_singular` uses; [Z] = `cycleComponentSupportedInjectiveClass X x hx`; d = `dim X.left`, the model dimension of upstream's charted space (instance `SmoothOfRelativeDimension.of_isIntegral`).

### The rung

```lean
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
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS W hW
```

| Hypothesis | Meaning | Why it is the literature's |
|---|---|---|
| `e`, `E` | a chart of X(ℂ) into E × ℂ^p, tangential factor E, normal factor ℂ^p | upstream's chart form for `chartNormalProjectionCoclass` and `exists_open_chartNormalProjectionCoclass_eq` |
| `L`, `he` | e is holomorphic: after some ℂ-linear identification E × ℂ^p ≃ ℂ^d it lies in Mathlib's maximal analytic atlas of X(ℂ) (upstream's `localChart` structure) | "local holomorphic coordinates"; any L works, since ℂ-linear maps are biholomorphic; `L` forces E finite-dimensional of dimension d − p |
| `hS` | on e.source, Z is the zero set of the normal coordinate | "adapted to Z"; the same predicate as upstream's `hS` |
| `hy`, `hyU` | y in the chart and off Z_sing | Z_reg; `hyU` is stated because analytic smoothness of Z at y does not give y ∉ Z_sing at the pin (as `hxreg` in the main statement) |

Conclusion: near y, the restriction of T [Z] from (X, X ∖ Z) to (W, W ∖ Z) is the pullback along the normal projection of the class pairing to 1 with the complex orientation class of (ℂ^p, ℂ^p ∖ 0) [`Fulton1998` ch. 19, `Iversen1986`; numbering unverified]. It is an equality in H^{2p}(W, W ∖ Z; ℚ): exact, no sign, no scalar, for every holomorphic adapted chart. y ∈ Z is not assumed; for y ∉ Z both sides vanish on a W missing Z, so the statement covers that case too. The existential W is equivalent to equality of the two germs in the stalk at y, through upstream's `supportRelativeCohomologyGerm_eq_zero_iff`; both sides restrict compatibly (`chartNormalProjectionCoclass_restrict`), so the identity holds on every smaller open around y.

Trivial proofs fail (scratch, deleted): `⟨⟨e.source, e.open_source⟩, subset_rfl, hy, rfl⟩`, the same with `Subsingleton.elim _ _`, and with `by simp` (unsolved goal).

### The chart step (finding 15), rung `open-subscheme-chart-analytic`, checked

```lean
theorem lift_mem_maximalAtlas_openScheme (X : Over (Spec ↧ℂ)) {d : ℕ}
    [SmoothOfRelativeDimension d X.hom] (U : X.left.Opens)
    [SmoothOfRelativeDimension d (openScheme X U).hom]
    {ψ : OpenPartialHomeomorph (ComplexPoint (openScheme X U)) (Fin d → ℂ)}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint (openScheme X U))) :
    ψ.lift_openEmbedding (isOpenEmbedding_map_open X U) ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)
```

In words: the inclusion of an open subscheme is a biholomorphism onto its image for upstream's complex structures, whose étale charts on U(ℂ) and on X(ℂ) are chosen independently with `Classical.choice`. No upstream file mentions `maximalAtlas` (grep at the pin). The second instance argument holds for every X and U (`smoothOfRelativeDimension_comp 0 d U.ι X.hom`); it is an argument so the file adds no instance. Its instance at X ∖ Z_sing, `lift_mem_maximalAtlas_smoothSupportAmbient`, is proved from it in one line, along upstream's `cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding`, with upstream's dimension instance on `cycleComponentSmoothLocusAmbientOpenOver`. `aesop`, `simp` and `exact hψ` fail on it.

It is its own rung, `open-subscheme-chart-analytic` (kind foundation, no dependencies), and `cycle-class-germ` depends on it. Proof (module `HodgeLadder.Normalization.ChartStep`): the inclusion ι is holomorphic, because a section of X evaluated at ι q is its pullback evaluated at q (upstream `Point.evaluate_map`); its local inverse is holomorphic, because a section of U is a section of X over the image open (upstream `evaluate_openEquiv`); upstream's `analyticAt_localChart_symm_evaluate` makes both evaluations analytic. Mathlib's `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn` concludes. The "missing input" named by the coordinator, `Point.evaluate` against the open immersion, was at the pin in these two upstream lemmas.

### Helpers, proved (change E of the red team on `normalization-singular`; changes B and F of the red team on `cycle-class-germ`)

| Declaration | Statement | Proof |
|---|---|---|
| `normalization_supportedInjectiveClass_ne_zero` | `(cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom (cycleComponentSupportedInjectiveClass X x hx) ≠ 0`, every x | upstream `cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSmoothSupportCoclassSection_ne_zero` (`Other`), 3 lines |
| `normalization_genericPoint_ne_zero` | the same at `genericPoint X.left`, `coheight_genericPoint_eq_zero X` (the case change E names) | instance of the above |
| `coclassSection_eq_singular` | `cycleComponentSmoothSupportCoclassSection X x hx` equals the right side of `normalization_singular` at a = [Z] | `(cycleComponentSupportedInjectiveClass_normalization X x hx).symm.trans (normalization_singular X x hx _)`, no `rw` |
| `toSheaf_transport_supportedClass_ne_zero` | that singular-form section is nonzero, every x | the two above |
| `adaptedChart_genericPoint` | at p = 0 and every y ∈ X(ℂ), e = `chartAt y` followed by the inverse of `ContinuousLinearEquiv.prodUnique ℂ (Fin d → ℂ) (Fin 0 → ℂ)` meets `he`, `hS`, `hy` | `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`, 15 lines |
| `adaptedChart_closedPoint` | at every y₀ ∈ X(ℂ), with x the closed point under y₀ (p = dim X) and e = `chartAt y₀` translated to 0 followed by the inverse of `ContinuousLinearEquiv.uniqueProd`, all four hypotheses `he`, `hS`, `hy`, `hyU` hold | red team RT2 text; `translate_mem`, `trans_mem_maximalAtlas` (in `ChartStep`), upstream `cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension` (`Other`) |
| `chartNormalProjectionCoclass_germ_ne_zero` | at y ∈ e.source with (e y).2 = 0, the germ of the chart coclass is nonzero | red team RT7 text; `supportRelativeCohomologyGerm_eq_zero_iff` (`Other`), `chartNormalProjectionCoclass_apply_normalClass` |

All seven check with the standard axioms. Non-vacuity of the rung's hypotheses (finding 4 of the red team): all four are met at the pin in positive codimension, on every X and at every complex point, by `adaptedChart_closedPoint` (p = dim X, Z the point), without `affine-chart-analytic`. At the generic point `adaptedChart_genericPoint` meets `he`, `hS`, `hy`; `hyU` there needs `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`, the lemma assigned to `cycle-class-multiplicative-codim-zero`. With `chartNormalProjectionCoclass_germ_ne_zero` the conclusion is a nonzero identity in positive codimension.

### The proof, as checked

1. `exists_restrict_eq_of_germ_eq`: equal germs at y of two relative classes give equal restrictions on an open W ∋ y (red team RT3; from `supportRelativeCohomologyGerm_eq_zero_iff`, `Other`, applied to the difference). The rung reduces to equality of germs at y; for y ∉ Z both vanish (`supportRelativeCohomologyGerm_eq_zero_of_not_mem`).
2. For y ∈ Z: the germ of T [Z] is the germ of upstream's coclass section, by `supportRelativeCohomologyGerm_restrict` and `coclassSection_eq_singular` composed with `congrArg`, no `rw` on N.
3. `germ_coclassSection_eq` removes the degree cast `dim X − (dim X − p) = p` of `cycleComponentSmoothClosedLiftCoclassSection` by `subst` on a statement generalized over the degree, then calls `germ_smoothSupportSection_eq`.
4. `germ_smoothSupportSection_eq`: y = ι y' with y' = i z₀ on Z_reg. The germ of upstream's glued section at y' is the flattening-chart germ (`smoothClosedSupportCoclassSection_germ`, `smoothClosedSupportCoclassStalk_eq_chartGerm`), so on a small O'' ∋ y' the section is the sheafified flattening-chart coclass (`germ_eq`). `supportRelativeCohomologySectionOnOpen_restrict` and `supportRelativeCohomologySheafOpenIso_unit_apply` (`Other`) move it to X(ℂ) as the pullback along `neighborhoodSupportPairImageIso`, which is the coclass of the lifted chart (`chartNormalProjectionCoclass_pairImage`, an equality of pair maps checked on points).
5. Chart comparison: the tangential factor of e is matched to ℂ^{m} by `ContinuousLinearEquiv.ofFinrankEq` (E is finite-dimensional of dimension m through L); the normal coordinate is unchanged, so the coclass is unchanged by definition. `analyticAt_transition_of_factor` gives analyticity of the transition and of its inverse at y from `he`, the chart step applied to `localChart` of X ∖ Z_sing, and the bi-analytic coordinate change inside upstream's flattening chart (`biAnalyticRestrict_mem_source_iff`). Then `exists_open_chartNormalProjectionCoclass_eq` and `chartNormalProjectionCoclass_restrict`.

Timing: `lake env lean HodgeLadder/Normalization/Germ.lean` 33 s wall (4 s imports), `ChartStep.lean` 5 s; default heartbeats throughout.

Downstream use. `cycle-class-multiplicative`'s `htr` gives φ in the maximal atlas with Z = {first a coordinates = 0}; take E = ℂ^{d−a}, e = φ followed by the inverse of a coordinate splitting L, and `he` by `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`, as in `adaptedChart_genericPoint`. That statement binds `{d} [SmoothOfRelativeDimension d X.hom]` where this rung uses `dim X.left`; the two connect by `obtain rfl := SmoothOfRelativeDimension.dim_eq (f := X.hom) d` (red team RT5, change I, not applied to the statement of `cycle-class-multiplicative`).

## Sources

`Fulton1998` ch. 7–8, 19 (numbering unverified), `Hatcher2002` §3.2, `Iversen1986` and `Bredon1997` (supports and products; unverified), `MilnorStasheff1974` (unverified). Upstream declarations by name, read at `2ead713`.
