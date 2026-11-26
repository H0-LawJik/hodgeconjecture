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

`normalization-singular` (elaborated 2026-11-26 with `lake env lean` against `Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization`, scratch file inside the worktree, deleted):

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

Here X carries `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`. In words: N applied to a is the sheafification unit at U = X ∖ Z_sing applied to the restriction from (X, X ∖ Z) to (U, U ∖ Z) of upstream's transport of a at ⊤. The route is `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply` and upstream's naturality in V.

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
| upstream `Other` (built in the shared cache; outside upstream's statement guard, so listed for pins and drift) | `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply` (`Cohomology/SupportSheafNormalization.lean`), `cycleComponentSupportedInjectiveClass_unique` (`Cycle/FundamentalClass.lean`), `sectionCohomologyToSheafSection_restriction` (`Sheaf/CohomologySectionRestriction.lean`), `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` (`Cycle/Component/PointClassNormalization.lean`), `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top` (`Hodge/CodimensionZeroComparison.lean`), `cycleComponentSheafClass_genericPoint_ne_zero` (`Hodge/CodimensionZeroNonvanishing.lean`) |
| this repository | `HodgeLadder.Cup.cup`, `one`, `cup_singular_comparison`, `cup_gradedComm`, `supported_forget_compat`, `supportedEquivPair`, `transport_eq_flasqueModel`, `pullbackCoh`; for ℙ¹: `HodgeLadder.Tests.projectiveLine`, `infty`, `openOne`, `complInftyHomeomorph`; for ℙ²: `HodgeLadder.Tests.smoothOfRelativeDimension_toSpec` (any n) |

The `Other` declarations above, with those listed in `docs/sketches/local-class-product.md` section "Pins and drift", form the drift list for the next pin bump. `cycleComponentSupportedInjectiveClass_unique` is immediate from its definition (red team finding 1); pin it by `rfl` where it is first used.

## What is missing

The local sub-rungs (companion sketch). For ℙ¹ × ℙ¹ at the pin: no product of varieties anywhere upstream or here; no Segre embedding, so no `IsProjective` instance for the product; no homeomorphism (X ×_ℂ Y)(ℂ) ≅ X(ℂ) × Y(ℂ) and no product charts; no pullback of cycle classes along a flat map (for pr₁*[pt] = [{pt} × ℙ¹]); no nonvanishing of a point class in H⁴. For ℙ² (first, decision 0010): integrality from three standard charts, H³ of the complement of a point, the chart x₂ ≠ 0 in the maximal atlas, the smooth-locus fact for each line; no product, Segre embedding or pullback. The last three inputs are shared with ℙ¹ × ℙ¹.

## Sub-rungs

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `fundamental-class-unit` | [X] = `one X` in H⁰(X; ℚ) (statement elaborated: `cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) = (one X : H^(2 * 0)(X; ℚ))`) | Z = X(ℂ): degree-0 local class pairs to 1 with a point; Ψ of `one` is the constant cocycle | `supported-forget-compat`, `one-is-kappa`, `cycle-class-germ` |
| `normalization-singular` | N_T γ = sheafified restriction to U_T of upstream's transport of γ (Lean text above) | `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply`, upstream naturality in V | |
| `cycle-class-germ` | near y ∈ Z_reg, the transported α_Z equals `chartNormalProjectionCoclass` for every analytic chart adapted to Z; includes the named chart step (maximal atlas on X(ℂ) to upstream's E × (Fin c → ℂ) form on X ∖ Z_sing) | step 5 | `normalization-singular` |
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

## Sources

`Fulton1998` ch. 7–8, 19 (numbering unverified), `Hatcher2002` §3.2, `Iversen1986` and `Bredon1997` (supports and products; unverified), `MilnorStasheff1974` (unverified). Upstream declarations by name, read at `2ead713`.
