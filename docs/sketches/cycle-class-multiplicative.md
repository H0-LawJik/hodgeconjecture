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
4. Normalization on the singular side. Upstream's normalization iso N_T sends γ to the sheafified restriction to U_T = X ∖ T_sing of upstream's transport of γ (`normalization-singular`, Lean text below). Upstream's transport agrees with Φ_X after the pair isomorphisms (`transport_eq_flasqueModel`; `supportedEquivPair_eq_transport` with `ofSubsetIsoNeighborhoodTop`, rung `supported-pair-forget`, checked).
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

`ofSubsetIsoNeighborhoodUniv` belongs to `supported-pair-forget`, which states (b) with its `Closeds` form `ofSubsetIsoNeighborhoodTop`; `unionComplIso` belongs to `cycle-class-multiplicative` itself, to be stated on `Closeds` in the `Z.compl` spelling (section "supported-pair-forget: statement", change D).

**Step 6 glue** (red team on `triad-relative-cup-naturality`, changes 2 and 3, 2026-11-26). Step 6 restricts `relCup2 (Φ_X α_Z) (Φ_X α_W)` to a chart neighbourhood by the checked `HodgeLadder.Cup.relCup2_restrict` (module `HodgeLadder.Cup.TriadCupNaturality`). This rung adds the four declarations below; they compile against the checked module together with `HodgeLadder.Cup.SupportedPairForget` and upstream's `NormalProjectionCoclass` definitions (about 4 s). The first moved here from `triad-relative-cup-naturality`, so that the triad module does not import the supported stack. The `unionComplIso` below, in `Closeds` form, supersedes the `Set` form above.

```lean
theorem neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv
    {Y : Type} [TopologicalSpace Y] (V : Set Y) (Z : Closeds Y) :
    neighborhoodSupportInclusionPairMap (W := V) (V := ((⊤ : Opens Y) : Set Y))
        (fun _ _ => trivial) (Z : Set Y) ≫ (ofSubsetIsoNeighborhoodTop Z).inv =
      restrictToNeighborhood V Z := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl

noncomputable def unionComplIso {Y : Type} [TopologicalSpace Y] {Z W T : Closeds Y}
    (hT : T = Z ⊓ W) :
    TopPair.ofSubset (X := TopCat.of Y) ((Z.compl : Set Y) ∪ (W.compl : Set Y)) ≅
      TopPair.ofSubset (X := TopCat.of Y) (T.compl : Set Y) :=
  TopPair.isoOfSubset (Homeomorph.refl Y) (fun y => by subst hT; simp [Closeds.compl]; tauto)

theorem mem_iff_of_eq_inf {Y : Type} [TopologicalSpace Y] (V : Set Y) {Z W T : Closeds Y}
    (hT : T = Z ⊓ W) :
    ∀ y ∈ V, y ∈ (T : Set Y) ↔ y ∈ (Z : Set Y) ∧ y ∈ (W : Set Y) := by
  subst hT; exact fun _ _ => Iff.rfl

theorem unionComplIso_restrict {Y : Type} [TopologicalSpace Y] (V : Set Y)
    {Z W T : Closeds Y} (hT : T = Z ⊓ W) :
    restrictToNeighborhood V T ≫ (unionComplIso hT).inv =
      (HodgeLadder.LocalClassProduct.chartUnionIso V (mem_iff_of_eq_inf V hT)).inv ≫
        TopPair.ofSubsetHom (subsetInclusion V)
          (HodgeLadder.Relative.triadMap_mem_union (subsetInclusion V)
            (mem_compl_of_neighborhood V Z) (mem_compl_of_neighborhood V W)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext <;> rfl
```

**`chartUnionIso` in place of `unionComplIsoNeighborhood`** (red team of `local-class-product`, change C4, 2026-11-26). The pair isomorphism (V; V ∖ Z ∪ V ∖ W) ≅ `neighborhoodSupportComplementPair V T` is now the checked `HodgeLadder.LocalClassProduct.chartUnionIso V h` (identity of V), the map in the conclusion of `relCup2_chartNormalProjectionCoclass` and of its `inv` form `chartNormalProjectionCoclass_eq_relCup2`; `mem_iff_of_eq_inf` turns `hT : T = Z ⊓ W` into its argument h. The earlier definition `unionComplIsoNeighborhood V hT` (`isoOfSubset (Homeomorph.refl V)` with its own membership proof) is the same term: `unionComplIsoNeighborhood V hT = chartUnionIso V h` holds by `rfl` for every h (red-team scratch RT1 B, rechecked). The three declarations above and that `rfl` bridge compile against `HodgeLadder.Local.ClassProduct` and `HodgeLadder.Cup.SupportedPairForget` (scratch, deleted). Step 6 then ends with `chartNormalProjectionCoclass_eq_relCup2`, whose `h` argument takes `mem_iff_of_eq_inf V hT`.

**Point-form seam** (same red team, section 6). When T is a point, step 5 may read the class of T from upstream's point form (`cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`) in place of `cycle-class-germ`. That class must then be matched with `chartNormalProjectionCoclass ET (a + b) eT T _` for the chart eT built from φ. The match is an orientation step: two holomorphic adapted charts give the same coclass (upstream `exists_open_chartNormalProjectionCoclass_eq`), and the point coclass is the chart coclass of the translated `chartAt` (checked as `pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass`, rung `cycle-class-germ-point`). It belongs to this rung, and its sign is the one to watch: `local-class-product` fixes the sign of the product only against the chart coclass of eT.

With these, step 6 closes from `relCup2_restrict` in two lines (red-team scratch RT3): `rw [compat, compat, compat]` with the first lemma, then `rw [← relCup2_restrict, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, unionComplIso_restrict]`. Type the classes on `Z.compl`, the codomain of `supportedEquivPair`. A class typed on `TopPair.ofSubset ((Z : Set Y)ᶜ)` still elaborates, but `rw [relCup2_restrict]` then fails to find its pattern (conventions row "Pair spellings of (X, X ∖ Z)").

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
| `supported-pair-forget` | on (X, X ∖ Z): forgetRel ∘ `supportedEquivPair` = Ψ ∘ `forgetSupport`, and `supportedEquivPair` = upstream's transport after the pair isomorphisms (`ofSubsetIsoNeighborhoodTop`), no sign | checked (`HodgeLadder.Cup.SupportedPairForget`); `supported_forget_compat`, `transport_eq_flasqueModel`, `topPairIso` | `supported-forget-compat`, `supported-model-agreement`, `cup-comparison-supported-pair` |
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
| `p1p1-fibres-transversal` | {∞} × ℙ¹, ℙ¹ × {∞}, (∞, ∞) have coheight 1, 1, 2, the supports meet as required, the product of the chart x₀ ≠ 0 of ℙ¹ with itself satisfies `htr` (in the maximal atlas by `prodChart_mem_maximalAtlas` and `affine-chart-analytic-p2`; the chart `openOne` misses ∞), and (∞, ∞) is in the smooth locus of each fibre (`hxreg`, `hwreg`) | product of the ℙ¹ chart; `cycleComponentι` computed on it | `p1p1-witness`, `complex-points-prod`, `projective-line-point`, `affine-chart-analytic` |
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

## p2-witness: statement

Rung `p2-witness`, checked 2026-11-26. The statements were fixed first and passed a statement red team with changes (`docs/sketches/p2-witness.redteam.md`); the changes are implemented. File `HodgeLadder/Tests/ProjectivePlane.lean`, module `HodgeLadder.Tests.ProjectivePlane`, next to the ℙ¹ witness, imported from `HodgeLadder.lean`.

### Choice: every ℙⁿ, with ℙ² as an abbreviation

The ℙ¹ proof generalizes to `Fin (n + 1)` with no new input, so the instances are stated for every n and `projective-space-test` can use them at any n. The plane is a separate abbreviation spelled with `Fin 3`, as in the rung title; `projectivePlane_eq : projectivePlane = projectiveSpace 2` is `rfl`, and instance search finds the general instances on `projectivePlane` by unifying `Fin 3` with `Fin (?n + 1)`.

### The statements

| Declaration | Statement | Status |
|---|---|---|
| `projectiveSpace n` | `Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))`, an abbreviation | definition |
| `projectivePlane` | `Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))`, an abbreviation | definition |
| `smooth_terminal_space n` | `SmoothOfRelativeDimension n (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift ℤ))))` | proved |
| instance `smoothOfRelativeDimension_projectiveSpace n` | `SmoothOfRelativeDimension n (projectiveSpace n).hom` | proved |
| instance `smooth_projectiveSpace n` | `Smooth (projectiveSpace n).hom` | proved |
| instance `isProjective_projectiveSpace n` | `IsProjective (projectiveSpace n).hom`, the identity presentation of dimension n | proved |
| `isPullback_projectiveSpace n`, `okaIsoSpace n` | Oka's `ℙₒ(n; ℂ)` is the pullback defining upstream's object; the iso `ℙₒ(n; ℂ) ≅ (projectiveSpace n).left` | proved |
| `okaIsoSpace_hom_toBase n`, `okaIsoSpace_hom_snd n` | `okaIsoSpace` lies over `Spec ℂ`; its second projection is Oka's coefficient change `ProjectiveSpace.map intToComplex` (red team finding 3, for moving L₀, L₁ and the chart x₂ ≠ 0 to upstream's side) | proved |
| `irreducibleSpace_of_cover` | an irreducible open `U` and a cover by irreducible sets each meeting `U` give an irreducible space | proved |
| instance `isIntegral_okaProjectiveSpace n` | `IsIntegral ℙₒ(n; ℂ)` | proved (route below) |
| instance `isIntegral_projectiveSpace n` | `IsIntegral (projectiveSpace n).left` | proved (route below) |
| `dim_projectiveSpace n` | `TopologicalSpace.dim (projectiveSpace n).left = n` | proved from the instances, by upstream's `SmoothOfRelativeDimension.dim_eq` |
| `relativeDimension_projectiveSpace_eq n d` | `[SmoothOfRelativeDimension d (projectiveSpace n).hom] : d = n` (red team finding 4) | proved |
| `projectivePlane_witness` | `IsIntegral projectivePlane.left ∧ SmoothOfRelativeDimension 2 projectivePlane.hom ∧ Smooth projectivePlane.hom ∧ IsProjective projectivePlane.hom` | `inferInstance` four times |
| `projectivePlane_t2Space` | `T2Space (ComplexPoint projectivePlane)` | `inferInstance` (upstream) |
| `projectivePlane_openParacompactSpace` | `∀ U : Opens (ComplexPoint projectivePlane), ParacompactSpace U` | upstream's `ComplexPoint.openParacompactSpace`; a theorem, to be installed as a local instance as in the ℙ¹ cup comparison |

These are the instance forms the statements of record and `cycle-class-multiplicative-p2` bind: `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`, `{d} [SmoothOfRelativeDimension d X.hom]` with d = 2, and the cup comparison's `T2Space` and paracompact opens.

### What instance search finds without the file

With only the ℙ¹ witness and upstream's Hausdorff file imported, `inferInstance` on `Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))` fails for `IsIntegral _.left`, `Smooth _.hom`, `SmoothOfRelativeDimension 2 _.hom`, `IsProjective _.hom` and `Nonempty _.left`, and succeeds for `T2Space (ComplexPoint _)` through upstream's `instT2SpaceProjectiveSpaceComplexPoint` (stated for every `Fin (n + 1)`). The ℙ¹ instances are stated on `Fin 2` and do not fire at `Fin 3`.

### Route for integrality

1. `ℙₒ(n; ℂ)` is reduced: each chart of Oka's affine open cover is `Spec ℂ[Y₁, …, Yₙ]` (`IsReduced.of_openCover`).
2. Each standard open `U i` is irreducible, as the image of the irreducible `Spec ℂ[Y₁, …, Yₙ]` under the chart (`opensRange_chart`).
3. `U 0` meets every `U i`: the point of chart 0 with all homogeneous coordinates 1 lies in `U i` (`chart_base_evalPoint_mem_U_iff`).
4. A space with an irreducible open `U` and a cover by irreducible sets that each meet `U` is irreducible: every member lies in the closure of `U` (`subset_closure_inter_of_isPreirreducible_of_isOpen`), so that closure is the whole space. This replaces the two-chart lemma of the ℙ¹ witness, and the cover is `iSup_U`.
5. Integral from irreducible and reduced (`isIntegral_of_irreducibleSpace_of_isReduced`), then transport along `okaIsoSpace n` (`isIntegral_of_isOpenImmersion`), with `Nonempty` from the image of a point of `ℙₒ(n; ℂ)`.

Every declaration the ledger names checks with the standard axioms. One trap met on the way: while the `IsIntegral` instances were still `sorry`, a `Nonempty` argument was found through them, so the axioms of the transported proof were read with the sorried instances removed; the checked file supplies `Nonempty` explicitly.

Timing: `lake env lean HodgeLadder/Tests/ProjectivePlane.lean` 5 s wall; default heartbeats.
## supported-pair-forget: statement
Date: 2026-11-26. Statements elaborated first with `sorry` bodies, red-teamed (`docs/sketches/supported-pair-forget.redteam.md`, pass with changes A to E, all implemented), then proved. Checked: module `HodgeLadder.Cup.SupportedPairForget`, rung `supported-pair-forget`, and the non-vacuity tests in `HodgeLadder.Tests.SupportedPairForget`, rung `supported-pair-forget-test`; both imported from `HodgeLadder.lean`. The ledger entry first had `"module": null` and a `file` hint `HodgeLadder/Supported/Pair/Forget.lean`; the module is now `HodgeLadder.Cup.SupportedPairForget`, next to `SupportedPair` and `SupportedForgetFinal` (change E). Imports: `HodgeLadder.Cup.SupportedPair`, `HodgeLadder.Cup.SupportedForgetFinal`, `HodgeLadder.Cup.SupportedAgreement`. `lake env lean` on the module: 29 s wall; on the test module, 34 s.
Notation. X carries `[IsIntegral X.left] [Smooth X.hom]`; Z : `Closeds (ComplexPoint X)`; Φ = `supportedEquivPair X Z n`, landing in H^n(X, X ∖ Z; ℚ) for the pair `TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Z.compl : Set _)`, the pair of `triad-relative-cup`; Ψ = `rationalCohomologyAddEquivSingularCohomology X n`; T α = `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n (rationalSupportAddEquivSupportedInjectiveHomology X Z n α)`, upstream's transport at ⊤, the form `normalization_singular` and `cycle-class-germ` use.
### The two statements
```lean
theorem forgetRel_supportedEquivPair [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    forgetRel (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Z.compl : Set (ComplexPoint X)))
        n (supportedEquivPair X Z n α) =
      rationalCohomologyAddEquivSingularCohomology X n (forgetSupport ℚ X Z n α)
theorem supportedEquivPair_eq_transport [IsProjective X.hom]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X Z n α =
      relativeCohomologyMap ℚ n (ofSubsetIsoNeighborhoodTop Z).hom
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α))
```
In words: (a) forgetting the subspace after Φ is Ψ after forgetting the support, with Ψ read on X itself (the checked `supported_forget_compat` reads it on the open ⊤ through `singularCochainComplexIsoTopOpen`); (b) Φ is upstream's transport T, pulled back along the identity of points from (X, X ∖ Z) to upstream's (⊤, ⊤ ∖ Z). Both are exact, with no sign and no scalar. (b) needs `IsProjective` because upstream's transport does; the `T2Space` instance that Φ needs is then upstream's `IsProjective.complexPoint_t2Space`.
Spelling (change A). The statement first used `ofSubsetIsoNeighborhoodUniv (Z : Set _)`, whose domain `TopPair.ofSubset (↑Z)ᶜ` agrees with Φ's codomain `TopPair.ofSubset ↑Z.compl` only at default transparency (`Closeds.compl` is a plain `def`), so `rw` failed across it. `ofSubsetIsoNeighborhoodTop` spells its domain as Φ's codomain and its codomain as T's target, and plain `rw` works in the downstream tests. Row "Pair spellings of (X, X ∖ Z)" of `docs/conventions.md` records the four spellings.
Trivial proofs fail (scratch file inside the worktree, deleted): for each statement `rfl` (not definitionally equal), `simp` (unsolved goal), and the checked statement it moves (`exact supported_forget_compat X Z n α`, `exact transport_eq_flasqueModel X Z n α`: type mismatch).
### Helpers
| Declaration | Statement | Proof |
| `ofSubsetIsoNeighborhoodTop` | for Z : `Closeds Y`, `TopPair.ofSubset (Z.compl : Set Y) ≅ neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) Z` | `TopPair.isoOfSubset (Homeomorph.Set.univ Y).symm (fun _ => Iff.rfl)` (upstream `isoOfSubset`) |
| `ofSubsetIsoNeighborhoodTop_fst_apply` | `(TopPair.Hom.fst (ofSubsetIsoNeighborhoodTop Z).hom y).1 = y` | `rfl` |
| `ofSubsetIsoNeighborhoodTop_hom_comp_inv` | `(ofSubsetIsoNeighborhoodTop Z).hom ≫ (openIntersectionPairIsoSupportComplement (TopCat.of Y) Z Z.isClosed ⊤).inv = (topPairIso (TopCat.of Y) Z.compl).hom` | ext on both components, `rfl`: the three maps are the identity on points |
| `ofSubsetIsoNeighborhoodUniv`, `_fst_apply` | the same identity for S : `Set Y`, (Y, Y ∖ S) ≅ (univ, univ ∖ S), kept for consumers spelled with sets | as above |
| `relativeCohomologyMap_inv_hom_apply` | `relativeCohomologyMap ℚ n e.inv (relativeCohomologyMap ℚ n e.hom x) = x` for an iso of pairs e (change B) | `relativeCohomologyMap_comp`, `e.inv_hom_id`, `relativeCohomologyMap_id` |
| `forgetRel_relativeCohomologyMap` | for f : P ⟶ P', `forgetRel P n (relativeCohomologyMap ℚ n f x) = homologyMap (linearDualMap (fstChainMap f)) n (forgetRel P' n x)` | dual of upstream's `relativeChainProjection_naturality`, 8 lines |
### The proofs, as checked
(a). `forgetRel_relativeCohomologyMap` along `topPairIso`, applied to R (flasqueModel X Z n α) with R upstream's `supportedRationalSingularSectionCohomologyEquivRelative … Z.compl ⊤ n`; then `supported_forget_compat X Z n α` and `fst_topOpen`. Four lines.
(b). `transport_eq_flasqueModel`; `congrArg (relativeCohomologyMap ℚ n ·)` of `ofSubsetIsoNeighborhoodTop_hom_comp_inv Z`, split by `relativeCohomologyMap_comp`; `LinearMap.congr_fun`. Four lines. Upstream's `…SupportComplement` unfolds to R followed by `relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement _ Z Z.isClosed ⊤).inv`, which the last step uses by unfolding.
Sign audit: every map in both proofs is either an upstream equivalence already in the checked statements or a pullback along a pair isomorphism that is the identity on points; the chain-level dual of an identity map is the identity, so no sign can enter.
Non-vacuity (change C, rung `supported-pair-forget-test`): `supportedEquivPair_supportedClass_ne_zero` (Φ [Z_x] ≠ 0 for every scheme point x, so both sides of (b) are nonzero) and `forgetRel_supportedEquivPair_genericPoint_ne_zero` (the left side of (a) is nonzero at the generic point, in degree 0).
Downstream spelling (change D, for `cycle-class-multiplicative`). State `unionComplIso` for `Z W T : Closeds Y` with `hT : T = Z ⊓ W`, on `TopPair.ofSubset ((Z.compl : Set Y) ∪ (W.compl : Set Y)) ≅ TopPair.ofSubset (T.compl : Set Y)`, so that it meets `relCup2` of two Φ-classes term for term, and spell the pairs of `triad-relative-cup` so that `A := (Z.compl : Set Y)` is accepted without unfolding. The `Set` form in "Glue statements" above is superseded by this one; also recorded in the ledger note of `cycle-class-multiplicative`.

## fundamental-class-unit: statement

Date: 2026-11-26. Statement elaborated with `sorry` bodies first, then every body proved in the same session. Red team: pass with changes (`docs/sketches/fundamental-class-unit.redteam.md`), all implemented. Checked: rung `fundamental-class-unit`, module `HodgeLadder.Tests.FundamentalClassUnit` (the derived `file` hint `HodgeLadder/Fundamental/Class/Unit.lean` is superseded), and rung `singular-unit`, module `HodgeLadder.Cup.SingularUnit` (change B), both imported from `HodgeLadder.lean`. All twelve declarations of the reviewed file, and the sign test of change C, check with `propext`, `Classical.choice`, `Quot.sound`. `lake env lean` on the test module: 35 to 45 s wall; on `SingularUnit`, 15 s; default heartbeats.

Result for the kill criterion: [X] = 1 holds at the pin, with sign + and no scalar. The decisive inputs are upstream's normalization `normalizedDual_apply_self` and `standardAmbientClassZero_projection` (the standard local class of ℝ⁰ is the point with coefficient 1; equivalently, augmentation 1), with `SSet.ιChainComplex_constCochain` (the constant cocycle is 1 on that point), so the degree-0 normalization of upstream's cycle class is the constant cocycle 1. `standardLocalClass_zero_epsilon` enters only for nonvanishing. Conventions row "Degree-zero orientation and the unit".
## affine-chart-analytic: statement
Rung `affine-chart-analytic` (red team finding 12, consumers `p2-lines-transversal` and `p1p1-fibres-transversal`), checked 2026-11-26. The statement was fixed first and passed a statement red team with changes (`docs/sketches/affine-chart-analytic.redteam.md`); the changes are implemented. General part: `HodgeLadder/Normalization/AffineChart.lean`, module `HodgeLadder.Normalization.AffineChart`, next to the checked chart step; it imports no `Tests` or port module (change D). The ℙⁿ instance is its own rung, `affine-chart-analytic-p2`, in `HodgeLadder/Tests/ProjectiveChart.lean`. Both are imported from `HodgeLadder.lean`.

### The rung

```lean
theorem cycleComponentSheafClass_genericPoint_eq_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) =
      (one X : H^(2 * 0)(X; ℚ))
```

Hypotheses: the three instances `cycleComponentSheafClass` needs. `one X` needs none. Inside the proof: `QuasiSeparatedSpace X.left` (from `quasiSeparatedSpace_of_quasiSeparated X.hom`) for upstream's `ComplexPoint.connectedSpace`, and paracompact opens (upstream `openParacompactSpace X`) for the comparison Ψ; `T2Space (ComplexPoint X)` comes from upstream's instance on projective X.

Trivial proofs fail (scratch file, deleted): `rfl` and `exact rfl` (not definitionally equal), `simp [one]` (unsolved goal `cycleComponentSheafClass … = oneY …`).

Non-vacuity: both sides are nonzero on every X (`cycleComponentSheafClass_genericPoint_ne_zero`; `one X = fieldCohomologyUnit ℚ X ≠ 0` by upstream `rationalCohomologyUnit_ne_zero`), and Spec ℂ meets the hypotheses (`HodgeLadder.Tests.exists_smooth_projective_integral`).

### Helpers, all proved

After change B, `oneSing`, its four lemmas, `rationalCohomologyAddEquivSingularCohomology_one` (generalized to `[T2Space (ComplexPoint X)]` and paracompact opens) and `one_eq_fieldCohomologyUnit` live in `HodgeLadder.Cup.SingularUnit`, namespace `HodgeLadder.Cup`; the others stay in `HodgeLadder.Tests`. Sign test (change C): `cycleComponentSheafClass_genericPoint_ne_neg_one`, [X] ≠ −1.

| Declaration | Statement | Proof |
|---|---|---|
| `one_eq_fieldCohomologyUnit` | `one X = fieldCohomologyUnit ℚ X`, any X | `oneY_eq_kappa`, both sides `Ext.mk₀` of the constant-sheaf map of `n ↦ n`; 5 lines |
| `exists_cycleComponentSheafClass_genericPoint_eq_smul_one` | `∃ c ≠ 0, [X] = c • one X` | upstream `rationalCohomologyClass_surjective` on connected X(ℂ), `fieldCohomologyClass_mul`, `cycleComponentSheafClass_genericPoint_ne_zero` |
| `oneSing Y` (def) | class of Tau Ceti's constant 0-cocycle `1`, moved to upstream's `Cohomology ℚ Y 0` along `cohIso` | |
| `cupSing_oneSing`, `oneSing_cupSing` | `oneSing` is a right and left unit of `cupSing` | Tau Ceti `singularCup_constSingularCocycle_right`, `_left`, unitors |
| `cohomologyMap_oneSing` | pullback of `oneSing` is `oneSing` | `homologyMap_dualIsoYoneda_apply`, Tau Ceti `singularCohomologyMap_homologyπ_constSingularCocycle` |
| `oneSing_ne_zero` | `oneSing Y ≠ 0` for nonempty Y | `homologyπ` is an iso in degree 0; the cochain is `1` on a vertex |
| `rationalCohomologyAddEquivSingularCohomology_one` | `Ψ (one X) = oneSing` | `cup_singular_comparison` at p = 0 (sign `(−1)^0`), Ψ surjective, right unit law |
| `exists_mem_cycleComponentSmoothSupportAmbientOpen` | `X(ℂ) ∖ Z_sing(ℂ)` has a point, every component Z | upstream `cycleComponentSmoothLocusOver_nonempty`; injectivity of the component's closed immersion |
| `forgetRel_eq_oneSing_of_standardLocalClass_zero` | on ℝ⁰, a class with value 1 on `standardLocalClass ℚ 0` forgets to `oneSing` | universal coefficients; `standardAmbientClassZero_projection` (the point, coefficient 1) and `SSet.ιChainComplex_constCochain` decide the value; `span_standardLocalClass_zero_eq_top` (nonvanishing) makes the value at one class enough (`linearDualHomologyEquiv_homologyπ_apply`, port) |
| `forgetRel_chartNormalProjectionCoclass_zero` | at c = 0, `forgetRel (chartNormalProjectionCoclass E 0 e S hS W hW) = oneSing W` | move upstream's normalized class from (ℂ⁰, ∅) to (ℝ⁰, ∅) along `standardComplexRealPairIso 0`; `forgetRel_relativeCohomologyMap`, `cohomologyMap_oneSing` |

### The proof, as checked

1. [X] = c • one X with c ≠ 0 (helper 2).
2. Ψ (one X) = oneSing, so Ψ [X] = c • oneSing (helpers 5 and 7; Ψ is additive, hence ℚ-linear).
3. Pick y in X(ℂ) ∖ Z_sing(ℂ) for Z the reduced closure of the generic point (helper 8); `adaptedChart_genericPoint` gives the chart hypotheses of `transport_supportedClass_eq_chartNormalProjectionCoclass` at y, and helper 8 gives `hyU`. So `cycle-class-germ` applies with no use of the missing lemma `cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤`: one point suffices.
4. On the open W ∋ y it returns, forget the subspace: the restriction of Ψ [X] to W is `forgetRel` of the normal projection coclass, through `supported-pair-forget` (a) and (b) and `forgetRel_relativeCohomologyMap`; that is `oneSing W` (helper 10).
5. Restriction of c • oneSing is c • oneSing W (helper 6), so (c − 1) • oneSing W = 0 and oneSing W ≠ 0 (helper 6, W ∋ y), hence c = 1.

Sign audit: the only signs on the route are `(−1)^{pq}` of `cup_singular_comparison` at p = q = 0, the identity pair maps of `supported-pair-forget`, and the transport (ℂ⁰, ∅) ≅ (ℝ⁰, ∅), a map of one-point spaces. The value is fixed by upstream's normalization `normalizedDual_apply_self` on `standardComplexLocalClass ℚ 0` and by `standardAmbientClassZero_projection` (the point with coefficient 1).

Inputs to list for the drift check on the next pin bump: from upstream's `Other`, `rationalCohomologyClass_surjective` (`Cohomology/RationalDegreeZero.lean`), `fieldCohomologyUnit`, `fieldCohomologyClass_mul` (`Hodge/Filtration.lean`), `ComplexPoint.connectedSpace` (`ComplexPoint/SmoothConnected.lean`), `cycleComponentSmoothLocusOver_nonempty` (`Cycle/Component/CoclassNonzero.lean`), besides those already listed above; from the statement closure, `standardAmbientClassZero`, `standardAmbientClassZero_projection`, `standardRelativeHomologyProjectionZeroIso`, `span_standardLocalClass_zero_eq_top` (`Lemmas/AlgebraicTopology/LocalHomology/FundamentalClassGenerator.lean`).

Red-team answers (implemented): the general lemmas moved to `HodgeLadder.Cup.SingularUnit` with a `docs/gaps.md` row; the module path is `HodgeLadder.Tests.FundamentalClassUnit`; the conventions row "Degree-zero orientation and the unit" was added. Further drift inputs named by the red team (section 8 of the verdict) are listed there.
variable (X : Over (Spec ↧ℂ)) {d : ℕ} (U : X.left.Opens)
  (e : openScheme X U ≅ Over.mk (complexAffineSpace (Fin d) ↘ Spec ↧ℂ))
def affineCoordinates : ComplexPoint (openScheme X U) ≃ₜ (Fin d → ℂ) :=
  (Point.isoMapHomeomorph e).trans (affineSpaceHomeomorph (Fin d))
def affineChart : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  (affineCoordinates X U e).toOpenPartialHomeomorph.lift_openEmbedding
    (isOpenEmbedding_map_open X U)
theorem affineChart_mem_maximalAtlas [SmoothOfRelativeDimension d X.hom] :
    affineChart X U e ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)
In words: U ≅ 𝔸^d over Spec ℂ (an isomorphism in `Over (Spec ℂ)` from upstream's `openScheme X U`), the complex points of U go to ℂ^d by the values of the coordinate functions `AffineSpace.coord m` pulled back along e, and this chart, extended along upstream's open embedding U(ℂ) → X(ℂ), is in Mathlib's maximal analytic atlas for upstream's charted space. Membership in the maximal atlas is compatibility with every chart of upstream's atlas, the range of `localChart`; `affineChart_compatible_localChart` states it in that form (both transitions with `localChart X d z` in `contDiffGroupoid ω`), proved from the rung by `IsManifold.compatible_of_mem_maximalAtlas`. Both definitions are sorry-free and use only upstream's homeomorphisms (`Point.isoMapHomeomorph`, `affineSpaceHomeomorph`, `isOpenEmbedding_map_open`). Sign: coordinate m of the chart is `AffineSpace.coord m` pulled back along e, with no conjugation (row "Holomorphic adapted chart").
### Proved with it
| `affineChart_apply_map` | `affineChart X U e (Point.map (openInclusion X U) q) = affineSpaceEquiv (Fin d) (Point.map e.hom q)` | `lift_openEmbedding_apply`, `rfl` |
| `affineChart_source`, `affineChart_target` | source is the range of `Point.map (openInclusion X U)`; target is `univ` | `lift_openEmbedding_source`, `_target` |
| `affineChart_compatible_localChart` | for every z, both transitions with `localChart X d z` are in the analytic groupoid | from the rung, `IsManifold.compatible_of_mem_maximalAtlas` |
### The instance for the ℙ² consumers
Rung `affine-chart-analytic-p2`, module `HodgeLadder.Tests.ProjectiveChart`. Stated for every ℙⁿ (`HodgeLadder.Tests.projectiveSpace n`), at the cost of ℙ², as in `p2-witness`.
| Declaration | Statement | Status |
| `projectiveChartImmersion n i` | Oka's `ProjectiveSpace.chart i : Spec ℂ[Y₀, …, Y_{n−1}] ⟶ ℙₒ(n; ℂ)` (Yₘ = x_{i.succAbove m} / xᵢ) followed by `(okaIsoSpace n).hom`; an open immersion (instance) | definition |
| `projectiveChartOpen n i` | its `opensRange`, an abbreviation | definition |
| `projectiveChartOpen_eq` | `projectiveChartOpen n i = (okaIsoSpace n).hom ''ᵁ ProjectiveSpace.U n ℂ i` | proved (`opensRange_comp`, `opensRange_chart`) |
| `projectiveChartSchemeIso`, `_over` | `isoOpensRange.symm ≪≫ (AffineSpace.SpecIso (Fin n) (.of ℂ)).symm`, and it lies over Spec ℂ | proved (`chart_toSpec`, `okaIsoSpace_hom_toBase`, `SpecIso_inv_over`) |
| `projectiveChartIso n i` | `openScheme (projectiveSpace n) (projectiveChartOpen n i) ≅ Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)` | definition, sorry-free (`Over.isoMk`) |
| `projectiveChart n i` | `affineChart` of that iso | definition |
| `projectiveChart_mem_maximalAtlas`, `projectivePlane_chart_mem_maximalAtlas (i : Fin 3)` | the chart is in the maximal atlas of ℙⁿ(ℂ), of ℙ²(ℂ) with `Fin 2 → ℂ` | one line from the rung |
| `projectiveChart_symm_underlying` | `((projectiveChart n i).symm v).underlying = (okaIsoSpace n).hom.base ((ProjectiveSpace.chart i).base (ProjectiveSpace.evalPoint (RingHom.id ℂ) v))` | proved (red team section 7: prime ideals compared by basic opens through `evaluate_affineSpaceEquiv_symm_top`) |
| `projectiveChart_symm_mem_U_iff` | `((projectiveChart n i).symm v).underlying ∈ (okaIsoSpace n).hom ''ᵁ ProjectiveSpace.U n ℂ j ↔ Fin.insertNth i 1 v j ≠ 0` (change B) | proved, from the row above and `chart_base_evalPoint_mem_U_iff` |
The last row is what `p2-lines-transversal` reads: the point (projectiveChart 2 2).symm v has homogeneous coordinates (v₀, v₁, 1), so the chart x₂ ≠ 0 has coordinates (x₀ / x₂, x₁ / x₂) and L₀, L₁ are {v₀ = 0}, {v₁ = 0} in it. The hypothesis of the rung is met at the pin by `projectiveChartIso`, which is sorry-free, so the rung is not vacuous.
### Failed trivial proofs
On `affineChart_mem_maximalAtlas`: `rfl`, `simp` (no progress), `aesop` (no progress), `trivial`, `exact?` fail, and `exact IsManifold.chart_mem_maximalAtlas _` times out at 200000 heartbeats. On `projectiveChart_symm_underlying`: `rfl`, `simp`, `aesop`, `trivial`, `exact?` fail.
### Open-immersion form (change A)
`openImmersionAffineIso X j`, `openImmersionChart X j`, `openImmersionChart_symm` (the inverse chart at v is `Point.map j` of the point of 𝔸^d with coordinates v) and `openImmersionChart_mem_maximalAtlas`, for an open immersion j : 𝔸^d ⟶ X over Spec ℂ, with U = range j. `p1p1-fibres-transversal` can build its chart this way; its coordinate order is that rung's convention.
Write ι = `Point.map (openInclusion X U)` and A = `affineSpaceEquiv (Fin d)`. Mathlib's `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn`, with `contMDiffAt_of_analyticAt_chart` from `ChartStep` (the chart of the model space is the identity, `chartAt_self_eq`).
1. The chart is holomorphic on its source. `affineChart_apply_eq_evaluate`: on the source, coordinate m is `Point.evaluate` of `affineCoordinateSection X U e m`, the section `(U.ι.appIso _).inv (e.hom.left.app ⊤ (coord m))` over `U.ι ''ᵁ (e.hom.left ⁻¹ᵁ ⊤)` (upstream `affineSpaceEquiv_apply`, `evaluate_top_eq_appTop`, `Point.evaluate_map`, `evaluate_openEquiv`); upstream's `analyticAt_localChart_symm_evaluate` makes it analytic in `localChart X d w`.
2. Its inverse is holomorphic on ℂ^d. The inverse is ι ∘ `Point.map e.inv` ∘ A⁻¹ by definition. Coordinate k of `localChart X d w` is evaluation of an étale coordinate section of X (`localChart_apply_component_eq_evaluate`); `Point.evaluate_map` twice moves it to a section of 𝔸^d, and `analyticAt_evaluate_affineSpaceEquiv_symm` (red team section 8, 30 lines: a basic open around the point, `exists_evaluate_basicOpen_eq_div`, `evaluate_affineSpaceEquiv_symm_top`, Mathlib's `AnalyticOnNhd.eval_continuousLinearMap`) makes it analytic. The membership of the point in the open comes from `mem_coordinateNeighborhood_of_mem_localChart_source` and `Point.mem_overOpen_map_iff` twice. Upstream's `analyticAt_localChart_symm_map` was not needed.
About 75 lines for the rung and its helper. One trap: `rw [hsymm]` with `hsymm : ∀ u, φ.symm u = ι (…)` rewrites the base point of `localEtaleCoordinates X d (φ.symm v)` first and fails on the motive; `rw [hsymm u]` works.
Open test rung `affine-chart-conj-test` (change F): the chart of ℙ¹ followed by complex conjugation is outside the maximal atlas; statement in its ledger note, elaborated, not proved.
Timing: `lake env lean HodgeLadder/Normalization/AffineChart.lean` 5 s wall, `HodgeLadder/Tests/ProjectiveChart.lean` 5 s; default heartbeats. Every declaration either ledger rung names checks with the standard axioms.

## cycle-class-germ-point: statement

Date: 2026-11-26. Rung `cycle-class-germ-point` (red team on `cycle-class-germ`, change H), kind test, checked. The statement was fixed first and passed a statement red team with changes (`docs/sketches/cycle-class-germ-point.redteam.md`); changes 1 to 5 are implemented, change 6 (a shared chart module for `Germ.lean` and the test) is skipped. Module `HodgeLadder.Tests.CycleClassGermPoint`, imported from `HodgeLadder.lean`; the derived `file` hint `HodgeLadder/Cycle/Class/Germ/Point.lean` is superseded. All 23 declarations the ledger names check with `propext`, `Classical.choice`, `Quot.sound`. `lake env lean` on the module: 28 s wall, default heartbeats.

Independence by imports, guarded: the module imports `HodgeLadder.Normalization.ChartStep` (atlas lemmas only), upstream `Other` and Mathlib modules, and neither `HodgeLadder.Normalization.Germ` nor `HodgeLadder.Normalization.Singular` (change 1). A `run_cmd` guard at the end of the file (change 2) fails the build if either is imported, or if the rung's proof reaches `exists_open_chartNormalProjectionCoclass_eq`, `exists_open_complexDifferentiable_localClass_invariance`, `smoothClosedSupportCoclassStalk_eq_chartGerm`, `analyticAt_transition_of_factor` or `analyticAt_transition_of_mem_maximalAtlas`. Positive controls (scratch, deleted): adding the `Singular` import, and pointing the guard at a probe theorem that uses `exists_open_chartNormalProjectionCoclass_eq`, each fail the build with the guard's message. The chart of `adaptedChart_closedPoint` sits behind an existential there, so the file names it as a definition and reproves its four hypotheses.

### Setting

Fix a complex point y₀ of X, d = dim X, x = y₀.underlying (closed, coheight d), Z = {y₀}, U = X ∖ Z_sing = X(ℂ). Write T [Z] for the left side of `cycle-class-germ`: `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2d)` after `rationalSupportAddEquivSupportedInjectiveHomology`, applied to `cycleComponentSupportedInjectiveClass X x hx`.

| Declaration | Statement | Status |
|---|---|---|
| `closedPointChartLinear X` (abbrev) | `ContinuousLinearEquiv.uniqueProd ℂ (Fin d → ℂ) (Fin 0 → ℂ)` | definition |
| `closedPointChart X y₀` (def) | `((chartAt y₀).trans (addRight (−chartAt y₀ y₀))).trans (closedPointChartLinear X).symm`, the chart `e` of `adaptedChart_closedPoint` | definition |
| `closedPointChart_source`, `closedPointChart_apply_snd`, `mem_closedPointChart_source` | source is that of `chartAt y₀`; normal coordinate `chartAt y₀ z − chartAt y₀ y₀`; y₀ in the source | proved |
| `coheight_underlying` | `Order.coheight y₀.underlying = dim X.left` | proved |
| `closedPointChart_mem_maximalAtlas`, `closedPointChart_support`, `mem_smoothSupportAmbientOpen_closedPoint` | hypotheses `he`, `hS`, `hyU` of `cycle-class-germ` for this chart (with `hy` above) | proved, as in `adaptedChart_closedPoint` |
| `transport_supportedClass_eq_pointRelativeCoclass` | for every x with `hx : coheight x = dim X.left` and every complex point z of the component, T [Z] = `analyticComponentPointRelativeCoclass X x (dim X.left) z` | proved: upstream `cycleComponentSupportedInjectiveClass_point_normalization`, `AddEquiv.apply_symm_apply`, `analyticComponentPointSupportedInjectiveCoclass_relative` |
| `pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass` | the cross-check, below | proved, Germ-free |
| `chartNormalProjectionCoclass_ne_zero_of_mem`, `chartNormalProjectionCoclass_closedPointChart_ne_zero` | non-vacuity (change 4): a chart coclass is nonzero on every open W of the source meeting the support; the right side of the rung is nonzero on every admissible W | proved; the generic one is listed in `docs/gaps.md` "General lemmas kept local" |
| `transport_restrict_eq_pointRelativeCoclass_restrict_eq_chartNormalProjectionCoclass` | on one open W ∋ y₀ inside the chart source: restriction of T [Z] = restriction of the point coclass, and restriction of the point coclass = chart coclass | proved from the two rows above |
| `transport_supportedClass_eq_chartNormalProjectionCoclass_closedPoint` | the conclusion of `cycle-class-germ` at x, this chart, y = y₀, by the point route | proved from the row above; z from upstream `range_cycleComponentMap` |

### The rung

```lean
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
          (closedPointChart_support X y₀) W hW
```

Instances: `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`; `SmoothOfRelativeDimension (dim X.left) X.hom` is found by upstream's `SmoothOfRelativeDimension.of_isIntegral`. Exact, no sign, no scalar. Both sides are normalized against the complex orientation of ℂ^d with consecutive (Re, Im) pairs (rows "Complex orientation of ℂ^p", "Fundamental-class normalization"): the left side is the normalized dual of `localClassOfChart` of `localChart X d y₀`, the right side the pullback along w ↦ chartAt y₀ w − chartAt y₀ y₀ of the normalized dual of `standardComplexLocalClass`. The shape (∃ W, restriction on W) is the shape of `cycle-class-germ`, so the two are compared like for like.

### What the test can and cannot show

Inside Lean the two paths cannot disagree: both are theorems at the same pin. A scratch file (deleted) that adds the import of `HodgeLadder.Normalization.Germ` proves the rung in eight lines from `transport_supportedClass_eq_chartNormalProjectionCoclass` and `transport_supportedClass_eq_pointRelativeCoclass`, and the same statement with the right side negated falls to none of the trivial tactics. So the rung holds at the pin, and the point route gives sign + with coefficient 1. The test's value is the second proof: an independent derivation of the closed-point case, which breaks if either route's normalization drifts at a pin bump. That proof is only independent if it avoids `Germ.lean`; the import list enforces it.

Shared inputs, named for the red team: both routes start from upstream's normalization isomorphism and `cycleComponentSmoothSupportCoclassSection` (the point route through `cycleComponentSupportedInjectiveClass_unique` inside upstream's `cycleComponentSupportedInjectiveClass_point_normalization`, and upstream's singleton comparison `smoothClosedSupportCoclassSection_eq_point_of_singleton`). They split after that: `cycle-class-germ` uses the flattening charts on X ∖ Z_sing, the chart step and `exists_open_chartNormalProjectionCoclass_eq`; the point route uses the old coclass `analyticPointLocalCoclass` and, in phase 2, a direct radial computation for the translated `localChart`.

### The proof, as checked

The computation is stated for an abstract chart c : M ⇀ ℂ^d with y₀ ∈ c.source and a chart e : M ⇀ ℂ⁰ × ℂ^d with e.source ⊆ c.source and normal coordinate c − c y₀ (section `Abstract` of the module), then specialized with c = `chartAt y₀` and e = `closedPointChart X y₀`. The red team met a kernel timeout on a direct proof at the concrete chart; the abstract form avoids it.

1. `chart_flattenedSupportHomeomorph`: on the normal fibre of the flattened neighbourhood F of e at y₀, c reads `univBall 0 r v + c y₀` (upstream `flattenedSupportHomeomorph_coordinates`, `univBall_zero_tangent_normal`).
2. `flattenedTargetPairMap` is that map into (c.target, c.target ∖ {c y₀}); followed by the inclusion it is the centred radial map then translation by c y₀ (`flattenedTargetPairMap_comp_inclusion`), so upstream's `chartTargetPointPairMap_localClass` with `centeredComplexUnivBall_preserves_standardComplexLocalClass` sends the standard class to `localClassOfChart d c y₀` (`flattenedTargetPairMap_localClass`).
3. `normalFiber_toPoint`: the normal fibre, upstream's `flattenedSupportPairIso` and the inclusion into (M, M ∖ {y₀}) compose to that map followed by the inverse of c. With `flattenedSupportNormalClass_eq_normalFiber`, the normal class goes to `localClassOfChart` (`normalClass_toPoint_eq_localClassOfChart`), coefficient 1.
4. `normalizedCoclass_toPoint_eq_chartNormalProjectionCoclass`: the normalized dual of `localClassOfChart`, pulled back to F, pairs to 1 with the normal class (`relativeCohomologyEquivDualHomology_relativeCohomologyMap`, `normalizedRelativeCoclass_pairing_self`), so upstream's `chartNormalProjectionCoclass_unique` makes it the chart coclass on F.
5. The rung, W = F. A `change` rewrites S in the spelling `cycleComponentSupport X x` and unfolds `analyticComponentPointRelativeCoclass`; `erw` with `relativeCohomologyMap_comp` and `neighborhoodSupportInclusionPairMap_toPoint` composes the two pair maps; the membership proof and then `cycleComponentMap X x z` are generalized and substituted by y₀ (upstream `cycleComponentSupport_eq_singleton_of_coheight_eq_dimension`); step 4 closes the goal, since `analyticPointLocalCoclass X d y₀` is by definition the normalized dual of `localClassOfChart d (localChart X d y₀) y₀` and `chartAt y₀` is `localChart X d y₀` by `rfl`.

About 150 lines for steps 1 to 5. The two paths agree: sign +, coefficient 1. In this proof the only sign-bearing inputs are upstream's radial normalization `centeredComplexUnivBall_preserves_standardComplexLocalClass` and the translation in `chartTargetPointPairMap_localClass`; the orientation of ℂ^d enters both sides through `standardComplexLocalClass` and cancels (pinned by `cross-orientation`, `real-affine-orientation`).

### Failed trivial proofs

On the rung (scratch file, deleted): `rfl`, `simp`, `trivial`, `decide`, `aesop` (heartbeat timeout), and with W = the chart source: `rfl` (the sides are not definitionally equal), `simp [chartNormalProjectionCoclass, analyticComponentPointRelativeCoclass]` (unsolved goals), `Subsingleton.elim` (no instance).

## p2-lines-transversal: statement

Date: 2026-11-26. Checked. Statements fixed first with one `sorry`, red-teamed (`docs/sketches/p2-lines-transversal.redteam.md`, pass with changes A to D, all implemented), then the open lemma proved. File `HodgeLadder/Tests/ProjectivePlaneLines.lean`, module `HodgeLadder.Tests.ProjectivePlaneLines`, next to `ProjectivePlane` and `ProjectiveChart`, imported from `HodgeLadder.lean`. The ledger's derived `file` hint `HodgeLadder/P2/Lines/Transversal.lean` is superseded. Imports: `HodgeLadder.Tests.ProjectiveChart`, upstream `HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity` (for `cycleComponentSmoothSupportAmbientOpen`) and `HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula` (for `SmoothOfRelativeDimension.coheight_le_complex`); no `Other` module. `lake env lean` on the file: 5 s wall, default heartbeats.

### The points and how they are named

All three come from the chart x₂ ≠ 0, `projectiveChartImmersion 2 2 : Spec ℂ[Y₀, Y₁] ⟶ projectivePlane.left` (Oka's `ProjectiveSpace.chart 2` followed by `okaIsoSpace 2`, Yₘ = xₘ / x₂).

| Declaration | Definition |
|---|---|
| `planeLineRestrict k` | `MvPolynomial.aeval (fun m => if m = k then 0 else X 0) : ℂ[Y₀, Y₁] →ₐ[ℂ] ℂ[T]`, restriction to Y_k = 0; surjective (`planeLineRestrict_surjective`) |
| `planeLinePrime k` | its kernel, the prime (Y_k), as a `PrimeSpectrum` |
| `planeEvalPoint v` | kernel of evaluation at v, the port's `evalPoint (RingHom.id ℂ) v` typed as a `PrimeSpectrum` (the `Spec` carrier blocks `rw` across the two) |
| `planeChartPoint q` | `(projectiveChartImmersion 2 2).base q` |
| `planeLine k : projectivePlane.left` | `planeChartPoint (planeLinePrime k)`: L₀ at k = 0, L₁ at k = 1 |
| `planeOriginPoint : ComplexPoint projectivePlane` | `(projectiveChart 2 2).symm 0`, the complex point [0 : 0 : 1] |
| `planeOrigin : projectivePlane.left` | `planeOriginPoint.underlying`; equal to `planeChartPoint (planeEvalPoint 0)` (`planeOrigin_eq`) |

### The statements, in the form of the hypotheses of `cycle-class-multiplicative`

With X = `projectivePlane`, x = `planeLine 0`, w = `planeLine 1`, t = `planeOrigin`, a = b = 1, d = 2:

```lean
theorem coheight_planeLine (k : Fin 2) : Order.coheight (planeLine k) = (1 : ℕ)
theorem coheight_planeOrigin : Order.coheight planeOrigin = (2 : ℕ)

theorem planeOrigin_support_eq_inter :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) =
      (cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0) :
          Set (ComplexPoint projectivePlane)) ∩
        cycleComponentAnalyticClosedSupport projectivePlane (planeLine 1)

theorem planeOrigin_support_eq_singleton :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) = {planeOriginPoint}

theorem planeLines_transversal :
    ∀ y ∈ (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint projectivePlane),
        y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0) ↔
            ∀ i : Fin 1, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 1) ↔
            ∀ j : Fin 1, φ z ⟨1 + j, by omega⟩ = 0)

theorem planeOrigin_support_subset_smoothSupportAmbientOpen (k : Fin 2) :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) ⊆
      cycleComponentSmoothSupportAmbientOpen projectivePlane (planeLine k)
```

These are `hx`, `hw` (k = 0, 1), `ht`, `hT`, the "= {p(ℂ)}" item, `htr`, and `hxreg`, `hwreg` (k = 0, 1). Instantiation check (scratch file inside the worktree, deleted): with the general statement of section "Statement" copied verbatim and `sorry`ed, the term `cycleComponentSheafClass_cup_of_transversal projectivePlane (planeLine 0) (planeLine 1) planeOrigin (coheight_planeLine 0) (coheight_planeLine 1) coheight_planeOrigin (by norm_num) planeOrigin_support_eq_inter (planeOrigin_support_subset_smoothSupportAmbientOpen 0) (planeOrigin_support_subset_smoothSupportAmbientOpen 1) planeLines_transversal` elaborates against `cup [L₀] [L₁] (2 * (1 + 1)) _ = cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin`. So `cycle-class-multiplicative-p2` closes by `exact` once the general rung is checked: `↑2` meets `↑(1 + 1)` by defeq, d = 2 comes from `Fin 2` in `htr` and the instance `smoothOfRelativeDimension_projectiveSpace 2`, and the `by omega` proofs inside `Fin.mk` are irrelevant to the match.

Also stated and proved: `closure_planeLine_inter` with `planeEvalPoint_zero_le` (change B: closure {L₀} ∩ closure {L₁} = closure {[0 : 0 : 1]} in `projectivePlane.left`), `mem_planeLine_support_iff` (in the chart x₂ ≠ 0, z ∈ L_k(ℂ) ↔ `projectiveChart 2 2 z k = 0`), `mem_planeLine_inter_iff`, `planeLine_zero_ne_one` (the two lines are different scheme points; with the coheights, all three points are distinct).

### What is proved

| Item | Status | Route |
|---|---|---|
| coheights 1, 1, 2 | proved | `planeOrigin < planeLine k < ⊤` in the specialization order (`planeChartPoint_specializes_iff`: the chart is an open embedding; `⊤` lies in every standard open, `L_k` does not lie in x_k ≠ 0), `Order.coheight_add_one_le` twice, and upstream's `coheight_le_complex` (≤ 2); no closedness of the point is used |
| `hT`, singleton | proved | `closure {L_k}` misses the open x_k ≠ 0 (`L_k` is outside it); the three standard opens cover (`iSup_U`), so a point of L₀(ℂ) ∩ L₁(ℂ) lies in the chart x₂ ≠ 0, where both coordinates vanish; L_k ⤳ [0 : 0 : 1] gives the other inclusion |
| `htr` | proved | φ = `projectiveChart 2 2`, in the atlas by `projectivePlane_chart_mem_maximalAtlas 2`; adaptedness from `projectiveChart_two_symm_underlying` and `planeLinePrime_le_planeEvalPoint_iff` (v ∈ V(Y_k) ↔ v_k = 0) |
| `hxreg`, `hwreg` | proved | membership in `cycleComponentSmoothSupportAmbientOpen` unfolds, by `rintro`, to the lemma below for a point of the reduced closure over [0 : 0 : 1] |
| scheme-level `hT` (change B) | proved | `closure_planeLine_inter` |

The smooth-locus lemma:

```lean
theorem cycleComponent_planeLine_mem_smoothLocus (k : Fin 2)
    (z : cycleComponent projectivePlane.left (planeLine k))
    (hz : cycleComponentι projectivePlane.left (planeLine k) z = planeOrigin) :
    z ∈ (cycleComponentι projectivePlane.left (planeLine k) ≫ projectivePlane.hom).smoothLocus
```

Every declaration the ledger names prints `propext`, `Classical.choice`, `Quot.sound`.

### The proof of the smooth-locus lemma, as checked

1. U = `projectiveChartOpen 2 2`, affine (`isAffineOpen_opensRange`). `cycleComponent` is the subscheme of I = `vanishingIdeal ⟨closure {L_k}, _⟩`; Mathlib's `I.subschemeCover.f U : Spec (Γ(X, U) ⧸ I.ideal U) ⟶ cycleComponent` is an open immersion with range ι⁻¹ U (`opensRange_subschemeCover_map`), which contains z because [0 : 0 : 1] ∈ U, and `subschemeCover_map_subschemeι`, `glueDataObjι_ι` give its composite with ι as `Spec.map (Ideal.Quotient.mk _) ≫ U.fromSpec`.
2. By `Scheme.Hom.preimage_smoothLocus_eq` and `smoothLocus_eq_top`, it suffices that this composite followed by the structure map is smooth.
3. Identify Γ(X, U) ≅ ℂ[Y₀, Y₁] through `isoOpensRange` and `IsAffineOpen.isoSpec`, compatibly with ℂ (the chart lies over `Spec.map C`, as in `projectiveChartSchemeIso_over`). Under it, `I.ideal U = vanishingIdeal (U.fromSpec ⁻¹' closure {L_k})` (Mathlib `vanishingIdeal_ideal`) is the comap of `planeLinePrime k`: the preimage of a closure under an open embedding is the closure of the preimage, and `vanishingIdeal (closure {q}) = q`.
4. Then Γ(X, U) ⧸ I(U) ≅ ℂ[Y₀, Y₁] ⧸ (Y_k) ≅ ℂ[T] over ℂ (`planeLineRestrict_surjective`, `quotientKerAlgEquivOfSurjective`), and ℂ → ℂ[T] is smooth.

As checked (about 80 lines with two helpers): step 3 does not name `isoSpec`. `IsOpenImmersion.isoOfRangeEq` between `projectiveChartImmersion 2 2` and `U.fromSpec` (equal ranges, `IsAffineOpen.range_fromSpec`) gives an iso g of affine schemes, and φ = `Spec.preimage g.inv : ℂ[Y₀, Y₁] ⟶ Γ(X, U)` is the ring isomorphism of the red team's caution 1, with `U.fromSpec = Spec.map φ ≫ projectiveChartImmersion 2 2`. The ℂ-structure is the one of `MvPolynomial.C` (caution 2): `projectiveChartImmersion_two_over` (the chart lies over `Spec.map C`) turns the composite into `Spec.map (C ≫ φ ≫ mk)`, and `HasRingHomProperty.Spec_iff` reduces smoothness to the ring map. `I.ideal U = (g.hom (Y_k)).asIdeal` from `U.fromSpec ⁻¹' closure {L_k} = closure {g.hom (Y_k)}` (both open embeddings reflect specialization), `vanishingIdeal_closure`, `vanishingIdeal_singleton`; its comap along φ is (Y_k) because `Spec.map φ = g.inv`. The ring step `smooth_quotient_of_comap_eq_planeLinePrime` builds Γ(U) ⧸ I(U) ≅ ℂ[T] from two `quotientKerEquivOfSurjective` and `quotEquivOfEq`, checks that it carries `C` to the constants, and concludes with `RingHom.Smooth.comp`, `smooth_algebraMap` and `of_bijective`. No upstream `Other` input. Traps: an `affineOpens` element and its proof `U.2` do not elaborate as `IsAffineOpen` for `fromSpec` instances, so the proof names `hUa : IsAffineOpen _`; the cover index type `I₀` blocks the `IsOpenImmersion` instance on `I.subschemeCover.f U` until U is ascribed `I.subschemeCover.I₀`; `simp only [Category.assoc]` makes no progress on the composite (the same index-type mismatch), so associativity is closed by explicit `Category.assoc` terms.

### Failed trivial proofs

Scratch file inside the worktree, deleted. Coheights: `rfl` (not definitionally equal), `simp`, `simp [planeLine, planeChartPoint]`, `simp [planeOrigin]` (unsolved goals). `hT`: `rfl` fails, `simp` makes no progress; singleton: `simp` makes no progress. `hxreg`: `simp` (unsolved goal), `aesop` (fails after exhaustive search). The smooth-locus lemma: `simp` fails; with its proof a `sorry`, `exact?` found only that lemma itself; red team RT2: `Smooth` of the line by `infer_instance` and `rw [Scheme.Hom.smoothLocus_eq_top]` fail. `htr` with upstream's own chart, `⟨chartAt _ y, IsManifold.chart_mem_maximalAtlas y, mem_chart_source _ y, by simp⟩`: `simp` leaves the adaptedness goal open, so the adapted chart carries content.

### What this rung shows about the general statement

Every hypothesis of `cycle-class-multiplicative` is met on ℙ² with the coordinate lines, in the stated form, with no change to the statement. Two points for the red team: (1) `htr` indexes coordinates as `⟨i, _⟩` and `⟨a + j, _⟩`, so the chart must list L₀ first; `projectiveChart 2 2` does (coordinates (x₀/x₂, x₁/x₂)), and a swapped chart would need a reordering of `Fin 2`. (2) `hT` is a statement about complex points only. On a scheme of finite type over ℂ the complex points are dense in every closed subset, so `hT` implies the scheme-level equality `closure {x} ∩ closure {w} = closure {t}` (T is the only component, as the literature requires); on ℙ² that equality is `closure_planeLine_inter`.

## cycle-class-multiplicative: statement and route

Date: 2026-11-26. Checked. Statement and route fixed first with `sorry` bodies, then proved in the same session; the final statement and proof red team passed it with changes A to G (`docs/sketches/cycle-class-multiplicative.final.redteam.md`), all implemented. File `HodgeLadder/Cycle/Multiplicative.lean`, module `HodgeLadder.Cycle.Multiplicative`, namespace `HodgeLadder.Cycle`, imported from `HodgeLadder.lean`; the ledger's earlier `file` hint `HodgeLadder/Cycle/Class/Multiplicative.lean` is superseded. The first instance, rung `cycle-class-multiplicative-p2`, is checked in `HodgeLadder/Tests/CycleClassMultiplicativeP2.lean` (`coheight_planeOrigin_add`, `planeLines_cup_eq_planeOrigin`: [L₀] ∪ [L₁] = [pt] on ℙ², red team change A). Imports: `HodgeLadder.Local.ClassProduct`, `HodgeLadder.Cup.SupportedPairForget`, `HodgeLadder.Cup.CupSingular`, `HodgeLadder.Normalization.Germ`, `Other.AlgebraicGeometry.Cycle.FundamentalClass` (all built in the shared cache). `supported-open-naturality` and `supported-model-agreement-open` are not in the import closure and are no longer listed as dependencies (change C).

**Result.** The statement of section "Statement" elaborates verbatim, with no change to any hypothesis, definition, orientation, coordinate order or factor order. The main statement and the route lemmas elaborated with `sorry` bodies first (two short helpers, `restrict_supportedEquivPair` and `restrict_eq_chartNormalProjectionCoclass`, were written with their proofs); each body then turned out short enough to prove in the same session, so the file has no `sorry`. `#print axioms` on the main theorem, on `germ_transport_eq_of_chart` and on `cup_forgetSupport_of_product` gives `propext`, `Classical.choice`, `Quot.sound`. The computed sign is `+` with coefficient 1: [Z] ∪ [W] = [T] exactly. No step produced a sign other than `(−1)^{(2a)(2b)} = 1`, and no step depends on the codimensions beyond that parity.

Trivial proofs fail on the main statement (scratch file inside the worktree, deleted): `rfl` (the sides are not definitionally equal), `simp` (unsolved goal), `trivial`, `aesop` (exhaustive search fails), `simp [cup, cycleComponentSheafClass]` (unsolved goal). The statement with the right side negated, `cup … = -cycleComponentSheafClass X t ht`, also fails `simp`.

### Notation

Φ_S = `supportedEquivPair X S n` (supported classes to H^n(X, X ∖ S; ℚ) on `TopPair.ofSubset (S.compl : Set _)`); Ψ = `rationalCohomologyAddEquivSingularCohomology X n`; 𝒯 α = `complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n (rationalSupportAddEquivSupportedInjectiveHomology X S n α)`, upstream's transport at ⊤; α_Z = `cycleComponentSupportedInjectiveClass X x hx`, so [Z] = `forgetSupport ℚ X Z (2a) α_Z` by definition; N_T = `cycleComponentSupportedClassNormalizationIso X t ht`; U_T = `cycleComponentSmoothSupportAmbientOpen X t`.

### The route, as named lemmas

| Step | Declaration | Statement in words | Sign | Proof |
|---|---|---|---|---|
| glue | `neighborhoodSupportInclusionPairMap_comp_ofSubsetIsoNeighborhoodTop_inv` | upstream's restriction from (⊤, ⊤ ∖ Z) to (V, V ∖ Z), then `(ofSubsetIsoNeighborhoodTop Z).inv`, is `restrictToNeighborhood V Z` (sketch text) | none, identity on points | ext, `rfl` |
| glue | `restrictToNeighborhood_comp_ofSubsetIsoNeighborhoodTop_hom` | the same square read with `.hom` | none | ext, `rfl` |
| glue | `unionComplIso`, `unionComplIso_fst_apply` | (Y, (Y ∖ Z) ∪ (Y ∖ W)) ≅ (Y, Y ∖ T) for `hT : T = Z ⊓ W`, `Closeds` form (change D of `supported-pair-forget`) | identity of Y | `TopPair.isoOfSubset (Homeomorph.refl Y)` |
| glue | `mem_iff_of_eq_inf`, `unionComplIso_restrict` | sketch text, unchanged | none | `subst`; ext, `rfl` |
| glue | `forgetRel_unionComplIso` | `forgetRel` across `unionComplIso` is `forgetRel` | none: `fstChainMap` of the identity is `𝟙` | 6 lines |
| glue | `restrict_eq_chartNormalProjectionCoclass` | a chart identity on V' restricts to V ⊆ V' | none | upstream `chartNormalProjectionCoclass_restrict` |
| glue | `closeds_eq_inf_of_coe_eq` | the set form of `hT` gives `T = Z ⊓ W` | none | `SetLike.coe_injective`, `Closeds.coe_inf` |
| 5 | `normalSplit`, `splitChart`, `splitChart_mem_maximalAtlas` | for an injection k : Fin c → Fin d, ℂ^d ≃L (tangential) × ℂ^c with normal coordinates `v (k 0), …, v (k (c − 1))`; the split chart followed by the inverse splitting is in the maximal atlas when φ is | coordinate permutation, no conjugation | `LinearEquiv.funCongrLeft`, `sumArrowLequivProdArrow`; `mem_maximalAtlas_of_eqOnSource` |
| 1, 2 | `restrict_supportedEquivPair` | restricting Φ_S α from (X, X ∖ S) to (V, V ∖ S) is restricting 𝒯 α from (⊤, ⊤ ∖ S) | none | `supportedEquivPair_eq_transport` and the glue square |
| 1 to 4 | `cup_forgetSupport_of_product` | if Φ_T γ = `unionComplIso.inv`-pullback of `relCup2 (Φ_Z α) (Φ_W β)`, then Ψ (forget α ∪ forget β) = (−1)^{pq} • Ψ (forget γ), any p, q | (−1)^{pq} from `cup_singular_comparison'`, the only sign | `forgetRel_supportedEquivPair` (three times), `forgetRel_relCup2`, `forgetRel_unionComplIso` |
| 6 | `transport_restrict_of_supportedEquivPair_eq` | with the same hγ, the restriction of 𝒯 γ to (V, V ∖ T) is `(chartUnionIso V _).inv`-pullback of `relCup2` of the restrictions of 𝒯 α and 𝒯 β | none | `relCup2_restrict`, `unionComplIso_restrict`, `restrict_supportedEquivPair` |
| 5, 6 | `germ_transport_eq_of_chart` | at y in the source of a holomorphic φ with Z, W the first a and next b coordinate zero sets, y ∈ U_Z ∩ U_W ∩ U_T: germ_y (𝒯 γ) = germ_y (𝒯 α_T) | `+` from `local-class-product` | `cycle-class-germ` three times (charts split from φ), restriction to V = V_Z ∩ V_W ∩ V_T, `chartNormalProjectionCoclass_eq_relCup2`, upstream `supportRelativeCohomologyGerm_eq_of_restrict_eq` |
| 6 | `normalization_eq_coclassSection_of_product` | N_T γ = upstream's normalized coclass section of T | none | `normalization_singular`, `coclassSection_eq_singular`, Mathlib `TopCat.Presheaf.section_ext` on U_T, upstream `supportRelativeCohomologyGerm_restrict`; off T upstream `supportRelativeCohomologyGerm_eq_zero_of_not_mem`, on T the row above with φ from `htr` |
| 6 | `eq_supportedInjectiveClass_of_product` | γ = α_T | none | upstream `cycleComponentSupportedInjectiveClass_unique` (`Other`) |
| 7 | `cycleComponentSheafClass_cup_of_transversal` | the rung | (−1)^{(2a)(2b)} = 1, computed by `Even.neg_one_pow` | `SmoothOfRelativeDimension.dim_eq` (d = dim X), γ from surjectivity of Φ_T, the rows above, injectivity of Ψ |

The localization step names its inputs: a section of upstream's sheaf 𝓗^{2(a+b)}_T over U_T is determined by its germs at the points of U_T (Mathlib `TopCat.Presheaf.section_ext`); germs vanish off T (upstream `supportRelativeCohomologyGerm_eq_zero_of_not_mem`, statement library); N_T is an equivalence, so equality of normalized sections gives equality of classes (upstream `cycleComponentSupportedInjectiveClass_unique`, `Other`). Only points of T ∩ U_T need the chart argument, and `htr`, `hxreg`, `hwreg` are used exactly there; `hyU` for T comes from y ∈ U_T in `section_ext`.

### Signs, with their sources

| Sign | Source | Value here |
|---|---|---|
| (−1)^{pq} | `cup_singular_comparison'` (Mathlib's `Ext.comp` is diagrammatic; row "Sheaf–singular comparison Ψ") | p = 2a, q = 2b: 1 |
| local product | `chartNormalProjectionCoclass_eq_relCup2` (`local-class-product`; pairing of the model product with `orient a b` is 1, computed) | + |
| chart choice | `cycle-class-germ` holds for every holomorphic adapted chart (`exists_open_chartNormalProjectionCoclass_eq`), so the normal coordinate order of the split charts does not enter | none |
| pair maps | `unionComplIso`, `chartUnionIso`, `ofSubsetIsoNeighborhoodTop`, `restrictToNeighborhood`: identity or inclusion on points | none |
| factor order | `relCup2 (Φ_Z α_Z) (Φ_W α_W)` matches `cup [Z] [W]` through `cup_singular_comparison'` with x = [Z], y = [W] | none |

### Deviations from the plan, and why

1. No definition `Φ_T⁻¹ (relCup2 …)`. A `def` applying `(supportedEquivPair X T n).symm` elaborated, but `AddEquiv.apply_symm_apply` on it hit `maximum recursion depth`. The route takes γ from `(supportedEquivPair X T n).surjective` instead and states every step for any γ with `hγ`; the statements are unchanged in content.
2. The point-form seam (T a point read from upstream's point normalization) is not used: `cycle-class-germ` applies at T in every codimension, so the general theorem covers the point case through the same chart route.
3. `rw` across hypotheses or lemmas whose sides are coercions of upstream `AddEquiv`s (`supportedEquivPair`, Ψ) timed out in keyed matching; `congrArg`, `Eq.trans` and `convert … using 2` replace those rewrites. Rewrites on `relativeCohomologyMap` terms work.

### Timing

`lake env lean HodgeLadder/Cycle/Multiplicative.lean`: about 96 s wall, default heartbeats. Most of it is kernel type checking: each declaration whose statement applies `supportedEquivPair` costs 9 to 18 s in the kernel (also with a one-line `rfl` body), measured with `set_option profiler true`; the elaborator side is under 5 s in total.

### Red-team changes (final pass), as implemented

| Change | Where it is now |
|---|---|
| A: `cycle-class-multiplicative-p2` from scratch RT2 | `HodgeLadder/Tests/CycleClassMultiplicativeP2.lean`, ledger `checked` |
| B: root import, ledger `checked` with the 20 declarations, roadmap row | `HodgeLadder.lean`, `ledger/ladder.json`, `docs/roadmap.md` |
| C: `depends_on` without the general-V rungs, corrected note | ledger |
| D: sign-visible tests next (`cycle-class-multiplicative-codim-zero`, `p2-point-class-nonzero`, `cup-positive-degree-test-p2`) | roadmap "Order of attack", ledger note |
| E: register rows cited in the main theorem's docstring | `HodgeLadder/Cycle/Multiplicative.lean` |
| F: `cycle-class-multiplicative-no-reg`, `cycle-class-multiplicative-generic` | ledger (statements in their notes), roadmap |
| G: drift list below; rebased on `main` with this sketch merged by hand | this section |

Conventions row "Transversal product of cycle classes" (added by the red team) records the sign chain.

### Stronger forms and the next case

- `cycle-class-multiplicative-no-reg` (open): the theorem without `hxreg`, `hwreg`, through `analytic-smooth-locus`.
- `cycle-class-multiplicative-generic` (open): transversality only at the generic point of T; the germ route does not reach points of T where Z or W is singular.
- Future rung, not yet in the ledger: several components, [Z] ∪ [W] = Σᵢ [Tᵢ] when Z(ℂ) ∩ W(ℂ) is a disjoint union of the Tᵢ(ℂ), each meeting the hypotheses of this rung (first case: a line and a conic in ℙ²). `cup_forgetSupport_of_product` is stated for any γ and carries over; the localization step needs one supported class per component and the splitting of H_{∪Tᵢ} into the H_{Tᵢ}.

### Vacuity and sign visibility

- At a = b = 0 the hypotheses hold on every X, with `hxreg` from `cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top` (rung `cycle-class-multiplicative-codim-zero`, checked). In positive codimension they hold on ℙ² (`p2-lines-transversal`, used by `cycle-class-multiplicative-p2`).
- The sign + is visible only where [T] ≠ 0. `cycle-class-multiplicative-codim-zero` (checked) detects only a sign that is −1 at a = b = 0. At a = b = 1, `p2-point-class-nonzero` gives [pt] ≠ 0 and `cup-positive-degree-test-p2` gives [L₀] ∪ [L₁] ≠ 0, which −[pt] also satisfies; so the main theorem's proof computes the sign there and no independent test confirms it. Proposed: `cycle-class-sign-test-p2` (open).
- The general lemma `cup_forgetSupport_of_product` keeps the sign (−1)^{pq} for every p, q; the main theorem uses it only in even degrees.

### Drift list (final red team, section 8)

For the next pin bump, besides the lists above:

- Statement library: `cycleComponentSheafClass`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSmoothSupportCoclassSection`, `cycleComponentAnalyticClosedSupport`, `cycleComponentSmoothSupportAmbientOpen`, `supportRelativeCohomologyGerm` with `_eq_of_restrict_eq`, `_eq_zero_of_not_mem`, `_restrict`, `chartNormalProjectionCoclass` and `chartNormalProjectionCoclass_restrict`, `neighborhoodSupportInclusionPairMap` and `_comp`, `neighborhoodSupportComplementPair`, `openParacompactSpace`, `SmoothOfRelativeDimension.dim_eq`, and the charted structure (`localChart`, `isManifold_omega`).
- `Other` (unguarded): `cycleComponentSupportedInjectiveClass_unique`, `cycleComponentSupportedInjectiveClass_normalization`, `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, `rationalCohomologyAddEquivSingularCohomology`.
- Mathlib: `TopCat.Presheaf.section_ext`, `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`, `LinearEquiv.funCongrLeft`, `LinearEquiv.sumArrowLequivProdArrow`, the meaning of `ω` in `WithTop ℕ∞`.

## p2-point-class-nonzero: statement

Date: 2026-11-26. Checked. Statement fixed and proved in the same session; the red team passed it with changes 1 to 4 (`docs/sketches/p2-point-class-nonzero.redteam.md`), all implemented; imported from `HodgeLadder.lean`. File `HodgeLadder/Tests/ProjectivePlanePoint.lean`, module `HodgeLadder.Tests.ProjectivePlanePoint`, next to `ProjectivePlaneLines`; the ledger's derived `file` hint `HodgeLadder/P2/Point/Class/Nonzero.lean` is superseded. Imports: `HodgeLadder.Tests.ProjectivePlaneLines`, `HodgeLadder.Tests.ClassNonzero`, `HodgeLadder.Tests.ContractibleAcyclic`, the port's `LefschetzPort.Oka.Topology.Sheaves.Cohomology.Dimension` (Mayer–Vietoris), Mathlib's `Analysis.Complex.Convex` and `Analysis.Convex.Contractible`. No `Other` module beyond those `ClassNonzero` and `ContractibleAcyclic` already import. `lake env lean` on the file: 20 s wall, default heartbeats.

### The rung

```lean
theorem projectivePlane_point_class_ne_zero :
    cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin ≠ 0
```

The class lives in `H^(2 * 2)(projectivePlane; ℚ)`; `planeOrigin` and `coheight_planeOrigin` are the ones of `p2-lines-transversal`, so `cup-positive-degree-test-p2` reads this lemma against the right side of `cycle-class-multiplicative-p2` with no transport.

### Route chosen, and why

Candidates (b) and (c) of the brief are closed at the pin. Upstream's nonvanishing results for cycle classes (`cycleComponentSmoothSupportCoclassSection_ne_zero`, `cycleComponentSheafClass_genericPoint_ne_zero`) stop at the supported class or at codimension zero; there is no degree map H⁴ → ℚ and no global fundamental class of X(ℂ) (`integralCompactificationFundamentalClass` in `Other` takes its existence and uniqueness as a hypothesis, and nothing at the pin discharges it for a compact X). A local restriction cannot detect a class of top degree. So the route is (a), the note's route, with one change: the ladder compares `Sheaf.H'` with singular cohomology only on contractible opens (`contractible-open-acyclic`), so the retraction of ℙ²(ℂ) ∖ pt onto a line is replaced by three Mayer–Vietoris steps whose pieces are all star-convex in a standard chart. Mathlib has the Mayer–Vietoris sequence for `Sheaf.H'`, and the port has its vanishing form `TopCat.Sheaf.subsingleton_H'_sup` and `TopCat.Sheaf.subsingleton_H'_bot` (H'(∅) = 0).

| Step | Open | Cover | Pieces |
|---|---|---|---|
| H³ = 0 | U = ℙ²(ℂ) ∖ [0 : 0 : 1] | {x₀ ≠ 0} ∪ {x₁ ≠ 0} (`planeOrigin_support_compl`) | two copies of ℂ²; intersection {v₀ ≠ 0} ≅ ℂ* × ℂ in the chart x₀ ≠ 0 (`planeChartOpen_zero_inf_one`) |
| H² = 0 | {v₀ ≠ 0} | v₀ ∉ (−∞, 0] and v₀ ∉ [0, ∞) (`chartSlitPos_union_chartSlitNeg`) | star-convex about (1, 1), (−1, −1); intersection {Im v₀ ≠ 0} (`chartSlitPos_inter_chartSlitNeg`) |
| H¹ = 0 | {Im v₀ ≠ 0} | Im v₀ > 0 and Im v₀ < 0 | convex; disjoint (`chartHalfPos_inter_chartHalfNeg`), and H⁰(∅) = 0 |

Contractible pieces have no rational cohomology in positive degrees (`contractibleOpen_subsingleton_H'`, rung `contractible-open-acyclic`). The class step is the codimension-two copy of `cycleComponentSheafClass_ne_zero_of_subsingleton`: `cycleComponentSheafClass_eq_forgetSupport`, `forgetSupport_injective_of_subsingleton` at n = 3 (the degrees 2 * 2 and 3 + 1 agree by evaluation), and upstream's normalization isomorphism with `cycleComponentSmoothSupportCoclassSection_ne_zero`.

### The statements

```lean
theorem cycleComponentSheafClass_ne_zero_of_subsingleton_three (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (hx : coheight x = ((2 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 3 (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0

theorem subsingleton_H'_three_compl_planeOrigin :
    Subsingleton (Sheaf.H' planeConst 3
      (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin).compl)

theorem planeOrigin_support_compl :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin).compl =
      planeChartOpen 0 ⊔ planeChartOpen 1

theorem planeChartOpen_zero_inf_one :
    planeChartOpen 0 ⊓ planeChartOpen 1 =
      planeChartZeroOpen {v | v 0 ≠ 0} (isOpen_ne_fun (continuous_apply 0) continuous_const)

theorem contractibleSpace_planeChartOpen (i : Fin 3) : ContractibleSpace (planeChartOpen i)

theorem contractibleSpace_planeChartZeroOpen (S : Set (Fin 2 → ℂ)) (hS : IsOpen S)
    {c : Fin 2 → ℂ} (hc : StarConvex ℝ c S) (hne : S.Nonempty) :
    ContractibleSpace (planeChartZeroOpen S hS)
```

`planeConst` is the rational constant sheaf on ℙ²(ℂ) in the spelling of `forget-support-exact`; `planeChartOpen i` is the source of `projectiveChart 2 i`; `planeChartZeroOpen S hS` is the part of the chart x₀ ≠ 0 (coordinates (x₁ / x₀, x₂ / x₀)) over an open S ⊆ ℂ². The criterion is stated for every smooth projective integral X, so `p1p1-point-class-nonzero` can use it once H³ of the complement of (∞, ∞) is known. Change 4 of the red team: `cycleComponentSheafClass_ne_zero_of_subsingleton_odd` (coheight p + 1, H^{2p+1} of the complement) is the general form; the codimension-two criterion is its case p = 1 by term, and the codimension-one criterion of `projective-line-class-nonzero` is its case p = 0 (an `example` in the file; `ClassNonzero.lean` is unchanged). Listed in `docs/gaps.md`, "General lemmas kept local".

### What is proved

Everything; every declaration in the file prints `propext`, `Classical.choice`, `Quot.sound`. Helpers: `mem_projectiveChart_source_iff` (the copy of `mem_projectiveChart_two_source_iff` for every i), `mem_projectiveChart_source_iff_of_mem` (a point of the chart xᵢ ≠ 0 lies in xⱼ ≠ 0 iff coordinate j of `Fin.insertNth i 1 (φᵢ z)` is nonzero, from `projectiveChart_symm_mem_U_iff`), `contractibleSpace_of_starConvex_image` (Mathlib's `homeomorphOfImageSubsetSource` with `StarConvex.contractibleSpace`), the four sets `chartSlitPos`, `chartSlitNeg`, `chartHalfPos`, `chartHalfNeg` with openness, star-convexity and their union and intersection identities, and the lattice lemmas `planeChartZeroOpen_inf`, `_sup`, `_empty`, `_congr`. The cover lemma uses `planeOrigin_support_eq_singleton` and `exists_mem_U`: a point outside x₀ ≠ 0 and x₁ ≠ 0 lies in the chart x₂ ≠ 0 with both coordinates zero.

### Failed trivial proofs

Scratch file inside the worktree, deleted. On the rung: `simp` (unsolved goals), `decide` (no `Decidable` instance), `aesop` (fails after exhaustive search), `exact?` (heartbeat limit 200000 reached at `isDefEq`). On the H³ vanishing: `infer_instance` fails.

### For the red team

(1) Vacuity: the statement has no hypotheses, and the proof goes through upstream's own supported class and normalization isomorphism, so a degenerate H⁴ cannot make it hold. (2) No sign or normalization enters: the statement is a nonvanishing, and the scalar in front of [pt] is not computed here (that is `cycle-class-multiplicative-p2`). (3) Drift: the proof reads `cycleComponentSheafClass_eq_forgetSupport` (an `rfl` upstream) and the `Other` normalization lemmas that `projective-line-class-nonzero` already uses; no upstream declaration beyond those. (4) The route differs from the note (Mayer–Vietoris in place of a retraction onto a line); the ledger note should say so when the rung is marked.

### cup-positive-degree-test-p2, as checked

Module `HodgeLadder.Tests.CupPositiveDegreeP2`, imported from `HodgeLadder.lean`.

```lean
theorem planeLines_cup_ne_zero :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) ≠ 0

theorem cup_ne_zero_of_positive_degree :
    ∃ (α β : H^2(projectivePlane; ℚ)), HodgeLadder.Cup.cup α β 4 rfl ≠ 0
```

The proof rewrites with `planeLines_cup_eq_planeOrigin` and closes with `projectivePlane_point_class_ne_zero`; the right side of the equality carries the coheight proof `coheight_planeOrigin_add`, and the two classes agree by proof irrelevance and evaluation of `2 * (1 + 1)`. What it rules out: the square-zero product, which satisfies every checked ring law of `cup` and vanishes on classes of positive degree. What it does not test: the sign of [L₀] ∪ [L₁] = [pt] (−[pt] is also nonzero); that sign is the content of `cycle-class-multiplicative`.

## cycle-class-multiplicative-codim-zero: statement

Date: 2026-11-26. Checked. Statement elaborated with `sorry` bodies first; every body then proved in the same session, so the rung came out short. Red team: pass with changes 1 to 7 (`docs/sketches/cycle-class-multiplicative-codim-zero.redteam.md`), all implemented, with one correction to its text (the ℙ² instance does not test the odd signs; see "Two routes, and sign visibility"). Imported from `HodgeLadder.lean`. File `HodgeLadder/Tests/CycleClassMultiplicativeCodimZero.lean`, module `HodgeLadder.Tests.CycleClassMultiplicativeCodimZero`, next to `FundamentalClassUnit` and `CycleClassMultiplicativeP2`; the ledger's derived `file` hint `HodgeLadder/Cycle/Class/Multiplicative/Codim/Zero.lean` is superseded. Imports: `HodgeLadder.Cycle.Multiplicative`, `HodgeLadder.Tests.FundamentalClassUnit` (for `exists_cycleComponentSheafClass_genericPoint_eq_smul_one` and `exists_mem_cycleComponentSmoothSupportAmbientOpen`, both upstream inputs only) and upstream `Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison` (already built). `lake env lean` on the file: 27 to 40 s wall, default heartbeats; 5 s for the first seven declarations before the `FundamentalClassUnit` import was added.

### The rung

```lean
theorem cycleComponentSheafClass_genericPoint_cup_self (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cup (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X))
        (2 * (0 + 0)) (by ring) =
      cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero_add_zero X)
```

This is `cycleComponentSheafClass_cup_of_transversal` at x = w = t = η (the generic point), a = b = 0, `d := dim X.left`. No `SmoothOfRelativeDimension` hypothesis is needed: upstream's instance `SmoothOfRelativeDimension.of_isIntegral` supplies `dim X.left`. The degree is the one the main theorem produces, `2 * (0 + 0)`; `ht` is stated as `↑0 + ↑0` (`coheight_genericPoint_eq_zero_add_zero`, by `rfl` after upstream's `coheight_genericPoint_eq_zero`), as in `coheight_planeOrigin_add`.

### The missing lemma, proved

```lean
theorem cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSmoothSupportAmbientOpen X (genericPoint X.left) = ⊤
```

Route, 20 lines: `closure {η} = X` (Mathlib `genericPoint_closure`), so the vanishing ideal in upstream's `cycleComponent` is `vanishingIdeal ⊤ = X.nilradical = ⊥` on the reduced `X` (Mathlib `vanishingIdeal_top`, `nilradical_eq_bot`); by `isIso_subschemeι_iff_eq_bot` the closed immersion `cycleComponentι X.left η` is an isomorphism (`isIso_cycleComponentι_genericPoint`, needs only `IsIntegral`); its composite with `X.hom` is smooth by instance search, so the smooth locus is `⊤` (`Scheme.Hom.smoothLocus_eq_top`), upstream's `cycleComponentSingularClosedFiltration X η 0` is `⊥`, its image and complex-point preimage are empty, and the complement is `⊤`.

### The hypotheses

| Hypothesis | Declaration | Content |
|---|---|---|
| `hx`, `hw` | upstream `coheight_genericPoint_eq_zero` | coheight 0 |
| `ht` | `coheight_genericPoint_eq_zero_add_zero` | the form `↑0 + ↑0` |
| `hd` | `Nat.zero_le _` | 0 + 0 ≤ dim X |
| `hT` | `genericPoint_support_eq_inter` | `Set.inter_self`; holds for any x = w = t |
| `hxreg`, `hwreg` | `genericPoint_support_subset_smoothSupportAmbientOpen` | the missing lemma |
| `htr` | `genericPoint_transversal X d` | `chartAt y`, Mathlib `IsManifold.chart_mem_maximalAtlas`, `mem_chart_source`; both supports are `⊤` (upstream `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`) and the conditions over `Fin 0` are empty |

What the instance tests: the maximal-atlas membership of upstream's charts, `hxreg` (the missing lemma) and the conclusion of the main theorem. It does not test the coordinate conditions of `htr` or a proper intersection in `hT`; those are tested by `cycle-class-multiplicative-p2`.

### Two routes, and sign visibility

`fundamental-class-unit` proves [X] = 1 by evaluating the degree-0 chart coclass on upstream's standard local class (`forgetRel_chartNormalProjectionCoclass_zero`); with `one_cup` that gives [X] ∪ [X] = [X] at once. The rung reaches the same identity through the transversal theorem, sharing `cycle-class-germ`, Ψ and `[X] = c • 1` with `fundamental-class-unit` (relative cup, `local-class-product` at a = b = 0, uniqueness of supported classes). The import closure of `HodgeLadder.Cycle.Multiplicative` does not contain `HodgeLadder.Tests.FundamentalClassUnit`. The routes share `transport_supportedClass_eq_chartNormalProjectionCoclass`, `cup_singular_comparison`, `one_cup`, `exists_cycleComponentSheafClass_genericPoint_eq_smul_one` and `exists_mem_cycleComponentSmoothSupportAmbientOpen` (red team, constant closure); they differ only in the last step: evaluation of the degree-0 coclass, against its idempotence under `relCup2`. A defect in the shared inputs would enter both, so their agreement is evidence about the last step only. The file also proves the converse direction:

- `cup_smul_one_smul_one X c e`: (c • 1) ∪ (e • 1) = (c e) • 1 in degree `2 * (0 + 0)`, from `add_cup`, `cup_add` (so `map_rat_smul`) and `one_cup`.
- `cycleComponentSheafClass_genericPoint_eq_one_of_cup_self`: [X] = 1, from the rung, [X] = c • 1 with c ≠ 0 (upstream: H⁰ is a line, [X] ≠ 0) and c² = c. It does not use `cycleComponentSheafClass_genericPoint_eq_one` or `forgetRel_chartNormalProjectionCoclass_zero`; it still uses `cycle-class-germ` through the transversal theorem.
- `cycleComponentSheafClass_genericPoint_cup_self_ne_neg` (change 5): [X] ∪ [X] ≠ −[X], from the rung and upstream's `cycleComponentSheafClass_genericPoint_ne_zero` alone.

So the codimension-zero instance is sign-visible for a sign constant in (a, b): if the transversal theorem carried a fixed sign ε = ±1, the same argument would give c² = ε c, so [X] = ε · 1, and [X] = −1 is excluded by `cycleComponentSheafClass_genericPoint_ne_neg_one`. Signs that equal 1 at a = b = 0, such as (−1)^{ab} or (−1)^a, are invisible here. The red team's verdict says `cycle-class-multiplicative-p2` with `p2-point-class-nonzero` tests them; that is corrected here: `cup-positive-degree-test-p2` shows only [L₀] ∪ [L₁] ≠ 0, which −[pt] also satisfies, so no current test detects a sign at a = b = 1. The main theorem's proof computes the sign, and no independent test confirms it. The test that would is rung `cycle-class-sign-test-p2` (open): a degree map H⁴(ℙ²; ℚ) → ℚ with deg [pt] = 1 computed from upstream's point-class normalization, independently of the multiplicativity proof. Both sides of the rung are nonzero: upstream `cycleComponentSheafClass_genericPoint_ne_zero` elaborates against the right-hand side with the `↑0 + ↑0` coheight proof as well.

### Trivial proofs, all fail

On the missing lemma: `rfl` (the sides do not unfold to each other), `simp` (no progress), `simp [cycleComponentSmoothSupportAmbientOpen, cycleComponentSingularAnalyticClosedFiltration]` (unsolved goal). On the rung: `rfl`, `simp` (unsolved goal), `Subsingleton.elim _ _` (no `Subsingleton` instance on H⁰).

### Axioms

`#print axioms` on all ten declarations (`tools/check.py`, and the red team's RT1 on the first nine): `propext`, `Classical.choice`, `Quot.sound`. The file has no `sorry`.

### Kept local

`isIso_cycleComponentι_genericPoint` and `cycleComponentSmoothSupportAmbientOpen_genericPoint_eq_top` are statement-level facts about upstream's `cycleComponent` at the generic point; by decision 0011 they stay here, listed in `docs/gaps.md`, "General lemmas kept local".

### Drift list (red team, section 8)

For the next pin bump: statement library `cycleComponent`, `cycleComponentι` (their `vanishingIdeal`/`subschemeι` bodies, unfolded by `change`), `cycleComponentSingularClosedFiltration` at k = 0, `cycleComponentSmoothSupportAmbientOpen` (unfolded by `change`), `SmoothOfRelativeDimension.of_isIntegral`; `Other`: `coheight_genericPoint_eq_zero`, `cycleComponentAnalyticClosedSupport_genericPoint_eq_top`, `cycleComponentSheafClass_genericPoint_ne_zero`; Mathlib: `Scheme.isIso_subschemeι_iff_eq_bot`, `Scheme.IdealSheafData.vanishingIdeal_top`, `Scheme.nilradical_eq_bot`, `Scheme.Hom.smoothLocus_eq_top`, `genericPoint_closure`. A change to the body of `cycleComponent` or of the smooth ambient open breaks the `change` steps, so drift there breaks the build.

## analytic-smooth-locus: statement

Date: 2026-11-26. Statement fixed and elaborated, route mapped, sub-rungs stated. Statement red team: pass with changes (`docs/sketches/analytic-smooth-locus.redteam.md`); the statement stands, route R2 goes first, and changes A to J are applied to the ledger, this section, `docs/references.md` and `docs/gaps.md`. The statement file was elaborated in a worktree as `HodgeLadder/Normalization/AnalyticSmoothLocus.lean` (single import `HodgeLadder.Normalization.Germ`, about 18 s, five open bodies) and removed before merging, since its bodies are open and the checker's sorry scan covers every file in the tree. Its exact text is kept below ("The statement file, as elaborated") and is the record until a prover lands it. The ledger's derived hint `HodgeLadder/Analytic/Smooth/Locus.lean` is superseded.

Notation as in "cycle-class-germ: statement": Z = `cycleComponentAnalyticClosedSupport X x`, U = `cycleComponentSmoothSupportAmbientOpen X x` = X(ℂ) ∖ Z_sing(ℂ), d = `dim X.left`, I the vanishing ideal of `closure {x}` (upstream's `cycleComponent` is the reduced closure).

### The rung

```lean
theorem source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    e.source ∩ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x
```

The binders `x`, `hx`, `E`, `e`, `L`, `he`, `hS` are those of `transport_supportedClass_eq_chartNormalProjectionCoclass`, unchanged. `hx` is kept although the inclusion is true without it: the chart forces the analytic codimension p, and identifying it with the coheight is a further comparison the route avoids by assuming it. The conclusion is an inclusion; as an identity it reads e.source ∩ Z = e.source ∩ Z ∩ U, with no extra content. Off Z the inclusion is upstream's `cycleComponentSupportComplement_le_smoothAmbientOpen` (helper `mem_smoothSupportAmbientOpen_of_not_mem`). `exact?` on the statement finds only the rung; `simp_all [cycleComponentSingularAnalyticClosedFiltration]` leaves `y.underlying ∉ cycleComponentSingularAmbientClosedFiltration X x 0`.

Literature: a point of a reduced complex algebraic variety at which the analytic space is a complex manifold of the right dimension is a regular point [`Serre1956` §2 for the comparison of local rings; the regularity statement in this form unverified]. Topology alone cannot give it: the cusp y² = x³ is a topological manifold at 0 and singular there, and its set is not a holomorphic submanifold. The holomorphy hypothesis `he` carries the content.

### The corollary: `cycle-class-germ` without `hyU`, proved from the rung

`transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`: the statement of `transport_supportedClass_eq_chartNormalProjectionCoclass` with the binder `hyU` deleted, nothing else changed. In the statement file it is proved in 6 lines from the rung (for y ∈ Z) and the helper (for y ∉ Z), then the checked theorem. After the red team it moves to rung `cycle-class-germ-no-reg`, proved there by route R2 from the stronger source form `transport_supportedClass_eq_chartNormalProjectionCoclass_source` (the identity on W = e.source), without the rung; the red team's change C has the exact text, elaborated against `HodgeLadder.Normalization.Germ`, and its planned module is `HodgeLadder/Normalization/GermNoReg.lean`.

### Inputs at the pin

| Input | Where | Status |
|---|---|---|
| regular functions are holomorphic in upstream's charts | upstream `analyticAt_localChart_symm_evaluate`; `chartAt = localChart X d` by `rfl` | at the pin |
| a function vanishing on Z evaluates to 0 on Z(ℂ); its germ lies in m_y | upstream `Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero`, Mathlib `Scheme.mem_basicOpen` | proved here (`evaluate_eq_zero_of_vanishes`, `germ_mem_maximalIdeal_of_vanishes`) |
| Jacobian criterion for a local algebra | Mathlib `Algebra.FormallySmooth.iff_injective_lTensor_residueField`, `iff_injective_cotangentComplexBaseChange_residueField` | at the pin |
| dimension of local rings of a smooth integral X, height plus coheight | upstream `SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed`, `IsAffineOpen.primeIdealOf_height_eq_coheight`, `orderKrullDim_eq_complex` | at the pin, for integral smooth schemes |
| smooth local ℂ-algebra is a domain (or: regular local ring is a domain) | | missing in Mathlib (`IsRegularLocalRing` is defined; neither implication is there) |
| the local ring of Z at y as a quotient of Γ(V)/I(V) | the recipe of `cycleComponent_planeLine_mem_smoothLocus` (`p2-lines-transversal`, steps 1 and 2) | at the pin, as a proof pattern |
| analytic local ring ℂ{z}, Noetherian; Weierstrass preparation for convergent series; Rückert Nullstellensatz | | missing; Mathlib has only the formal `PowerSeries` Weierstrass preparation |
| excellence; completion of a reduced local ring of finite type is reduced | | missing |
| comparison of algebraic and analytic completions at a point | [`Serre1956`] | missing |

### Route R1 (Jacobian), as sub-rungs, smallest first

The cheapest sound route for the rung is the Jacobian criterion. In the étale chart Z is cut out by its normal coordinates; if p regular functions vanishing on Z have independent differentials at y, the subscheme they cut out is smooth of dimension d − p at y, contains Z, and has the same dimension, so it is Z near y. The step from "Z(ℂ) is a holomorphic submanifold" to "such functions exist" is the analytic input, and it does not reduce to the pin.

| # | Lean name | Statement (exact text in the file) | Kind | Size and status |
|---|---|---|---|---|
| 3a | `linearIndependent_cotangent_of_linearIndependent_chartDerivative` | if the chart differentials `chartDerivative X V (f i) y` are ℂ-independent, the classes of the germs in m_y/m_y² are independent over the residue field | elementary | about 150 lines: m_y² has zero differential (product rule on representatives), `evaluate_res`, residue field ≅ ℂ at a ℂ-point; only this direction is needed |
| 3b | `mem_smoothSupportAmbientOpen_of_linearIndependent_cotangent` | p = codim Z functions vanishing on Z with independent cotangent classes at y ∈ Z give y ∈ U | algebraic | several hundred lines; needs "smooth local ℂ-algebra is a domain", missing in Mathlib |
| 3 | `mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative` | 3a then 3b | | proved from 3a, 3b; ledger rung `jacobian-smooth-point` (3a, 3b, 3) |
| 2 | `exists_linearIndependent_chartDerivative_of_norm_le` | if ‖(e z).2‖ ≤ C ∑ ‖g_j(z)‖ near y and g_j(y) = 0, some p of the g_j have independent chart differentials | elementary | 150 to 250 lines: along t ↦ y + t h with h ∈ ⋂ ker dg_j(y), ‖n‖ = o(t), so h ∈ ker dn(y); dn(y) has rank p by `he` |
| 1 | `exists_norm_normalCoordinate_le` | near y ∈ e.source ∩ Z there are an open V ∋ y, regular g_j on V vanishing on Z and C with ‖(e z).2‖ ≤ C ∑ ‖g_j(z)‖ | deep | not at the pin; ledger rung `analytic-normal-bound` (1 with 2, since 2 has no use without 1) |
| rung | `source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen` | 1, then 2, then 3 | | proved from 1, 2, 3 |
| rung, source form | `source_subset_smoothSupportAmbientOpen` | e.source ⊆ U (change F) | | proved from the rung and the helper |

Sub-rung 1 is a Łojasiewicz inequality with exponent one: the algebraic ideal controls the distance to Z linearly. Given 2 and 3 it is equivalent to the rung, so it carries all of the analytic content. The form is the weakest that 2 consumes: no holomorphy of coefficients, no common generators, only a bound. Its proof in the literature: I·𝒪^an_y is radical (the local ring of X at y is excellent, so the completion of the reduced local ring of Z is reduced, and 𝒪^an_{Z,y} injects into it), its zero set is the germ {n = 0}, so by Rückert's Nullstellensatz it equals (n_1, …, n_p); writing n_k = ∑ a_kj g_j with a_kj holomorphic gives the bound [`Serre1956` for the completions; excellence and the Nullstellensatz unverified, no key in `docs/references.md`]. Each ingredient is a foundation project missing from Mathlib. An elimination proof (finite projection to ℂ^{d−p+1}, minimal polynomial with a simple root along Z) avoids excellence but needs local Noether normalization, finiteness on ℂ-points and continuity of roots; it is no cheaper.

### Route R2 (purity), for the consumers of the rung

The rung's consumers need only the corollary: `cycle-class-multiplicative-no-reg` uses `hxreg`, `hwreg` only through `restrict_eq_chartNormalProjectionCoclass` (line 436 of `HodgeLadder/Cycle/Multiplicative.lean`), which wraps `cycle-class-germ` at y ∈ T ∩ U_T. The corollary has a topological proof that avoids the rung:

1. `singularBoundarySectionCohomology_isZero_of_lt` (stated, open body): for every open V of X(ℂ), cohomology of V with supports in Z_sing(ℂ) vanishes below degree 2(p + 1). Upstream proves it at V = ⊤ (private `cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`), and ⊤ enters only as the evaluation open (red team, finding 6):

   | Upstream lemma | Open | Change for V |
   |---|---|---|
   | `finiteNestedSupport_homology_isZero` (`FiniteFiltrationVanishing.lean:122`) | conclusion at `supportEvaluation X ⊤`; base case `supportedSections_top_homology_isZero X ⊤ K n`, which already takes any `W` | replace ⊤ by V; layer hypothesis on `V ⊓ O (k + 1)` |
   | `nestedSupportRestriction_middle_homology_isZero` (same file, line 100) | uses `nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K`, which takes any `W`, and its short exactness, which takes any `W` | replace ⊤ by V |
   | `nestedSupportRestrictionLastComplexIso` (`NestedOnOpen.lean:152`) | the only ⊤-specific piece: identifies X₃ at ⊤ with sections on U vanishing on V | a version at W: X₃ at W is `ker(K(W ⊓ U) → K(W ⊓ V))` by `sheafSectionsBetweenOpensOnOpenIso X h W F`, then `sheafSectionsSupportedOutsideOnOpenIso` at `W ⊓ U`; the same for `nestedSupportRestrictionLastComplexIso_g` |
   | `cycleComponentSingularLayerSectionCohomology_isZero_of_lt` (`LocalSupportVanishing.lean:136`) | on `O (k + 1)`, through `sectionCohomology_isZero_of_cofinal_lower_vanishing`, which holds on any open | the same lemma on `V ⊓ O (k + 1)`; the local input `cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing` needs only `y ∉ S_{k+1}` |

   A fixed V suffices for the induction. Fallback: run upstream's general-space lemmas on `TopCat.of V` with the restricted complex (flasque by `openSheafRestriction_isFlasque`) and identify supported sections on `⊤_V` with those on V.
2. `restrict_smoothSupportAmbientOpen_injective` (change C): on every open V, the support sequence Z_sing ⊆ Z gives H^{2p}_Z(V) ↪ H^{2p}_Z(V ⊓ U) from step 1 at n = 2p, transported to singular relative cohomology by naturality of `complexSupportInjectiveSectionCohomologyEquiv`.
3. On V ∩ U the lower cohomology sheaves with supports in Z vanish (upstream `cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing`), so H^{2p}_Z(V ∩ U) is the sections of the sheaf 𝓗^{2p}_Z (`TopCat.Sheaf.lowestSectionCohomologyIso`); a section whose germs vanish is zero.
4. The difference of the two sides of `cycle-class-germ` on V has zero germs on V ∩ U by the checked theorem, so it is zero on V. This gives the corollary with W = e.source, stronger than the germ form.

R2 uses only upstream's sheaf machinery and the checked `cycle-class-germ`. Red team estimate: 350 to 650 lines (purity on V 150 to 250, injectivity 100 to 200, the section argument and assembly 100 to 200); the main risk is the `W`-version of `nestedSupportRestrictionLastComplexIso_g`, with the `TopCat.of V` fallback. Ledger rung `cycle-class-germ-no-reg`.

### Decision, as applied (red team changes B, D, E, G)

- `analytic-smooth-locus` stays `open`; "needs split" is recorded in its note (it is not a ledger status). `depends_on`: `jacobian-smooth-point` (sub-rung 3) and `analytic-normal-bound` (sub-rungs 1 and 2). The rung is a three-line assembly of them and has no consumer on the ladder.
- Kill criterion (change D): mark `analytic-smooth-locus` dead when `cycle-class-germ-no-reg` and `jacobian-smooth-point` are checked, unless the pinned Mathlib then has the ring of convergent power series in n variables as a Noetherian local ring with Weierstrass preparation; a revival takes a new id.
- New rung `cycle-class-germ-no-reg` (route R2, depends on `cycle-class-germ` only). `cycle-class-multiplicative-no-reg` now depends on it in place of `analytic-smooth-locus`.
- Optional test rung `p2-cusp-singular-point` (red team section 7b): a component of ℙ² with a singular complex point, so that U = ⊤ fails for some component.
- Order: `cycle-class-germ-no-reg`, then `cycle-class-multiplicative-no-reg` (mechanical, red team finding 8), then optionally `jacobian-smooth-point`, whose 3b waits on "a regular local ring is a domain" in Mathlib; `analytic-normal-bound` is parked.
- Sub-rung 3 is useful alone: it turns `hxreg`-type hypotheses into a computation of p differentials, which `p2-lines-transversal` now proves by identifying the quotient ring by hand.

### What was proved in the statement file

`mem_smoothSupportAmbientOpen_of_not_mem`, `evaluate_eq_zero_of_vanishes`, `germ_mem_maximalIdeal_of_vanishes` (helpers, no `sorry`); the assemblies `mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative`, `source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen`, `source_subset_smoothSupportAmbientOpen` and the corollary `transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`, each with no `sorry` of its own and inheriting the open sub-rungs. Definition `chartDerivative` (the differential at y in `chartAt y` of a regular function).

### Red team

Pass with changes, `docs/sketches/analytic-smooth-locus.redteam.md`. It confirmed sub-rungs 2, 3a, 3b true as stated (findings 1, 3, 4; 3b needs `hx`), the junk values harmless (finding 5), and route R2 sound with the identity on all of e.source (findings 6, 7). It added the conventions rows "Chart differentials and the Zariski cotangent space" and "Local purity on an open".

### The statement file, as elaborated

Exact text of `HodgeLadder/Normalization/AnalyticSmoothLocus.lean` after change F, elaborated with `lake env lean` at the pin (five open bodies, each marked by the Lean placeholder token; everything else proved). It imports only `HodgeLadder.Normalization.Germ`. Per change A, a prover lands the R2 statements in `HodgeLadder/Normalization/GermNoReg.lean` and keeps the R1 statements here, or on a branch, until they are proved.

```lean
module

public import HodgeLadder.Normalization.Germ

/-!
# Analytic smoothness of `Z` in an adapted holomorphic chart gives `Z_reg`

Rung `analytic-smooth-locus` (red team on `cycle-class-germ`, change G). Phase 1: statements and
route; the sub-rungs have open bodies.

Let `x` be a point of coheight `p` of a smooth integral projective `X` over `ℂ`, with
`Z = cycleComponentAnalyticClosedSupport X x` and `U = cycleComponentSmoothSupportAmbientOpen X x`
(`X(ℂ) ∖ Z_sing(ℂ)`). The rung: for every holomorphic chart `e` of `X(ℂ)` into `E × ℂ^p` in which
`Z` is the zero set of the normal coordinate (the hypotheses `he`, `hS` of
`transport_supportedClass_eq_chartNormalProjectionCoclass`), `e.source ∩ Z ⊆ U`. With it, the
`cycle-class-germ` identity holds without `hyU`.

Route (Jacobian criterion, three sub-rungs; `docs/sketches/cycle-class-multiplicative.md`, section
"analytic-smooth-locus: statement"):

1. `exists_norm_normalCoordinate_le` (deep, not at the pin): near `y ∈ e.source ∩ Z`, finitely
   many regular functions vanishing on `Z` bound the normal coordinate with exponent one,
   `‖(e z).2‖ ≤ C · ∑ ‖g_j(z)‖`. This is the analytic input: the algebraic ideal of `Z`
   generates the ideal of holomorphic germs vanishing on the submanifold `Z ∩ e.source`.
2. `exists_linearIndependent_chartDerivative_of_norm_le` (elementary): such a bound forces `p` of
   the `g_j` to have linearly independent differentials at `y`.
3. `mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative` (algebraic): `p` functions
   vanishing on `Z` with independent differentials at `y` put `y` in `Z_reg`; split into the
   bridge `linearIndependent_cotangent_of_linearIndependent_chartDerivative` (analytic
   differentials to the Zariski cotangent space) and the Jacobian step
   `mem_smoothSupportAmbientOpen_of_linearIndependent_cotangent`.

## Main results

* `HodgeLadder.Normalization.source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen`:
  the rung, assembled from the sub-rungs (proved modulo them).
* `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`:
  `cycle-class-germ` without `hyU` (proved from the rung and the checked `cycle-class-germ`).
* `HodgeLadder.Normalization.singularBoundarySectionCohomology_isZero_of_lt` (open body): local
  purity on every open, the first step of route R2, a topological proof of the corollary that
  does not use the rung.
* `HodgeLadder.Normalization.mem_smoothSupportAmbientOpen_of_not_mem`,
  `HodgeLadder.Normalization.evaluate_eq_zero_of_vanishes`,
  `HodgeLadder.Normalization.germ_mem_maximalIdeal_of_vanishes`: proved helpers.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology.Singular Topology Filter
open scoped Manifold ContDiff

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The differential at `y`, in upstream's chart `chartAt y`, of the evaluation of a regular
function `s` on a Zariski open `V`: the derivative of `w ↦ s((chartAt y)⁻¹ w)` at `chartAt y y`,
a `ℂ`-linear form on `ℂ^d`, `d = dim X`. -/
def chartDerivative (V : X.left.Opens) (s : Γ(X.left, V)) (y : ComplexPoint X) :
    (Fin (dim X.left) → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (fun w => Point.evaluate V s ((chartAt (Fin (dim X.left) → ℂ) y).symm w))
    (chartAt (Fin (dim X.left) → ℂ) y y)

/-- Off `Z` the inclusion is upstream's: `Z_sing(ℂ) ⊆ Z(ℂ)`
(`cycleComponentSupportComplement_le_smoothAmbientOpen`). -/
theorem mem_smoothSupportAmbientOpen_of_not_mem (x : X.left) (y : ComplexPoint X)
    (hy : y ∉ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))) :
    y ∈ cycleComponentSmoothSupportAmbientOpen X x :=
  cycleComponentSupportComplement_le_smoothAmbientOpen X x hy

/-- A regular function vanishing on `closure {x}` (no point of `closure {x}` in its basic open)
evaluates to `0` at every complex point of `Z` inside its open. -/
theorem evaluate_eq_zero_of_vanishes (x : X.left) {V : X.left.Opens} (s : Γ(X.left, V))
    (hs : ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen s) (y : ComplexPoint X)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
    (hyV : y.underlying ∈ V) :
    Point.evaluate V s y = 0 := by
  by_contra h
  exact hs y.underlying hyZ
    ((Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero s y hyV).mpr h)

/-- The germ at `y` of a regular function vanishing on `closure {x}` lies in the maximal ideal of
the stalk. -/
theorem germ_mem_maximalIdeal_of_vanishes (x : X.left) {V : X.left.Opens} (s : Γ(X.left, V))
    (hs : ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen s) (y : ComplexPoint X)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
    (hyV : y.underlying ∈ V) :
    X.left.presheaf.germ V y.underlying hyV s ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk y.underlying) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hs y.underlying hyZ ((X.left.mem_basicOpen s y.underlying hyV).mpr hu)

/-- **Sub-rung 3b, the Jacobian step** (algebraic). If `p = codim Z` regular functions vanishing
on `Z` have linearly independent classes in the Zariski cotangent space `m_y / m_y²` of `X` at a
complex point `y ∈ Z`, then `y ∉ Z_sing`. Route: they cut out a subscheme `Z'` smooth of relative
dimension `d − p` at `y` (Mathlib's `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
on the stalk), whose local ring at `y` is a domain of dimension `d − p` containing `Z`'s, of the
same dimension (`hx`, upstream dimension formulas); so `Z = Z'` near `y`. -/
theorem mem_smoothSupportAmbientOpen_of_linearIndependent_cotangent (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (y : ComplexPoint X)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
    (V : X.left.Opens) (hyV : y.underlying ∈ V) (f : Fin p → Γ(X.left, V))
    (hf : ∀ i, ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen (f i))
    (hind : LinearIndependent (IsLocalRing.ResidueField (X.left.presheaf.stalk y.underlying))
      (fun i => (IsLocalRing.maximalIdeal (X.left.presheaf.stalk y.underlying)).toCotangent
        ⟨X.left.presheaf.germ V y.underlying hyV (f i),
          germ_mem_maximalIdeal_of_vanishes X x (f i) (hf i) y hyZ hyV⟩)) :
    y ∈ cycleComponentSmoothSupportAmbientOpen X x := by
  sorry

/-- **Sub-rung 3a, the bridge** (elementary). The analytic differential at `y` in upstream's
chart, `chartDerivative`, factors through `m_y / m_y²`: a function in `m_y²` has zero
differential (product rule), and germs on smaller opens have the same evaluation
(`Point.evaluate_res`). So independence of the analytic differentials gives independence in the
cotangent space. Only this direction is needed. -/
theorem linearIndependent_cotangent_of_linearIndependent_chartDerivative (x : X.left) {p : ℕ}
    (y : ComplexPoint X)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
    (V : X.left.Opens) (hyV : y.underlying ∈ V) (f : Fin p → Γ(X.left, V))
    (hf : ∀ i, ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen (f i))
    (hind : LinearIndependent ℂ (fun i => chartDerivative X V (f i) y)) :
    LinearIndependent (IsLocalRing.ResidueField (X.left.presheaf.stalk y.underlying))
      (fun i => (IsLocalRing.maximalIdeal (X.left.presheaf.stalk y.underlying)).toCotangent
        ⟨X.left.presheaf.germ V y.underlying hyV (f i),
          germ_mem_maximalIdeal_of_vanishes X x (f i) (hf i) y hyZ hyV⟩) := by
  sorry

/-- **Sub-rung 3**, the Jacobian criterion in analytic form: `p = codim Z` regular functions
vanishing on `Z` whose differentials at `y ∈ Z` in upstream's chart are linearly independent put
`y` in `Z_reg`. Proved from 3a and 3b. -/
theorem mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (y : ComplexPoint X)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
    (V : X.left.Opens) (hyV : y.underlying ∈ V) (f : Fin p → Γ(X.left, V))
    (hf : ∀ i, ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen (f i))
    (hind : LinearIndependent ℂ (fun i => chartDerivative X V (f i) y)) :
    y ∈ cycleComponentSmoothSupportAmbientOpen X x :=
  mem_smoothSupportAmbientOpen_of_linearIndependent_cotangent X x hx y hyZ V hyV f hf
    (linearIndependent_cotangent_of_linearIndependent_chartDerivative X x y hyZ V hyV f hf hind)

/-- **Sub-rung 2** (elementary: chain rule and linear algebra). If finitely many regular
functions `g_j` vanishing on `Z` bound the normal coordinate of a holomorphic adapted chart near
`y ∈ e.source ∩ Z` with exponent one, then `p` of them have linearly independent differentials at
`y`. Route: along `t ↦ y + t h` in the chart, `h ∈ ⋂ ker dg_j(y)` gives `‖n(y + t h)‖ = o(t)`,
so `h ∈ ker dn(y)`; `dn(y)` has rank `p` because `e ≫ L` is a chart of the maximal analytic
atlas (`he`), so the `dg_j(y)` span a space of dimension at least `p`. -/
theorem exists_linearIndependent_chartDerivative_of_norm_le {p : ℕ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (V : X.left.Opens) (hyV : y.underlying ∈ V) {m : ℕ} (g : Fin m → Γ(X.left, V))
    (hg0 : ∀ j, Point.evaluate V (g j) y = 0) (C : ℝ)
    (hC : ∀ᶠ z in 𝓝 y, ‖(e z).2‖ ≤ C * ∑ j, ‖Point.evaluate V (g j) z‖) :
    ∃ σ : Fin p → Fin m, LinearIndependent ℂ (fun i => chartDerivative X V (g (σ i)) y) := by
  sorry

/-- **Sub-rung 1, the analytic input** (deep; not at the pin). Near a point `y ∈ e.source ∩ Z`
of a holomorphic chart adapted to `Z`, finitely many regular functions vanishing on `Z` bound the
normal coordinate with exponent one. Mathematics: the ideal `I·𝒪^an_y` generated by the
algebraic ideal `I` of the reduced `Z` is radical (the local ring of `X` at `y` is excellent,
so its completion `ℂ[[z]]` is reduced modulo `I`), its zero set is the germ of the submanifold
`{n = 0}`, so by Rückert's Nullstellensatz it is `(n_1, …, n_p)`; write `n_k = ∑ a_kj g_j` with
`a_kj` holomorphic, hence bounded near `y`. Equivalent, given sub-rungs 2 and 3, to the rung. -/
theorem exists_norm_normalCoordinate_le (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))) :
    ∃ (V : X.left.Opens) (_ : y.underlying ∈ V) (m : ℕ) (g : Fin m → Γ(X.left, V)) (C : ℝ),
      (∀ j, ∀ z ∈ closure ({x} : Set X.left), z ∉ X.left.basicOpen (g j)) ∧
      ∀ᶠ z in 𝓝 y, ‖(e z).2‖ ≤ C * ∑ j, ‖Point.evaluate V (g j) z‖ := by
  sorry

/-- **The rung `analytic-smooth-locus`.** For a holomorphic chart `e` of `X(ℂ)` adapted to `Z`
(the hypotheses of `transport_supportedClass_eq_chartNormalProjectionCoclass`), every point of
`e.source ∩ Z(ℂ)` lies off `Z_sing(ℂ)`. Assembled from sub-rungs 1, 2, 3. -/
theorem source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    e.source ∩ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ⊆
      cycleComponentSmoothSupportAmbientOpen X x := by
  rintro y ⟨hy, hyZ⟩
  obtain ⟨V, hyV, m, g, C, hg, hC⟩ := exists_norm_normalCoordinate_le X x hx e L he hS y hy hyZ
  obtain ⟨σ, hσ⟩ := exists_linearIndependent_chartDerivative_of_norm_le X e L he y hy V hyV g
    (fun j => evaluate_eq_zero_of_vanishes X x (g j) (hg j) y hyZ hyV) C hC
  exact mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative X x hx y hyZ V hyV
    (fun i => g (σ i)) (fun i => hg (σ i)) hσ

/-- The rung in the form `e.source ⊆ U` (red team on `analytic-smooth-locus`, change F): off `Z`
the inclusion is `mem_smoothSupportAmbientOpen_of_not_mem`. -/
theorem source_subset_smoothSupportAmbientOpen (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    e.source ⊆ cycleComponentSmoothSupportAmbientOpen X x := by
  intro y hy
  by_cases hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))
  · exact source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen X x hx e L he hS
      ⟨hy, hyZ⟩
  · exact mem_smoothSupportAmbientOpen_of_not_mem X x y hyZ

/-- **`cycle-class-germ` without `hyU`** (the corollary named in the rung's title). For every
holomorphic chart adapted to `Z` and every `y ∈ e.source`, the restriction of upstream's
transport of `[Z]` equals `chartNormalProjectionCoclass` of `e` on some open `W ∋ y`, exact, no
sign. Proved from the rung and the checked
`transport_supportedClass_eq_chartNormalProjectionCoclass`. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source) :
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
  have hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x := by
    by_cases hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))
    · exact source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen X x hx e L he hS
        ⟨hy, hyZ⟩
    · exact mem_smoothSupportAmbientOpen_of_not_mem X x y hyZ
  exact transport_supportedClass_eq_chartNormalProjectionCoclass X x hx e L he hS y hy hyU

/-- **Route R2, local purity** (topological, alternative to the rung for its consumers). Upstream
proves at `⊤` (private `cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`, used for
`cycleComponentSingularBoundaryRelH_isZero_of_lt`) that cohomology of `X(ℂ)` with supports in
`Z_sing(ℂ)` vanishes below degree `2(p + 1)`. This is the same vanishing on every open `V`. Route:
upstream's proof with `⊤` replaced by `V`; `nestedSupportRestrictionSectionsComplexShortComplex`
takes the open as an argument, and the layer vanishing is upstream's cofinal local vanishing
(`cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing`), applied inside
`V`. With the lowest-degree identification on `V ∩ U` (`TopCat.Sheaf.lowestSectionCohomologyIso`,
`cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing`) it gives
`transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted` without the rung: a class
on `V` with supports in `Z` whose germs vanish on `V ∩ U` is zero. -/
theorem singularBoundarySectionCohomology_isZero_of_lt (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (V : Opens (ComplexPoint X)) (n : ℤ)
    (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) := by
  sorry

end HodgeLadder.Normalization
```

## cycle-class-sign-test-p2: statement

Date: 2026-11-26 (statement and proofs), 2026-11-27 (checked). Statement, route and proofs written in one session; the statement and proof red team passed it with changes A to E and G (`docs/sketches/cycle-class-sign-test-p2.redteam.md`), all implemented; F (an unconditional singular reading) is skipped, since it would add kernel time. File `HodgeLadder/Tests/CycleClassSignTestP2.lean`, module `HodgeLadder.Tests.CycleClassSignTestP2`, next to `ProjectivePlanePoint` and `CycleClassMultiplicativeP2`, imported from `HodgeLadder.lean`. The ledger's derived `file` hint `HodgeLadder/Cycle/Class/Sign/Test/P2.lean` is superseded. Imports: `HodgeLadder.Tests.ProjectivePlanePoint`, `HodgeLadder.Tests.CycleClassMultiplicativeP2` (for the corollary only), upstream `Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization`, `Other.AlgebraicGeometry.ComplexPoint.CoclassOrientation`, `Other.AlgebraicTopology.Singular.Sheaf.ChainStalk` (all built in the shared cache), and `meta import Lean` for the guard.

### Degree evidence

The degree is computed, with no orientation or definition chosen in this file: deg [pt] = +1 (`planeDegree_planeOrigin`). With the checked `planeLines_cup_eq_planeOrigin`, deg ([L₀] ∪ [L₁]) = +1 (`planeDegree_planeLines_cup`), the literature's value for two lines of ℙ² meeting in one point [`Hatcher2002` §3.2, the cohomology ring of ℂP²; `Fulton1998` ch. 8, numbering unverified]. deg (−[pt]) = −1, so [L₀] ∪ [L₁] ≠ −[pt] (`planeLines_cup_ne_neg_planeOrigin`).

### Route chosen, and why

Route (a). Candidates (b) and (c) are closed at the pin: there is no degree or trace map H⁴(X; ℚ) → ℚ upstream, and no global class [ℙ²] ∈ H₄(ℙ²(ℂ); ℚ). Building [ℙ²] from charts (route (b)) needs the overlap compatibility of `complexLocalOrientation` that upstream's `LocalOrientation` header leaves to a separate naturality theorem, and a Mayer–Vietoris argument in singular homology; neither exists. Route (a) costs one more degree of the checked Mayer–Vietoris computation of `p2-point-class-nonzero`, and the rest is upstream's own transport. The vanishing is proved in every degree q + 3 at once, with the same three covers.

| Step | Map | Declaration | Source |
|---|---|---|---|
| 1 | H⁴(ℙ²; ℚ) ≅ H⁴_Z(ℙ²; ℚ), Z = {pt} = `planeOriginSupport` | `planeOriginForgetEquiv`, inverse of `forgetSupport` | `forgetSupport_planeOrigin_bijective`: injective from H³(ℙ²(ℂ) ∖ pt) = 0 (checked), surjective from H⁴(ℙ²(ℂ) ∖ pt) = 0 (`subsingleton_H'_compl_planeOrigin 1`), both by `forget-support-exact` |
| 2 | H⁴_Z(ℙ²; ℚ) → H⁴(⊤, ⊤ ∖ Z; ℚ) | inside `planeOriginLocalize` | upstream `rationalSupportAddEquivSupportedInjectiveHomology`, then `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ 4` (the transport 𝒯 of `cycle-class-germ`) |
| 3 | H⁴(⊤, ⊤ ∖ Z; ℚ) → H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}; ℚ) | `planeOriginPairMap`, pullback | `pointToNeighborhoodSupportPairMap`: the identity on points, for S ⊆ {y}; inverse to upstream's `neighborhoodSupportToPointPairMap` when y ∈ S (`pointToNeighborhoodSupportPairMap_comp_toPoint`, `toPoint_comp_pointToNeighborhoodSupportPairMap`) |
| 4 | H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}; ℚ) → ℚ | `planeOriginEvaluation` | upstream `relativeCohomologyEquivDualHomology`, applied to `complexLocalOrientation projectivePlane 2 planeOriginPoint` |

`planeDegree` is 4 ∘ 3 ∘ 2 ∘ 1, an `AddMonoidHom`. Signs: none. Steps 1 to 3 are additive equivalences or pullbacks along identities of points; step 4 is evaluation.

### The statements

```lean
theorem subsingleton_H'_compl_planeOrigin (q : ℕ) :
    Subsingleton (Sheaf.H' planeConst (q + 3) planeOriginSupport.compl)

theorem forgetSupport_planeOrigin_bijective :
    Function.Bijective (forgetSupport ℚ projectivePlane planeOriginSupport (2 * 2))

def planeDegree : H^(2 * 2)(projectivePlane; ℚ) →+ ℚ

theorem planeDegree_forgetSupport (a : H_[planeOriginSupport]^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree (forgetSupport ℚ projectivePlane planeOriginSupport (2 * 2) a) =
      planeOriginEvaluation (planeOriginLocalize a)

theorem planeDegree_planeOrigin :
    planeDegree (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin) = 1

theorem planeDegree_planeLines_cup :
    planeDegree (HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring)) = 1

theorem planeDegree_bijective : Function.Bijective planeDegree

theorem planeDegree_eq_one_iff (α : H^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree α = 1 ↔
      α = cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin

theorem planeDegree_neg_planeOrigin :
    planeDegree (-cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin) = -1

theorem planeLines_cup_ne_neg_planeOrigin :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) ≠
      -cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin

theorem planeDegree_eq_eval_of_restrict
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint)
    (α : H^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree α = cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane))
      (2 * 2) (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2) α) μ
```

Well-definedness is `forgetSupport_planeOrigin_bijective` (the lift in step 1 exists and is unique) with `planeDegree_forgetSupport` (on a supported class the degree is the evaluation of its local class, no choice). `planeDegree_bijective` says H⁴(ℙ²; ℚ) is a line and the degree is an isomorphism onto ℚ: injectivity of step 4 from `span_complexLocalOrientation_eq_top`, surjectivity from rational multiples of `analyticPointLocalCoclass`. `planeDegree_eq_eval_of_restrict` is the agreement with the literature's definition deg α = ⟨α, [ℙ²]⟩: a fundamental class restricts to the local orientation at each point [`Hatcher2002` §3.3, recalled, unverified], and the lemma says that any μ with that restriction at pt computes the degree. Its hypothesis is not discharged (no such μ at the pin). Its proof uses the ladder's `forgetRel_supportedEquivPair` and `supportedEquivPair_eq_transport` (rung `supported-pair-forget`) and upstream `cohomologyEquivDualHomology_forgetSupport`, `relativeCohomologyEquivDualHomology_relativeCohomologyMap`, `relativeChainProjection_supportInclusion`.

### The proof of deg [pt] = 1, as checked

`cycleComponentSheafClass_eq_forgetSupport` (upstream, `rfl`) and `planeDegree_forgetSupport` reduce the degree to the evaluation of the transported supported class. Upstream's `cycleComponentSupportedInjectiveClass_point_normalization` (d = 2, `coheight_planeOrigin`), `AddEquiv.apply_symm_apply` and `analyticComponentPointSupportedInjectiveCoclass_relative` make the transport `analyticComponentPointRelativeCoclass`, the pullback of `analyticPointLocalCoclass projectivePlane 2 w` along `neighborhoodSupportToPointPairMap`, with w a complex point of the component (from upstream `range_cycleComponentMap`); w = `planeOriginPoint` by `planeOrigin_support_eq_singleton`. The two pullbacks compose to the identity (`relativeCohomologyMap_pointToNeighborhood_toPoint`), and upstream's `analyticPointLocalCoclass_apply_complexLocalOrientation` gives 1. About 40 lines.

### What the test shows, and what it does not

- It shows that upstream's [pt], read through upstream's own transport and evaluated on upstream's complex local orientation, has degree +1, and that the degree is a bijection, so it separates [pt] from −[pt]. With the exact identity [L₀] ∪ [L₁] = [pt], the product of the two line classes has degree +1, the literature's value.
- The value 1 is close to upstream's normalization: upstream defines `analyticPointLocalCoclass` as the normalized dual of `analyticPointLocalHomologyClass`, which is `complexLocalOrientation` by `rfl` (`analyticPointLocalHomologyClass_eq_complexLocalOrientation`). On that path only upstream's point normalization of the supported class could carry a sign (its substantive step is `smoothClosedPointNormalModelPairMap_localClass`): the inverse of `forgetSupport` is applied to its own image, the pair maps compose to the identity, and the transport T enters both the normalization of [pt] and the degree, so a sign in T would cancel. A sign in T against Ψ shows only through `planeDegree_eq_eval_of_restrict`, where `forgetRel_supportedEquivPair` excludes it.
- It does not recompute [L₀] ∪ [L₁] by a second route: the degree of the cup product is read through the checked identity. An independent computation of the cup product (a second route through the singular cup product in charts) is not attempted.
- It does not test independence of the point. The degree uses the local orientation at pt only; that it equals the evaluation on a global orientation class is `planeDegree_eq_eval_of_restrict`, conditional on such a class. If upstream's local orientations were incoherent between points, a degree read at another point could differ in sign; the missing naturality theorem of upstream's `LocalOrientation` header is what would exclude it.
- It does not test the orientation of ℂ² itself: `complexLocalOrientation` is `localClassOfChart` of `standardComplexLocalClass`, pinned by the rows "Complex orientation of ℂ^p" and "Fundamental-class normalization" of `docs/conventions.md` and by `cross-orientation`, `real-affine-orientation`.

### Independence, guarded

The degree and `planeDegree_planeOrigin` use no part of the multiplicativity proof. The module imports it (through `CycleClassMultiplicativeP2`, for `planeDegree_planeLines_cup`), so a guard on the import list cannot express that; a `run_cmd` at the end of the file walks the constants of this file reachable from `planeDegree`, `planeDegree_planeOrigin`, `planeDegree_bijective` and `planeDegree_forgetSupport` (types and values) and judges each imported constant by its module, since imported theorem bodies are not visible under the module system; it fails the build if that module is, or imports directly or transitively, `HodgeLadder.Cycle.Multiplicative`, `HodgeLadder.Tests.CycleClassMultiplicativeP2`, `HodgeLadder.Local.ClassProduct` or `HodgeLadder.Normalization.Germ`. It also fails if any of those modules is missing from the import closure (stale guard), and if the walk from `planeDegree_planeLines_cup` meets no such module (blind guard, the positive control); the red team checked a transitive control with only `HodgeLadder.Local.ClassProduct` forbidden. Shared with the multiplicativity proof: upstream's transport `complexSupportInjectiveSectionCohomologyEquiv`, `forgetSupport`, the supported class `cycleComponentSupportedInjectiveClass`; `planeDegree_eq_eval_of_restrict` also shares `supported-pair-forget`.

### What is proved

Everything; the file has no open proof. `#print axioms` on all 24 declarations (red team RT1, and `tools/check.py` once the ledger names them): `propext`, `Classical.choice`, `Quot.sound`. Helpers: `planeOriginSupport` (abbrev), `planeOriginForgetEquiv`, `pointToNeighborhoodSupportPairMap` with its two composition lemmas and the two `relativeCohomologyMap` corollaries, `planeOriginPairMap`, `planeOriginLocalize`, `planeOriginEvaluation`, `planeOriginSupportInclusion`, `planeOriginPairMap_eq_comp`, `relativeHomologyMap_planeOriginSupportInclusion_projection`, `relativeHomologyMap_planeOriginPairMap_orientation`. `pointToNeighborhoodSupportPairMap` and its lemmas are general facts about pairs (any space, S ⊆ {y}); phase 2 lists them in `docs/gaps.md`, "General lemmas kept local".

### Failed trivial proofs

Scratch file inside the worktree, deleted. On `planeDegree [pt] = 1`: `rfl` (fails: the sides do not unfold to each other), `simp`, `norm_num`, `simp [planeDegree, planeOriginEvaluation, planeOriginLocalize]` (unsolved goals), `decide` (fails to reduce). On `planeDegree [pt] = −1`: `simp` fails, and `planeDegree [pt] ≠ −1` is proved from the rung by `rw` and `norm_num`. `infer_instance` fails on H⁴ of the complement; `simp` fails on `planeDegree_bijective`.

### Timing

`lake env lean` on the file: 4 min 18 s wall in two runs, default heartbeats. Kernel type checking is 195 s of it, in nine declarations: `planeOriginForgetEquiv` 43 s, `planeDegree_bijective` 37 s, `planeOriginLocalize` 30 s, `planeDegree_forgetSupport` 27 s, `planeDegree` 16 s, `planeDegree_planeOrigin` 15 s, three more near 6 s each (`-Dtrace.profiler`). Elaboration and tactics take about 10 s, the guard 5 s. The longest test module before this one took 96 s. Scratch measurements point at the types: the kernel takes 1 s to check the bare type `H^4(projectivePlane; ℚ)`, 2 s to check `forgetSupport ℚ projectivePlane ⊤ 4`, and 2.5 s more when that map is restated with the notation's types (upstream states `forgetSupport` for a field K, so its ℚ instances come by a different path). Dropping the type ascription of `planeOriginForgetEquiv` moved the cost into `planeDegree` and `planeDegree_forgetSupport` (4 min 44 s in total), so it was reverted. Cutting the kernel time is a phase 2 item.

### Red-team changes (2026-11-27), as implemented

| Change | What | Where |
|---|---|---|
| A | the guard judges imported constants by module and import closure, since imported theorem bodies are not visible under the module system; it needs no fuel | end of the Lean file; section "Independence, guarded" |
| B | ledger title and note say what the test establishes: upstream's [pt] has degree 1 for this degree map, H⁴(ℙ²; ℚ) ≅ ℚ, and with ε = +1 from `cup-singular-comparison` the scalars of the two line classes multiply to 1; no independent sign check at a = b = 1 | `ledger/ladder.json`, this rung and `cycle-class-multiplicative-codim-zero` |
| C | `planeLines_cup_ne_neg_planeOrigin` follows from `cycle-class-multiplicative-p2` and `p2-point-class-nonzero` alone; the value 1 is upstream's | docstrings, section header, module docstring |
| D | only upstream's point normalization could carry a sign on the path; a sign in T would cancel | section "What the test shows, and what it does not" |
| E | the kernel time of the module | `docs/gaps.md`, "Known weaknesses" |
| G | new open rung `p2-fundamental-class`, which would discharge the hypothesis of `planeDegree_eq_eval_of_restrict` | ledger, roadmap |

### For the red team

(1) Is evaluation of the supported lift on the local orientation at one point an acceptable degree map, given `planeDegree_eq_eval_of_restrict` and `planeDegree_bijective`, or should the rung wait for a global class? (2) Vacuity: the degree is nonzero and bijective; `deg [pt] = 1` passes through `forgetSupport⁻¹` and upstream's point normalization, so a sign anywhere on that path shows. (3) The closeness of the value to upstream's definition of `analyticPointLocalCoclass` (third bullet above): is the test strong enough to post as `test`? (4) Drift: upstream `cycleComponentSupportedInjectiveClass_point_normalization`, `analyticComponentPointSupportedInjectiveCoclass_relative`, `analyticPointLocalCoclass_apply_complexLocalOrientation`, `complexLocalOrientation`, `span_complexLocalOrientation_eq_top`, `neighborhoodSupportToPointPairMap`, `supportInclusionPairMap`, `relativeChainProjection_supportInclusion`, `cohomologyEquivDualHomology_forgetSupport`, `range_cycleComponentMap`, `cycleComponentSheafClass_eq_forgetSupport` (an `rfl`); the ladder's `forgetSupport_injective_of_subsingleton`, `forgetSupport_surjective_of_subsingleton`, the Mayer–Vietoris pieces of `ProjectivePlanePoint.lean`, `supportedEquivPair_eq_transport`, `forgetRel_supportedEquivPair`.

## p2-fundamental-class: statement

Date: 2026-11-27 (statement, proofs, red team, checked). The statement and proof red team passed it with changes A to H (`docs/sketches/p2-fundamental-class.redteam.md`), all implemented: the rung is posted with the `∃!` form as headline and the corollary module as its `module`. Files `HodgeLadder/Tests/ProjectivePlaneFundamental.lean` (module `HodgeLadder.Tests.ProjectivePlaneFundamental`, the rung) and `HodgeLadder/Tests/ProjectivePlaneFundamentalDegree.lean` (module `HodgeLadder.Tests.ProjectivePlaneFundamentalDegree`, the corollaries that need `planeDegree`). Both are imported from `HodgeLadder.lean`. The ledger's derived `file` hint `HodgeLadder/P2/Fundamental/Class.lean` is superseded, as for `cycle-class-sign-test-p2`. The rung module imports `HodgeLadder.Tests.ProjectivePlanePoint`, upstream `HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf`, `Other.AlgebraicGeometry.ComplexPoint.LocalOrientation`, `Other.AlgebraicTopology.Singular.EmptySubspace` and Mathlib's `Mathlib.Algebra.Homology.HomologySequence`; it does not import `CycleClassSignTestP2`. The corollary module imports the rung module and `HodgeLadder.Tests.CycleClassSignTestP2`.

### The statements

In the rung module:

```lean
/-- the rung -/
theorem exists_restrict_complexLocalOrientation :
    ∃ μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint

theorem planeOrigin_relativeHomologyProjection_surjective :
    Function.Surjective
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom

theorem subsingleton_homology_three_compl_planeOrigin :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) 3)

theorem subsingleton_homology_compl_planeOrigin_of_H' (n : ℕ)
    (h : Subsingleton (Sheaf.H' planeConst n planeOriginCompl)) :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) n)

theorem relativeHomologyProjection_surjective_of_subsingleton (P : TopPair.{0}) (n : ℕ)
    (h : Subsingleton (Homology ℚ P.snd n)) :
    Function.Surjective (relativeHomologyProjection ℚ P (n + 1)).hom

theorem relativeHomologyProjection_injective_of_subsingleton (P : TopPair.{0}) (n : ℕ)
    (h : Subsingleton (Homology ℚ P.snd n)) :
    Function.Injective (relativeHomologyProjection ℚ P n).hom
```

Helpers: `planeOriginCompl` (abbrev, the open ℙ²(ℂ) ∖ pt as `Opens`), `relativeHomologyProjection_bijective_of_eq_empty`, `subsingleton_relH_compl_planeOrigin`, `subsingleton_relativeCohomology_compl_planeOrigin`. In the corollary module:

```lean
theorem subsingleton_homology_four_compl_planeOrigin :
    Subsingleton (Homology ℚ
      (TopCat.of ({planeOriginPoint}ᶜ : Set (ComplexPoint projectivePlane))) 4)

theorem planeOrigin_relativeHomologyProjection_bijective :
    Function.Bijective
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom

theorem existsUnique_restrict_complexLocalOrientation :
    ∃! μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint

theorem exists_planeDegree_eq_eval :
    ∃ μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2),
      (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
        complexLocalOrientation projectivePlane 2 planeOriginPoint ∧
      ∀ α : H^(2 * 2)(projectivePlane; ℚ),
        planeDegree α = cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane))
          (2 * 2) (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2) α) μ

theorem eval_planeOrigin_of_restrict
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) :
    cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2)
        (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2)
          (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin)) μ = 1

theorem ne_zero_of_restrict_complexLocalOrientation
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) : μ ≠ 0
```

The rung's statement is the hypothesis `hμ` of `planeDegree_eq_eval_of_restrict` verbatim, under `∃`. The types use upstream's `relativeHomologyProjection`, `pointComplementPair` (the pair `TopPair.ofSubset {x}ᶜ`, so `P.snd` is `TopCat.of {x}ᶜ` by `rfl`), `complexLocalOrientation` and the ladder's `planeOriginPoint` = [0 : 0 : 1]. The index `2 * 2` matches the type of `complexLocalOrientation projectivePlane 2`; `4` and `3 + 1` are the same `Nat` by reduction, and the proofs pass between them with no cast.

### Route

| Step | Statement | Declaration | Source |
|---|---|---|---|
| 1 | sheaf H³(V; ℚ) = 0, V = ℙ²(ℂ) ∖ pt | `subsingleton_H'_three_compl_planeOrigin` | checked, rung `p2-point-class-nonzero` (three Mayer–Vietoris steps) |
| 2 | relH ℚ_X n (V ⊓ (X ∖ ⊤) ≤ V) injects into sheaf Hⁿ(V) | `subsingleton_relH_compl_planeOrigin` | upstream `relH.forget_injective_of_eq_bot`; V ⊓ (X ∖ ⊤) = ⊥ by `ext; simp` |
| 3 | that group ≃ singular Hⁿ(V, V ∖ ⊤; ℚ) | `subsingleton_relativeCohomology_compl_planeOrigin` | upstream `relHAddEquivSupportedSectionsHomology` (ambient injective resolution of ℚ, as in `injectiveModelOpen`) followed by `complexSupportInjectiveSectionCohomologyEquiv projectivePlane ⊤ V n`, which takes `openParacompactSpace` internally |
| 4 | Hₙ(V, V ∖ ⊤; ℚ) = 0 | inside `subsingleton_homology_compl_planeOrigin_of_H'` | upstream `relativeCohomologyEquivDualHomology` and Mathlib `Module.subsingleton_dual_iff` (a ℚ-vector space with zero dual is zero) |
| 5 | Hₙ(V; ℚ) = 0, then Hₙ({pt}ᶜ; ℚ) = 0 | same | `relativeHomologyProjection_bijective_of_eq_empty` (upstream `homologyEmptySubspaceIso` after `subst`; the second space {w ∣ w ∉ ⊤} is empty), then the set equality (V : Set) = {pt}ᶜ from `planeOrigin_support_eq_singleton`, transported by `subst` |
| 6 | H₄(ℙ²) → H₄(ℙ², {pt}ᶜ) onto | `relativeHomologyProjection_surjective_of_subsingleton` at n = 3 | upstream `relativeChainShortComplex_shortExact`; Mathlib `ShortComplex.ShortExact.homology_exact₃` with the connecting map zero, `Exact.epi_f`, `ModuleCat.epi_iff_surjective` |
| 7 | the rung | `exists_restrict_complexLocalOrientation` | surjectivity applied to `complexLocalOrientation projectivePlane 2 planeOriginPoint` |

The "Ψ on the open" of the ledger note is step 3. Upstream's `rationalCohomologyAddEquivSingularCohomology` exists only for the whole space X(ℂ); on an open, the transport with support ⊤ plays its part, and only to carry a vanishing. The corollary module adds the degree-four case: `subsingleton_H'_compl_planeOrigin 1` (sheaf H⁴(V) = 0, from `CycleClassSignTestP2`) through the same steps 2 to 5 gives H₄({pt}ᶜ; ℚ) = 0, then `homology_exact₂` (`relativeHomologyProjection_injective_of_subsingleton`) makes the projection injective, hence bijective, and μ unique; the red team checked (RT2) that none of these roots reaches the multiplicativity proof.

### Signs and normalization

None enter. Steps 1 to 5 transport a vanishing statement, so a sign in any equivalence there is invisible and harmless. Step 6 is exactness. The rung's μ is any preimage of upstream's local orientation; it is unique (corollary module), so "the" class is well defined. Its identification with the literature's [ℙ²] for the complex orientation is the one-point characterization [`Hatcher2002` §3.3, Theorem 3.26 and the definition of the fundamental class; numbering unverified]: on a closed connected oriented n-manifold, Hₙ(M) → Hₙ(M, M ∖ x) is an isomorphism and [M] is the preimage of the local orientation at x. That reading also needs `complexLocalOrientation` to be the literature's local orientation at pt; the row "Complex orientation of ℂ^p" of `docs/conventions.md` pins it, outside this rung. Unlike deg [pt] = 1, the reading is sensitive to that row: a real-parts-first ordering of ℂ² ((−1)^{d(d−1)/2} = −1 at d = 2) would make μ = −[ℙ²] and upstream's [pt] = −PD(pt), with every statement here still true. The conjugate orientation is invisible ((−1)² = 1).

### What is proved

Everything; neither file has an open proof. `#print axioms` (scratch, deleted) on `subsingleton_homology_three_compl_planeOrigin`, `planeOrigin_relativeHomologyProjection_surjective`, `exists_restrict_complexLocalOrientation`, `existsUnique_restrict_complexLocalOrientation`, `exists_planeDegree_eq_eval`, `relativeHomologyProjection_injective_of_subsingleton`: `propext`, `Classical.choice`, `Quot.sound`. Non-vacuity: any μ with `hμ` is nonzero (`ne_zero_of_restrict_complexLocalOrientation`, red team change E), since μ = 0 would give `planeDegree [pt] = 0` through `planeDegree_eq_eval_of_restrict`; `eval_planeOrigin_of_restrict` states the positive form, ⟨Ψ [pt], μ⟩ = 1. `tools/check.py` prints the axioms of all 16 ledger declarations.

### Failed trivial proofs

Scratch, with `CycleClassSignTestP2` and `EmptySubspace` imported and the new modules not imported: `exact?` fails on H₃ = 0, on the surjectivity and on the rung. With the new modules imported: `infer_instance` and `simp` fail on H₃ = 0; `simp` fails on the surjectivity; `⟨0, rfl⟩`, `⟨0, by simp⟩` and `aesop` fail on the rung.

### Timing

`lake env lean` on the rung module: 8.6 s wall; `lake build` of it 7.0 s. The corollary module: 5.9 s to 11.7 s wall with `lake env lean`, 4.4 s `lake build`, since `CycleClassSignTestP2` is read from its built `.olean` and not re-elaborated. Neither module is slow; the 4.5 min of `CycleClassSignTestP2` is not paid again.

### For the red team (answered)

Answers in `docs/sketches/p2-fundamental-class.redteam.md`: post the `∃!` form (change B); the support-⊤ transport is sound (section 6); no drift at the pin; the pair lemmas are in `docs/gaps.md` (change F). The questions as posed:

(1) Is the rung's `∃` the right statement, or should the posted rung be the `∃!` form, which costs one import of `CycleClassSignTestP2` (for `subsingleton_H'_compl_planeOrigin 1`) and nothing else? The sheaf H⁴ vanishing could move to the rung module by repeating its three Mayer–Vietoris steps, at the cost of duplicated proof. (2) Step 3 uses the supported transport with support ⊤ on V in place of a comparison Ψ_V: acceptable, given it only carries a vanishing? (3) Drift: upstream `relH.forget_injective_of_eq_bot`, `relHAddEquivSupportedSectionsHomology`, `ambientRationalInjectiveComplex` and its three companions, `complexSupportInjectiveSectionCohomologyEquiv`, `relativeCohomologyEquivDualHomology`, `homologyEmptySubspaceIso`, `relativeChainShortComplex_shortExact`, `pointComplementPair`, `complexLocalOrientation`; Mathlib `homology_exact₂`, `homology_exact₃`, `Module.subsingleton_dual_iff`. (4) The two general pair lemmas and `relativeHomologyProjection_bijective_of_eq_empty` are facts about any pair; phase 2 lists them in `docs/gaps.md`, "General lemmas kept local".

## Sources

`Fulton1998` ch. 7–8, 19 (numbering unverified), `Hatcher2002` §3.2, `Iversen1986` and `Bredon1997` (supports and products; unverified), `MilnorStasheff1974` (unverified). Upstream declarations by name, read at `2ead713`.
