# Sketch: `cycle-class-multiplicative`

Date: 2026-11-26. Front `cup`, decisions 0008 and 0009, rung 6, and the front's kill criterion. Local input: `docs/sketches/local-class-product.md`. This is a plan. Nothing in it is checked, and each identity below is a target.

## Statement

**Plain words.** Let X be smooth, integral and projective over ℂ, of dimension d, and Z, W, T integral subvarieties of codimensions a, b, a + b with T(ℂ) = Z(ℂ) ∩ W(ℂ). Suppose Z and W meet transversally along T: every point of T(ℂ) lies in Z_reg and W_reg and has a holomorphic chart in which Z is {first a coordinates = 0} and W is {next b coordinates = 0}. Then [Z] ∪ [W] = [T] in H^{2(a+b)}(X; ℚ), with sign +, for upstream's cycle classes `cycleComponentSheafClass` and the ladder's Yoneda cup `HodgeLadder.Cup.cup`. Degrees are even, so factor order does not matter (`cup_gradedComm`).

**Literature.** For X nonsingular the cycle map A^*(X) → H^{2*}(X) is a ring homomorphism, and a transversal intersection has multiplicity one [`Fulton1998` ch. 19 and ch. 7–8; numbering unverified]. Cohomology with supports and its products [`Iversen1986`, `Bredon1997`; chapters unverified]. The first case required by decision 0009: two fibres {∞} × ℙ¹ and ℙ¹ × {∞} on ℙ¹ × ℙ¹, meeting in the point (∞, ∞).

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

The chart condition uses upstream's charted-space instance on X(ℂ) (`localChart`) and Mathlib's maximal analytic atlas; it is the literature's transversality in local holomorphic coordinates. `hxreg`, `hwreg` are stated because upstream's normalization lives on X(ℂ) ∖ Z_sing(ℂ), and the analytic-implies-algebraic smoothness needed to drop them is not at the pin. The red team should check that the hypotheses hold at a = b = 0 for every X (expected) and on ℙ¹ × ℙ¹.

## Why the ladder needs it

It is the kill criterion of front `cup`: products of algebraic classes are the reason to have a product. `cup-positive-degree-test` (closes the vacuity gap of the ring laws) and every product of cycle classes in M2 and M3 go through it.

## Proof idea

1. Singular side. With `cup_singular_comparison` (sign (−1)^{(2a)(2b)} = 1), Ψ([Z] ∪ [W]) = cupSing (Ψ[Z]) (Ψ[W]).
2. Supported lifts. Ψ[Z] = forgetRel (Φ_X α_Z) on (X, X ∖ Z), from `supported_forget_compat` moved to `TopPair.ofSubset` by `supportedEquivPair` (rung `cup-comparison-supported-pair`); α_Z = `cycleComponentSupportedInjectiveClass`.
3. Relative product. By `triad-relative-cup`, cupSing (forgetRel a) (forgetRel b) = forgetRel (relCup2 a b) with relCup2 a b ∈ H^{2(a+b)}(X, (X ∖ Z) ∪ (X ∖ W)) = H^{2(a+b)}(X, X ∖ T), by `hT`.
4. Normalization on the singular side. Upstream's normalization iso N_T sends γ to the sheafified restriction to U_T = X ∖ T_sing of upstream's transport of γ (`normalization-singular`, statement elaborated in the scratch file). Upstream's transport agrees with Φ_X after the pair isomorphisms (`transport_eq_flasqueModel`).
5. Germs. At y ∈ T(ℂ), shrink to a chart neighborhood inside Z_reg ∩ W_reg (`hxreg`, `hwreg`, `htr`). There the restriction of Φ_X α_Z is `chartNormalProjectionCoclass` for the chart derived from φ (`cycle-class-germ`: upstream's section is glued from charts, `smoothClosedSupportCoclassStalk_eq_chartGerm`, and any two analytic charts agree, `exists_open_chartNormalProjectionCoclass_eq`); likewise for W and T.
6. Local product. By naturality of relCup2 and `local-class-product`, the restriction of relCup2 (Φ_X α_Z) (Φ_X α_W) is the chart coclass of T. Off T both sections vanish. So N_T (Φ_X⁻¹ (relCup2 …)) is upstream's normalized section, and `cycleComponentSupportedInjectiveClass_unique` gives Φ_X⁻¹ (relCup2 …) = α_T.
7. Forget the support of T and use injectivity of Ψ (an equivalence): [Z] ∪ [W] = [T].

On the decided general-V route: steps 4 and 5 need Φ in V-generality only through naturality in V, which upstream has for the singular step (`supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, `sectionCohomologyToSheafSection_restriction`). The product formula Φ_V (α ∪ β) = (−1)^{pq} relCupSing (Φ_V α) (β|_V) from `track/general-v` is not used in steps 1 to 7, because the product is formed on the singular side. It would be used by a sheaf-side product of two supported classes, which this route avoids.

## What exists (checked by `grep` at the pin)

| Source | Declarations |
|---|---|
| Mathlib | `IsManifold.maximalAtlas`; for ℙ¹ × ℙ¹: `AlgebraicGeometry.GeometricallyIntegral` and its pullback instances, `smooth_isStableUnderBaseChange` |
| upstream | `cycleComponentSheafClass`, `cycleComponentSupportedInjectiveClass`, `cycleComponentSupportedClassNormalizationIso`, `cycleComponentSupportedClassNormalizationIso_apply`, `cycleComponentSupportedInjectiveClass_unique`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply`, `complexSupportInjectiveSectionCohomologyEquiv`, `supportRelativeCohomologyToSheaf`, `smoothClosedSupportCoclassStalk_eq_chartGerm`, `closedImmersionHolomorphicFlatteningChart`, `localChart`, `coheight_genericPoint_eq_zero`, `cycleComponentSheafClass_genericPoint_ne_zero` |
| this repository | `HodgeLadder.Cup.cup`, `one`, `cup_singular_comparison`, `cup_gradedComm`, `supported_forget_compat`, `supportedEquivPair`, `transport_eq_flasqueModel`, `pullbackCoh`; for ℙ¹: `HodgeLadder.Tests.projectiveLine`, `infty`, `openOne`, `complInftyHomeomorph` |

## What is missing

The local sub-rungs (companion sketch). For ℙ¹ × ℙ¹ at the pin: no product of varieties anywhere upstream or here; no Segre embedding, so no `IsProjective` instance for the product; no homeomorphism (X ×_ℂ Y)(ℂ) ≅ X(ℂ) × Y(ℂ) and no product charts; no pullback of cycle classes along a flat map (for pr₁*[pt] = [{pt} × ℙ¹]); no nonvanishing of a point class in H⁴. A cheaper first transversal case is ℙ² with two coordinate lines (projective by definition, one standard chart); changing the order fixed by decision 0009 needs a decision record.

## Sub-rungs

| Id | Statement | Route | Depends on |
|---|---|---|---|
| `fundamental-class-unit` | [X] = `one X` in H⁰(X; ℚ) (statement elaborated: `cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X) = (one X : H^(2 * 0)(X; ℚ))`) | Z = X(ℂ): degree-0 local class pairs to 1 with a point; Ψ of `one` is the constant cocycle | `supported-forget-compat`, `one-is-kappa`, `cycle-class-germ` |
| `normalization-singular` | N_T γ = sheafified restriction to U_T of upstream's transport of γ (elaborated) | `cycleComponentSupportedClassNormalizationIso_apply`, `complexSupportInjectiveCohomologySheafIsoRelative_section_apply`, upstream naturality in V | |
| `cycle-class-germ` | near y ∈ Z_reg, the transported α_Z equals `chartNormalProjectionCoclass` for every analytic chart adapted to Z | step 5 | `normalization-singular` |
| `supported-pair-forget` | on (X, X ∖ Z): forgetRel ∘ `supportedEquivPair` = Ψ ∘ `forgetSupport`, and `supportedEquivPair` = upstream's transport after the pair isomorphisms, no sign | `supported_forget_compat`, `transport_eq_flasqueModel`, `topPairIso` | `supported-forget-compat`, `supported-model-agreement`, `cup-comparison-supported-pair` |
| `cycle-class-multiplicative` | the theorem above | steps 1 to 7 | `local-class-product`, `triad-relative-cup`, `normalization-singular`, `cycle-class-germ`, `supported-pair-forget`, `cup-singular-comparison-absolute` |
| `complex-points-prod` | Point ℂ (X ⨯ Y) ≃ₜ Point ℂ X × Point ℂ Y over Spec ℂ, with product charts in the maximal atlas | universal property; affine charts Hom(A ⊗ B, ℂ) | |
| `p1p1-witness` | ℙ¹ ×_ℂ ℙ¹ in `Over (Spec ℂ)` is integral, smooth of relative dimension 2, projective (Segre) | Mathlib base change; Segre closed immersion into ℙ³ | `projective-line-witness` |
| `p1p1-fibres-transversal` | {∞} × ℙ¹, ℙ¹ × {∞}, (∞, ∞) have coheight 1, 1, 2, the supports meet as required, and the product chart of `openOne` satisfies `htr` | product of the ℙ¹ chart | `p1p1-witness`, `complex-points-prod`, `projective-line-point` |
| `cycle-class-multiplicative-p1p1` | [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)] on ℙ¹ × ℙ¹ | instance of the theorem | `cycle-class-multiplicative`, `p1p1-fibres-transversal` |
| `fibre-class-pullback` | `pullbackCoh pr₁ [∞] = [{∞} × ℙ¹]` | local classes pull back along a submersion | `p1p1-fibres-transversal`, `cycle-class-germ`, `cup-pullback` |
| `p1p1-point-class-nonzero` | [(∞, ∞)] ≠ 0 in H⁴(ℙ¹ × ℙ¹; ℚ) | `forget-support-exact` with H³ of the complement zero | `p1p1-fibres-transversal`, `forget-support-exact` |

`cup-positive-degree-test` then follows from `cycle-class-multiplicative-p1p1`, `fibre-class-pullback` and `p1p1-point-class-nonzero`.

## Kill criterion and smallest falsification test

The front closes (decision 0009) if `cycle-class-multiplicative` fails on upstream definitions. Concretely: if `local-class-cross-model` evaluates to a value other than 1, or `fundamental-class-unit` fails, and the discrepancy is traced to upstream's normalization after the ladder's own definitions (`relCup2`, the cap and cup order) are ruled out, the rung is marked `refuted` with the computed value, and the front is closed or reopened on a corrected normalization by a decision record. A computed −1 would mean [Z] ∪ [W] = −[T] for a, b ≥ 1 at the pin.

Smallest tests, in order: (1) `fundamental-class-unit`, the codimension-zero case: since [X] ≠ 0 upstream and H⁰ is a field for connected X, [X] ∪ [X] = [X] holds only if [X] = 1. (2) `local-class-cross-model` at a = b = 1, the first sign-visible case, on ℂ² with no variety. (3) `cycle-class-multiplicative-p1p1`.

## Risks

1. `cross-orientation` and `real-affine-orientation` are the largest pieces: explicit shuffle simplices and a GL⁺ path that Mathlib lacks.
2. Upstream's triad and cap files are in library `Other`, unbuilt in the shared cache; first import builds them, and upstream does not guard them as statements of record.
3. Pair spellings: (⊤, ⊤ ⊓ (X ∖ Z)), `TopPair.ofSubset`, `neighborhoodSupportComplementPair`; all identifications are identity on points, and each must be shown sign-free.
4. `hxreg`, `hwreg` may be implied by `htr` mathematically; the implication is not at the pin.

## Sources

`Fulton1998` ch. 7–8, 19 (numbering unverified), `Hatcher2002` §3.2, `Iversen1986` and `Bredon1997` (supports and products; unverified), `MilnorStasheff1974` (unverified). Upstream declarations by name, read at `2ead713`.
