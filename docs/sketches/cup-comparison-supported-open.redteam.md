# Red team: `cup-comparison-supported-open` (supported comparison on a general open)

Date: 2026-11-26. Branch `track/general-v` at `0f863f9` (rung commit `7a67044`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Targets: rungs `singular-restrict-open`, `supported-open-rep`, `supported-open-sections-class`, `cup-comparison-supported-open`, `cup-comparison-open-test`; main theorem `HodgeLadder.Cup.cup_singular_comparison_open` (`HodgeLadder/Cup/SupportedOpenFinal.lean`). Inputs read: the five modules, `Supported.lean` (`supCupY`, `comp_supCupY₀`), `SupportedVariety.lean` (`supCup`), `SupportedFinal.lean` (`flasqueModel`, `cup_singular_comparison_supported`), `SupportedAgreement.lean`, `SupportedForgetFinal.lean`, `RelCupNaturality.lean`, `SupportedConeCompat.lean`, the ledger entries, the sketch section "The comparison on a general open", the handoff, the V = ⊤ verdict `cup-singular-comparison-supported.redteam.md`, and upstream `Support/Cohomology.lean` (`supportH`, `supportHOnOpenPresheaf`), `Support/CohomologyFlasqueModel.lean` (definition and lemmas), `Support/SingularSectionCohomology.lean`, `Support/SingularSectionNaturality.lean`, `Support/CohomologyInjectiveModel.lean`, `SheafCohomology/Pair.lean` (`relH.restrict`), `Singular/Cohomology.lean` (`cohomologyMap`, `relativeCohomologyMap`), `Cycle/Local/LocalHomology.lean`, `Cycle/Transport/CohomologySheaf.lean`. Four scratch files were compiled with `lake env lean` in the worktree and deleted afterwards (A: the V = ⊤ specialization; B: a nonzero instance on a chart neighborhood; C: naturality in V; D: triviality attempts). Their key statements are quoted below.

**Verdict: pass with changes.** The identity is exact, its objects are upstream's, its sign and factor order are those of V = ⊤, and none of the five rungs is vacuous. The three gaps named in the handoff are smaller than recorded: the V = ⊤ spelling gap closes in about 25 lines (scratch A), a nonzero instance exists on upstream's chart neighborhoods for every smooth closed subvariety (scratch B), and Φ_V is natural in V with no sign from two upstream lemmas (scratch C). The changes (section 9) turn these three scratch results into checked declarations and record what `local-class-product` still lacks.

## 1. Is this the statement of the literature?

Literature fact: for V open and Z closed, H^n(V, V ∖ Z; ℚ) ≅ H^n_{Z ∩ V}(V; ℚ), and the product H^p_{Z∩V}(V) × H^q(V) → H^{p+q}_{Z∩V}(V), composed with restriction H^q(X) → H^q(V), corresponds to the relative cup H^p(V, V ∖ Z) × H^q(V) → H^{p+q}(V, V ∖ Z), front face of the relative factor times back face of the absolute one (`Hatcher2002` §3.2), up to a convention-fixed sign. The sheaf side (Bredon, Iversen, Kashiwara and Schapira on Ext(ℤ_{V,W}, F) and on j_! ⊣ j^*) is unverified: not opened, not in `docs/references.md`.

| Literature | Lean | Local or upstream |
|---|---|---|
| H^p_{Z∩V}(V; ℚ) = H^p(V, V ∖ Z) on the sheaf side | `CategoryTheory.Sheaf.relH ℚ_X p (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))` = Ext^p(ℤ[V, W], ℚ_X), W = V ⊓ (X ∖ Z) | upstream; it is the value at V of upstream's `supportHOnOpenPresheaf` (`Support/Cohomology.lean:116`), definitionally the same expression |
| product with an absolute class | `supCupY α β (p+q) rfl` = α followed by `liftH β` (Yoneda, α first), source the pair sheaf `pairSheaf' X Z.compl V (V ⊓ Z.compl) rfl` | local, rung `supported-cup`; no new definition |
| H^q(X; ℚ) ≅ H^q_sing(X) | Ψ = `rationalCohomologyAddEquivSingularCohomology X q` | upstream `Other` |
| restriction of β to V | `cohomologyMap ℚ q (Opens.inclusion' V) (Ψ β)` = homology of the linear dual of the singular chain map of V → X | upstream |
| sheaf-to-singular on (V, W) | Φ_V = `supportedRationalSingularSectionCohomologyEquivRelative X Z.compl V n ∘ flasqueModelOpen X Z V n` | composite of two upstream equivalences at V; `flasqueModelOpen` is a local `abbrev` for upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque` with K = S, ι = `iotaQ`, U = Z.compl, W = V ⊓ Z.compl, hW = `rfl` |
| relative cup | `relCupSing (pairVU X Z.compl V)`, relative factor first, Alexander–Whitney along `relDiagonal`, no sign | local, rung `relative-singular-cup`; matches `Hatcher2002` |
| pair | `openInclusionPair X (Opens.infLELeft V Z.compl)` = (V, V ⊓ (X ∖ Z)) as opens of X | upstream; identified with upstream's (V, V ∖ Z) = `neighborhoodSupportComplementPair V Z` by `openIntersectionPairIsoSupportComplement`, identity on points (used in scratch B) |
| identity | LHS = `((p*q : ℤ).negOnePow : ℤ) • relCupSing (Φ_V α) (β\|_V)` | exact |

Is `supCupY` on the pair sheaf the product the literature means? Yes, for β global. The product depends on β only through its restriction to V: ℤ[V] = j_!ℤ_V and Yoneda composition commutes with the exact restriction j^*, so composing with β on X is composing with β|_V on V (literature step, unverified in Lean). The Lean statement takes β ∈ H^q(X), which is weaker than the literature's β ∈ H^q(V). That is not a defect of this rung: the title says H^q(X), and no upstream object for H^q(V) as an Ext group of ℚ_V on the site of V is used anywhere on the ladder. Section 9 records it for `local-class-product`.

Compatibility with the V = ⊤ product: `supCup α β n h` is by definition `supCupY (Y := TopCat.of (ComplexPoint X)) α β n h` (`SupportedVariety.lean:32`), so the products are the same function, and the only difference at V = ⊤ is the spelling of W. That difference matters at the level of types: `relH … (homOfLE _ : Z.compl ≤ ⊤)` (upstream's `supportH`) and `relH … (homOfLE _ : ⊤ ⊓ Z.compl ≤ ⊤)` are different types, since `⊤ ⊓ Z.compl` and `Z.compl` are propositionally but not definitionally equal. It does not matter for truth. Scratch A recovers `cup_singular_comparison_supported` verbatim from `cup_singular_comparison_open` at V = ⊤, axioms `[propext, Classical.choice, Quot.sound]`:

```lean
lemma cohomologyMap_inclusion_top {Y : TopCat.{0}} (q : ℕ) (c : Cohomology ℚ Y q) :
    cohomologyMap ℚ q (Opens.inclusion' (⊤ : Opens Y)) c =
      HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).hom q c
-- from isoTopOpen_inv_comp_inclusion at V = ⊤ (homOfLE le_top = 𝟙, linearDualMap_id)

theorem rt_open_generalW (W : Opens (ComplexPoint X)) (hW : ⊤ ⊓ Z.compl = W) {p q : ℕ}
    (α : relH ℚ_X p (homOfLE (hW ▸ (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤) : W ≤ ⊤))) (β : H^q(X; ℚ)) :
    <the statement of cup_singular_comparison_open at V = ⊤, with upstream's flasque model at (W, hW)>
  := by subst hW; exact cup_singular_comparison_open X Z ⊤ α β

theorem rt_supported_of_open {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) :
    <the statement of cup_singular_comparison_supported, verbatim> := by
  have h := rt_open_generalW X Z Z.compl (top_inf_eq _) α β
  rw [cohomologyMap_inclusion_top] at h
  exact h
```

The trick is upstream's own interface: `relHAddEquivSupportedSectionsHomologyOfFlasque` takes W and a proof `hW : V ⊓ U = W`, and the domain's `homOfLE` proof is irrelevant, so the statement generalized over (W, hW) reduces to the rfl case by `subst`. No sign enters: the β side is the identity at V = ⊤.

## 2. Are the hypotheses satisfiable?

Yes. `HodgeLadder.Tests.projectiveLine_cup_singular_comparison_open` instantiates the theorem on upstream's ℙ¹ for every closed Z and every open V (IsIntegral and Smooth from `Tests.ProjectiveLine`, T2 from `IsProjective.complexPoint_t2Space`, paracompact opens from upstream's `openParacompactSpace`). All four instance hypotheses are used, by Ψ, `iotaQ` and the supported singular equivalence, as at V = ⊤. `IsProjective` is not required. V and Z are unconstrained.

## 3. Trivially true?

Scratch D, on the goal of `cup_singular_comparison_open`: `Subsingleton.elim`, `simp only [supCupY, relCupSing]; done` and `rfl` fail; `infer_instance` fails for `Subsingleton (RelativeCohomology ℚ (pairVU _ Z.compl V) n)` and for `Subsingleton (relH … (V ⊓ Z.compl ≤ V))`. No `ℕ∞` coercion, no empty index type; the sign is `Int.negOnePow` of `(p : ℤ) * q`.

Edge cases, all harmless: V = ⊥ or V ⊆ X ∖ Z give W = V, both sides zero. Z = ⊤ gives W = V ⊓ ⊥ and an absolute-type statement on (V, ∅).

Nonzero instance with V a small open (scratch B, compiles, axioms `[propext, Classical.choice, Quot.sound]`). For a closed immersion i : Y → X of smooth varieties of relative dimensions m and d, a point z of Y(ℂ) and an open V containing i(z), take Z = i(Y(ℂ)) (closed by upstream's `isClosed_range_map_of_closedImmersion`) and T = upstream's chart neighborhood `smoothClosedSupportNeighborhood X Y i m d z V hzV`, the open where upstream's normalized local classes live:

```lean
theorem rt_nonzero_open :
    ∃ α : relH ℚ_X (2 * (d - m)) (homOfLE (inf_le_left : T ⊓ Z.compl ≤ T)),
      α ≠ 0 ∧
      relCupSing (pairVU _ Z.compl T) (Φ_T α)
        (cohomologyMap ℚ 0 (Opens.inclusion' T) (Ψ (one X))) (2 * (d - m) + 0) rfl ≠ 0
```

Proof: α = Φ_T⁻¹ of upstream's `smoothClosedSupportNormalCoclass` moved along `openIntersectionPairIsoSupportComplement`; it is nonzero because the coclass pairs to 1 with the normal class (`smoothClosedSupportNormalCoclass_apply_class`) and Φ_T and the pair isomorphism are bijective; then `cup_singular_comparison_open` at β = 1 together with `supCupY_oneY` gives `relCupSing (Φ_T α) (1|_T) = Φ_T α ≠ 0`. So both sides of the theorem are nonzero on an open that upstream itself uses. Limits: q = 0, so the sign (−1)^{pq} is 1 here; T ≠ ⊤ is not proved (T is a chart neighborhood, a proper open in every case of interest, but nothing in the proof needs that). A concrete ℙ¹ instance needs a closed immersion Spec ℂ → ℙ¹ with `SmoothOfRelativeDimension 0` and a complex point, which `HodgeLadder.Tests` does not have; i = 𝟙 with m = d gives a degree-0 instance at once.

## 4. Interface rung?

Not applicable: no structure, no axioms (decision 0003).

## 5. Checker

`python3 tools/check.py --no-build` in the worktree: `ACCEPTED: all checks passed`. The ten declarations of the five rungs (`isoTopOpen_inv_comp_inclusion`, `cohomologyMap_inclusion_singClass`, `flasqueModelOpen`, `supCocycleOpen`, `exists_supported_rep_open`, `supCup_flasque_open`, `cup_singular_comparison_open`, `cohomologyMap_inclusion_singClass_pair`, `projectiveLine_cup_singular_comparison_open`) report `[Classical.choice, Quot.sound, propext]`; `#print axioms` in scratch A agrees for `cup_singular_comparison_open`, `cohomologyMap_inclusion_singClass`, `exists_supported_rep_open`, `supCup_flasque_open`. Each is the declaration its ledger entry means: `flasqueModelOpen` is upstream's flasque model at (V, V ⊓ Z.compl, rfl), the statement types match the ledger titles. Bookkeeping: `cohomologyMap_inclusion_singClass_pair` is listed under `cup-comparison-supported-open` though it is the general-space restriction lemma; it belongs with `singular-restrict-open`. Harmless.

## 6. Conventions

| Convention | Register row | Truth depends on it? |
|---|---|---|
| Yoneda order: `supCupY α β` = α followed by `liftH β` | "Cup product" | yes; the same function as at V = ⊤ (`supCup` unfolds to it) |
| Relative cup, relative factor first, no sign | "Relative singular cup product" | yes, through order; `rightMulApp` has the same order |
| R_b components (−1)^{pq}·(c ↦ c ∪ b) | "Right multiplication as a Hom-complex cocycle" | yes; the only sign source, entering through `pairSheafEvaluation_cocycleComp_rightMul'`, general in V |
| Cone steps of Φ at V | "Supported comparison Φ" | no; `supported_singular_class` is stated for general V (`SupportedConeCompat.lean:118`) and fixes the composite on classes of Θ₁ x with no sign |
| Pullback of β to V: `cohomologyMap` along `Opens.inclusion' V` | **missing**; added as row "Pullback to an open" | yes in principle; it is precomposition with the singular chain map, no sign, kernel-checked by `cohomologyMap_inclusion_singClass`; at V = ⊤ it equals the top-open transport `singularCochainComplexIsoTopOpen` used at V = ⊤ (scratch A) |
| Restriction of supported classes in V: upstream `relH.restrict` (precomposition with `pairSheafMap`) against `relativeCohomologyMap (openInclusionPairMap …)` | **missing**; added to row "Supported comparison Φ" | no for this identity; yes for `local-class-product`. Φ_V commutes with it, no sign (scratch C) |
| (V, V ⊓ (X ∖ Z)) against (V, V ∖ Z): `openIntersectionPairIsoSupportComplement` | covered for V = ⊤ in "Supported comparison Φ" | no; identity on points, no sign (used in scratch B) |
| Φ_V against upstream's cycle-class transport at V; forgetting support against Ψ at V | "Supported comparison Φ" records both at V = ⊤ only | no for this identity; yes for any use of upstream's local classes through Φ_V (section 9) |

October 2026 failure mode (`LekiliSheridan2026`): every borrowed result enters through its Lean statement. The two new borrowed inputs, upstream's `cohomologyMap` and the flasque model at V, are used through their definitions and the kernel. The residual risk is interpretive: a later rung that uses Φ_V on a class of (V, W) as if it were upstream's cycle-class transport at V, or that moves a forgotten class of V into H^n(X), without a proof at V.

## 7. Equality first

Exact identity with an explicit sign, no scalar. It is a step toward `local-class-product` (open), which is an equality of classes; that rung exists and lists this one in `depends_on`.

## 7b. Non-vacuity

Smallest test that would fail if the statement were trivially satisfied: `rt_nonzero_open` (section 3), from upstream's `smoothClosedSupportNeighborhood`, `smoothClosedSupportNormalCoclass`, `smoothClosedSupportNormalCoclass_apply_class`, `openIntersectionPairIsoSupportComplement`, `isClosed_range_map_of_closedImmersion`, `relativeCohomologyMap_comp`, `relativeCohomologyMap_id`, and the local `supCupY_oneY`. It compiles in scratch; it is not a checked declaration. The checked test `projectiveLine_cup_singular_comparison_open` is an instantiation only: it would still compile if both sides were zero for every V ≠ ⊤. A sign-visible test needs p and q odd, which nothing at the pin computes (as in both earlier verdicts).

## 8. Pin drift

None: the rungs were checked at the current pin `2ead713` (`lakefile.toml` line 15, unchanged since `b8c7b29`). Definitions to diff on the next bump, beyond the V = ⊤ list: `supportHOnOpenPresheaf`, `CategoryTheory.Sheaf.relH.restrict`, `pairSheafMap`, `relHAddEquivSupportedSectionsHomologyOfFlasque_restrict`, `supportedSectionsRestriction`, `supportedSectionsRestriction_refl`, `sectionComplexRestriction`, `supportedRationalSingularSectionCohomologyEquivRelative_naturality`, `openInclusionPairMap`, `relativeCohomologyMap`, `cohomologyMap`, `singularCochainComplexMap`, `Opens.inclusion'` (Mathlib), `openIntersectionPairIsoSupportComplement`, and for the nonzero test `smoothClosedSupportNeighborhood`, `smoothClosedSupportNormalCoclass`, `normalizedRelativeCoclass`.

## 9. Verdict: pass with changes

Findings:

1. The statement is the literature's product H^p(V, V ∖ Z) × H^q(X) → H^{p+q}(V, V ∖ Z) with β restricted to V, on upstream's objects, in the order and with the sign of V = ⊤. It takes β global, which is weaker than the literature's β ∈ H^q(V).
2. The V = ⊤ spelling gap (`⊤ ⊓ Z.compl` against `Z.compl`) does not matter for truth: scratch A derives `cup_singular_comparison_supported` verbatim from the open theorem, with no sign on the β side. The handoff and ledger note overstate it as open.
3. The restriction of Ψ β to V carries no sign (`cohomologyMap_inclusion_singClass`, kernel-checked), and at V = ⊤ it is the top-open transport.
4. Non-vacuous: on upstream's chart neighborhood T, Φ_T⁻¹ of upstream's normal coclass is a nonzero class, and the theorem at β = 1 is a nonzero identity there (scratch B). The checked ℙ¹ test does not exercise this.
5. Natural in V: Φ_{V'} ∘ `relH.restrict` = `relativeCohomologyMap (openInclusionPairMap …)` ∘ Φ_V, no sign, from upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque_restrict` (at hU = `le_refl`), `supportedSectionsRestriction_refl` and `supportedRationalSingularSectionCohomologyEquivRelative_naturality` (scratch C, about 20 s). Restriction commutes with the product, `relH.restrict (supCupY α β) = supCupY (relH.restrict α) β`, by `comp_supCupY₀` (scratch C). With `relCupSing_naturality` and upstream's `cohomologyMap_comp`, the whole identity is natural in V.
6. For `local-class-product` three things are still missing at a general V: (a) agreement of Φ_V with upstream's cycle-class transport `complexSupportInjectiveSectionCohomologyEquiv X Z V` (upstream's transport takes V; `transport_eq_flasqueModel` is stated at ⊤ only, but its engine `relHSupported_eq_flasque` is already general in (U, V, W, hW)); (b) a product of two supported classes, or a version with β ∈ H^q(V), since α ∪ β keeps the support of α only; (c) the move from `pairVU` to upstream's `neighborhoodSupportComplementPair V Z`, where the normalized local classes live (one `relCupSing_naturality` along `openIntersectionPairIsoSupportComplement`, whose first component is `𝟙 (TopCat.of V)`). `supported-forget-compat` has no direct analogue at V: Ψ is defined for varieties, not for opens.

Changes:

1. **Checked corollary `cup_singular_comparison_supported_of_open`** (or state the open theorem in (W, hW) form, as upstream's flasque model does, and derive both spellings): the scratch-A proof, with `cohomologyMap_inclusion_top`. Put it under `cup-comparison-supported-open` and delete the sentence "the two are not identified in Lean" from the ledger note, the handoff's "Open" line and the sketch.
2. **Checked non-vacuity test**: add `rt_nonzero_open` (section 3) to `HodgeLadder/Tests/SupportedOpenComparison.lean` as a theorem under `cup-comparison-open-test`, and keep the ℙ¹ instantiation. Update the test's module docstring and ledger note ("does not exhibit a nonzero class") accordingly.
3. **New rung `supported-open-naturality`**: Φ_V natural in V and the product compatible with restriction, the two scratch-C statements, exact, no sign. Add it to `depends_on` of `local-class-product`.
4. **New rung `supported-model-agreement-open`**: `complexSupportInjectiveSectionCohomologyEquiv X Z V n` against `supportedRationalSingularSectionCohomologyEquivSupportComplement … V n ∘ flasqueModelOpen X Z V n` on classes of (V, V ⊓ Z.compl), through `relHSupported_eq_flasque` at V; the injective side needs upstream's `relHAddEquivSupportedSectionsHomology` at V in place of `rationalSupportAddEquivSupportedInjectiveHomology` (which is ⊤-only). Add it to `depends_on` of `local-class-product`.
5. **`local-class-product` note**: record items 6(b) and 6(c) of the findings as the remaining inputs.
6. **Ledger bookkeeping**: move `cohomologyMap_inclusion_singClass_pair` to `singular-restrict-open`, or say in that rung's note that its variety form lives in `SupportedOpenFinal.lean`.
7. **Conventions register**: done in this pass (rows "Supported comparison Φ" amended, "Pullback to an open" added).

## 10. Attempts that failed or were not completed

- Scratch A, first tries: `rw [← Iso.inv_comp_eq]` on `singularCochainComplexMap ℚ (Opens.inclusion' ⊤) = (singularCochainComplexIsoTopOpen ℚ Y).hom` fails (the two sides' types agree only up to unfolding `SingularCochainComplex`); `rw [Category.comp_id]` fails on the composite for the same reason; `erw` works. The first version of `rt_open_generalW` hit `maximum recursion depth`; `maxRecDepth 20000` fixes it.
- Scratch B, first try: `smoothClosedSupportNormalCoclass_ne_zero` lives in upstream's `Other` library and is not imported by the ladder's `HodgeConjecture` modules; its three-line proof from `smoothClosedSupportNormalCoclass_apply_class` was inlined.
- Scratch D: `Subsingleton.elim`, `simp only [supCupY, relCupSing]; done`, `rfl` on the main goal, and `infer_instance` for both subsingleton instances: all fail.
- Not attempted: a concrete ℙ¹ version of `rt_nonzero_open` (needs a closed point immersion and a complex point in `HodgeLadder.Tests`); the full naturality of the identity in V (only its two non-formal parts were proved; the rest is `relCupSing_naturality` and `cohomologyMap_comp`); `supported-model-agreement-open`; a sign-visible instance.
- Did not open Bredon, Iversen or Kashiwara and Schapira; the sheaf-side literature comparison is unverified.
