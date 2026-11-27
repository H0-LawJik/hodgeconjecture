# Red team: `analytic-smooth-locus` (statement and planning), the proposed split, route R2

Date: 2026-11-26. Worktree branch on `main` at `6084c3a`, uncommitted `HodgeLadder/Normalization/AnalyticSmoothLocus.lean` and the section "analytic-smooth-locus: statement" of `docs/sketches/cycle-class-multiplicative.md`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Statement pass, before any proof.

Targets: the rung `source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen`; the corollary `transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`; route R1 (sub-rungs 3a, 3b, 2, 1); route R2 (`singularBoundarySectionCohomology_isZero_of_lt`, then injectivity, the lowest-section identification and the checked `cycle-class-germ`); the proposals "needs split plus kill criterion", new rung `cycle-class-germ-no-reg`, re-pointing `cycle-class-multiplicative-no-reg`.

Read at the pin: `Definitions/AlgebraicGeometry/Cycle/Support.lean` (`cycleComponent`, `cycleComponentι`), `Definitions/AlgebraicGeometry/Cycle/Component/SmoothClosedLift.lean`, `Definitions/AlgebraicGeometry/Cycle/Component/SingularClosedFiltration.lean`, `Definitions/AlgebraicGeometry/Cycle/Component/SmoothSupportPurity.lean`, `Definitions/AlgebraicGeometry/Stratification/Basic.lean` (`singularLocusClosed`), `Lemmas/AlgebraicGeometry/Cycle/Component/SupportExtensionVanishing.lean` (the private ⊤ lemmas), `Lemmas/AlgebraicGeometry/Stratification/LocalSupportVanishing.lean`, `Lemmas/AlgebraicTopology/Support/FiniteFiltrationVanishing.lean`, `Lemmas/AlgebraicTopology/Support/NestedLocalization.lean`, `Lemmas/AlgebraicTopology/Support/NestedOnOpen.lean`, `Lemmas/AlgebraicTopology/Sheaf/OpenRestrictedVanishing.lean`, `Definitions/AlgebraicTopology/Sheaf/FlasqueLowestCohomology.lean`, `Lemmas/AlgebraicGeometry/Cycle/Component/SmoothSupportPurity.lean`, `Lemmas/AlgebraicGeometry/Cohomology/SupportedInjectiveModel.lean` (`rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen`), `Lemmas/AlgebraicGeometry/Cycle/Transport/CohomologySheaf.lean`, `Lemmas/AlgebraicTopology/Support/SingularFlasqueModel.lean`, `Lemmas/AlgebraicTopology/Support/SingularSectionNaturality.lean`, `Definitions/AlgebraicTopology/Support/SingularCohomologySheafComparison.lean`, `Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean` (`analyticAt_localChart_symm_evaluate`), `Other/AlgebraicTopology/Support/RelativeCohomologyGerm.lean`; this repository `HodgeLadder/Normalization/Germ.lean`, `HodgeLadder/Cycle/Multiplicative.lean`, `HodgeLadder/Tests/CycleClassGermPoint.lean`; Mathlib `RingTheory/RegularLocalRing/`.

Scratch files (inside the worktree, deleted afterwards):

| File | What | Result |
|---|---|---|
| RT1 | `lake env lean` on the statement file | compiles; five `sorry` warnings, as the sketch says |
| RT2 | all hypotheses of the rung with `e.source ∩ Z` nonempty (section 2) | compiles, no `sorry` |
| RT3 | trivial proofs of the rung, and of `U = ⊤` | all fail (section 3) |
| RT4 | the proposed statements of `cycle-class-germ-no-reg` and the one-term derivation of the `∃ W` form (section 9, change C) | elaborate; the derivation compiles |

`python3 tools/check.py --no-build` in the worktree: every checked rung ACCEPTED; REJECTED on the sorry scan at `AnalyticSmoothLocus.lean` lines 9, 39, 112, 129, 161, 183, 258. Lines 9 and 39 are module-docstring text (finding 8).

**Verdict: pass with changes.** The rung is true, at the literature's strength, sign-free, satisfiable, and not provable by a trivial argument. Route R1 is sound but its sub-rung 1 is a foundation project. Route R2 is sound: upstream's proof at ⊤ uses ⊤ only as the evaluation open and carries over to every open V, and the step from injectivity to the corollary is correct and gives a stronger statement (the identity on all of `e.source`). Pursue R2 first. The changes (section 10) re-point the consumer, split R1 into two ledger rungs with a checkable kill criterion, strengthen the corollary to the whole source, and fix two file-level problems that would block merging.

## 1. Is this the statement the literature makes?

Literature. Let Z be a reduced closed subscheme of a smooth complex variety X and y ∈ Z(ℂ). Z is smooth over ℂ at y if and only if the analytic space Z^an is smooth at y [`SGA1` Exp. XII, Prop. 3.1 for "f smooth iff f^an smooth"; Prop. 2.1 for "Z reduced implies Z^an reduced"; numbering unverified, key proposed in change H]. The comparison goes through the equality of completions of the algebraic and analytic local rings [`Serre1956` §2, Prop. 3; numbering unverified]. Since Z^an is reduced, it is determined by its set; if that set is a complex submanifold of dimension d − p near y, Z^an is smooth at y, hence Z is smooth at y.

Field by field:

| Literature | Lean | Source | Match |
|---|---|---|---|
| X smooth integral projective over ℂ, X(ℂ) a complex manifold of dimension d | `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]`, charted space `localChart X (dim X.left)`, `isManifold_omega` | upstream | yes |
| Z reduced, irreducible, codimension p | `cycleComponent X.left x` = subscheme of `vanishingIdeal (closure {x})`; `hx : Order.coheight x = p` | upstream `Cycle/Support.lean`; register row "Cycle components" | yes |
| Z(ℂ) as a set | `cycleComponentAnalyticClosedSupport X x` = `underlying ⁻¹' closure {x}` | upstream `SmoothClosedLift.lean:112` | yes |
| Z(ℂ) is a complex submanifold of dimension d − p near each point of e.source | `he` (e ≫ L in the ω-maximal atlas, L : E × ℂ^p ≃L[ℂ] ℂ^d, so dim E = d − p) and `hS` (Z = {(e ·).2 = 0} on e.source) | register row "Holomorphic adapted chart" | yes |
| Z smooth over ℂ at y | `y ∈ cycleComponentSmoothSupportAmbientOpen X x` = complement of the complex points over `cycleComponentι '' (smoothLocus (cycleComponentι ≫ X.hom))ᶜ` | upstream `SmoothSupportPurity.lean:32`, `SingularClosedFiltration.lean:48`, `Stratification/Basic.lean:77` | yes: Mathlib's `smoothLocus` of Z → Spec ℂ; Z is irreducible, so the relative dimension is d − p wherever it is smooth |
| for all y ∈ Z near the chart | `e.source ∩ Z ⊆ U` | | yes |

1a. Strength. The rung quantifies over every holomorphic adapted chart and every tangential factor E, as `cycle-class-germ` does. Since `Z_sing ⊆ Z` (upstream `cycleComponentSupportComplement_le_smoothAmbientOpen`), the conclusion is equivalent to `e.source ⊆ U` and to `Disjoint e.source Z_sing`. The form `e.source ⊆ U` is what removes `hyU` in one step; change F adds it as a corollary. The equivalence is a set-theoretic rewrite, so this is not a strengthening of the mathematics.

1b. `hx` is harmless. When `e.source ∩ Z` is nonempty, `he` and `hS` force the analytic dimension d − p, and the analytic dimension of Z(ℂ) equals the algebraic one, so `hx` holds whenever the conclusion has content. Sub-rung 3b needs it (finding 4).

1c. The literature statement needs holomorphy. The cuspidal cubic y² = x³ is a topological manifold at 0 and singular there. In Lean, `he` carries the holomorphy (ω over ℂ in Mathlib's `contDiffGroupoid` is analytic). Dropping `he` gives a false statement.

## 2. Can the hypotheses be satisfied?

Yes, with `e.source ∩ Z` nonempty, on every X and at every complex point y₀ (RT2, compiles with `HodgeLadder.Tests.CycleClassGermPoint`):

```lean
example (y₀ : ComplexPoint X) :
    ∃ (x : X.left) (_ : Order.coheight x = dim X.left)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)))
      (L : ((Fin 0 → ℂ) × (Fin (dim X.left) → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ)),
      e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
        IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X) ∧
      (∀ z ∈ e.source,
        z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) ∧
      y₀ ∈ e.source ∩ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) :=
  ⟨y₀.underlying, coheight_underlying X y₀, closedPointChart X y₀, closedPointChartLinear X,
    closedPointChart_mem_maximalAtlas X y₀, closedPointChart_support X y₀,
    mem_closedPointChart_source X y₀, subset_closure (Set.mem_singleton _)⟩
```

In positive dimension and codimension, the charts of `htr` in `p2-lines-transversal` meet `he` and `hS` for lines on ℙ². Every instance available has U = ⊤ or Z smooth, so the conclusion holds there for an easy reason. This is forced: the rung's content is that no adapted chart passes through a singular point, so no positive instance can exhibit it. Section 7b names the test that shows the conclusion is not trivial in general.

## 3. Trivially true?

RT3: on the rung, `simp_all [cycleComponentSmoothSupportAmbientOpen, cycleComponentSingularAnalyticClosedFiltration]`, `aesop` and `simp` fail; on `cycleComponentSmoothSupportAmbientOpen X x = ⊤`, `simp [cycleComponentSmoothSupportAmbientOpen]` and `ext; simp [cycleComponentSingularAnalyticClosedFiltration, cycleComponentSingularAmbientClosedFiltration]` fail. The sketch's `exact?` finds only the rung. No definition unfolds to `True`, there is no `ℕ∞` coercion (coheight is compared to `(p : ℕ∞)` exactly as in the checked `cycle-class-germ`), the index types `Fin p`, `Fin m` are used with arbitrary p and m, and every hypothesis is used by the assembly (`he`, `hS` by sub-rungs 1 and 2, `hx` by 3b).

The corollary has the same binders as the checked `transport_supportedClass_eq_chartNormalProjectionCoclass` minus `hyU`, so its non-vacuity is that rung's (`adaptedChart_closedPoint`, `chartNormalProjectionCoclass_germ_ne_zero`).

## 4. Interface rung

Not an interface rung; no structure, no axioms.

## Findings on route R1

**Finding 1 (sub-rung 2 is true as stated).** Hypotheses: a holomorphic chart, `y ∈ e.source`, `y.underlying ∈ V`, `g_j(y) = 0` and `‖(e z).2‖ ≤ C ∑ ‖g_j(z)‖` eventually near y; no `hS`. Proof: with c = `chartAt y`, each `g_j ∘ c⁻¹` is analytic at `c y` (upstream `analyticAt_localChart_symm_evaluate`, whose hypothesis `c⁻¹ (c y) ∈ overOpen V` is `hyV`), so for h ∈ ⋂ ker dg_j(y) the bound gives `n(c⁻¹(c y + t h)) = o(t)`, hence h ∈ ker d(n ∘ c⁻¹)(c y). The transition `(e ≫ L) ∘ c⁻¹` is a local biholomorphism at `c y` because both charts lie in the maximal atlas (`he`, `IsManifold.chart_mem_maximalAtlas`, `StructureGroupoid.compatible_of_mem_maximalAtlas`), so `d(n ∘ c⁻¹)(c y) = snd ∘ L⁻¹ ∘ D(transition)` has rank p. So the span of the `dg_j(y)` has dimension at least p, and p of them are independent. Degenerate cases hold: if C ≤ 0 or m < p, the bound forces n ≡ 0 near y, which contradicts rank p unless p = 0, where `Fin 0` makes the conclusion trivial. The exponent one is necessary: a Łojasiewicz bound with exponent below one gives no tangent-space information.

**Finding 2 (sub-rung 1 carries all the analytic content; "equivalent given 2 and 3" is correct in truth).** 1 ⇒ rung is the assembly. Rung ⇒ 1: at y ∈ Z_reg, the ideal of Z at y is generated by p regular functions with independent differentials (Z smooth of codimension p in smooth X); in coordinates where they are the last p coordinates, n vanishes on {g = 0}, so n = A·g with A holomorphic (Hadamard), and A is bounded near y. That direction is elementary but not free in Lean, and nothing needs it. The literature proof of 1 (I·𝒪^an_y radical by excellence and reducedness of completions, then Rückert's Nullstellensatz) needs the convergent power series ring as a Noetherian local ring and Weierstrass preparation for it, neither in Mathlib at the pin (Mathlib has the formal `PowerSeries` Weierstrass preparation only). I looked for a cheaper route and found none: the elimination route (minimal polynomial of a normal coordinate over d − p tangential coordinates) needs a simple root along Z, which is the same analytic input; topological invariants of the local class see nothing (the germ of [Z] at a point where Z(ℂ) is a submanifold is the orientation generator, whatever the algebraic multiplicity); rank semicontinuity of the Jacobian goes the wrong way.

**Finding 3 (sub-rung 3a is true).** The classes `toCotangent ⟨germ (f i), _⟩` are independent over the residue field if the ℂ-linear forms `chartDerivative X V (f i) y` are. Route: if ∑ cᵢ [fᵢ] = 0 with cᵢ in the residue field, lift cᵢ to ℂ (the residue field at a complex point is ℂ through the structure map), so ∑ cᵢ germ(fᵢ) ∈ m_y²; an element of m_y² is a finite sum of products of germs vanishing at y, each represented on a smaller open, whose chart differentials vanish (product rule, `Point.evaluate_res`). No hypothesis is idle: `hyZ`, `hf` build the membership proofs in the statement.

**Finding 4 (sub-rung 3b is true and needs `hx`).** O_{X,y} is regular of dimension d; p germs in I_{Z,y} with independent cotangent classes are part of a regular system of parameters, so O_{X,y}/(f) is regular of dimension d − p, a domain; it surjects onto O_{Z,y}, which has dimension d − p (`hx` and the dimension formula for the integral Z); a surjection from a Noetherian local domain onto a ring of the same finite dimension has zero kernel; so O_{Z,y} is regular, and Z is smooth at the closed point y over the perfect field ℂ. The hypothesis "no point of `closure {x}` in `basicOpen (f i)`" is membership of `f i` in `vanishingIdeal (closure {x})` on V, the ideal of the reduced Z. Without `hx` the statement is false: at p = 0 with `f` empty, `hind` holds vacuously and the conclusion would put every point of Z in U, which fails at a cusp. Missing in Mathlib at the pin: "a regular local ring is a domain" (`IsRegularLocalRing` is defined in `RingTheory/RegularLocalRing/Defs.lean`; no `IsDomain` instance for it; no "formally smooth local algebra over a field is a domain" either). That is a Mathlib contribution of its own.

**Finding 5 (junk values).** `chartDerivative X V s y` evaluates `s` off V and `chartAt y` off its target; the derivative at `chartAt y y` depends only on values near that point, and every statement that uses it assumes `y.underlying ∈ V`. Off `e.source`, `(e z).2` is junk; sub-rung 1's bound is `∀ᶠ z in 𝓝 y`, and `e.source` is open. Both are sound.

## Findings on route R2

**Finding 6 (purity on every open V is true, and upstream's ⊤ proof carries over).** Mathematics: Z_sing(ℂ) is a closed analytic subset of complex codimension at least p + 1 in X(ℂ), so cohomology of any open V with supports in Z_sing(ℂ) vanishes below degree 2(p + 1) [`Iversen1986`, `Bredon1997`; sections unverified]; for V disjoint from Z_sing the supported sections are zero and the statement is trivial; negative degrees vanish because the complex is concentrated in degrees ≥ 0.

Upstream's proof at ⊤, read in full (`SupportExtensionVanishing.lean:33-66`): `cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt` applies `TopCat.Sheaf.finiteNestedSupport_homology_isZero` to the opens `O j = (S_j)ᶜ` of the singular filtration, with `O N = ⊤`, the flasque ambient injective complex, and layer vanishing `cycleComponentSingularLayerSectionCohomology_isZero_of_lt` on `O (k + 1)`. Nothing uses compactness or projectivity beyond the standing instances, and ⊤ enters only as the evaluation open:

| Upstream lemma | Open | Change for V |
|---|---|---|
| `finiteNestedSupport_homology_isZero` (`FiniteFiltrationVanishing.lean:122`) | conclusion at `supportEvaluation X ⊤`; base case `supportedSections_top_homology_isZero X ⊤ K n`, which already takes any `W` | replace ⊤ by V; layer hypothesis on `V ⊓ O (k + 1)` |
| `nestedSupportRestriction_middle_homology_isZero` (same file, line 100) | uses `nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K`, which takes any `W`, and its short exactness, which takes any `W` | replace ⊤ by V |
| `nestedSupportRestrictionLastComplexIso` (`NestedOnOpen.lean:152`) | the only genuinely ⊤-specific piece: identifies X₃ at ⊤ with sections on U vanishing on V | needs a version at W: X₃ at W is `ker(K(W ⊓ U) → K(W ⊓ V))` by the existing `sheafSectionsBetweenOpensOnOpenIso X h W F`, then `sheafSectionsSupportedOutsideOnOpenIso` at `W ⊓ U`; same for `nestedSupportRestrictionLastComplexIso_g` |
| `cycleComponentSingularLayerSectionCohomology_isZero_of_lt` (`LocalSupportVanishing.lean:136`) | on `O (k + 1)`, through `sectionCohomology_isZero_of_cofinal_lower_vanishing`, which holds on any open | apply the same lemma on `V ⊓ O (k + 1)`; the local input `cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing` needs only `y ∉ S_{k+1}`, true for every point of `V ⊓ O (k + 1)` |

Fixed V suffices for the induction (no quantification over opens inside it). An alternative avoids the `W`-version of the last-complex iso: run upstream's general-space lemmas on `TopCat.of V` with the restricted complex (flasque by `openSheafRestriction_isFlasque`), then identify supported sections on `⊤_V` with those on V. Both need comparable glue. The `W`-general versions of the three upstream lemmas are statement-level infrastructure and belong upstream (`docs/gaps.md`, "To upstream").

**Finding 7 (injectivity to the corollary is sound, and gives the whole source).** On V = `e.source`, with h : `Zᶜ ≤ U` (from `Z_sing ⊆ Z`), the nested-support sequence Γ_{Z_sing}(V, I) → Γ_Z(V, I) → Γ_Z(V ⊓ U, I) is short exact (flasque terms), so H^{2p}_{Z_sing}(V) = 0 (finding 6 at n = 2p < 2p + 2) makes restriction H^{2p}_Z(V) → H^{2p}_Z(V ⊓ U) injective in the injective model. Transport to singular relative cohomology needs naturality of `complexSupportInjectiveSectionCohomologyEquiv X Z V (2p)` under V ⊓ U ≤ V: its singular half is upstream's `supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, and its other half (`supportedSingularInjectiveHomologyIso`, a `homologyMap` of the evaluation of one morphism of sheaf complexes) is natural by functoriality of `sectionComplexRestriction`; a few lines. On V ⊓ U the lower supported sheaves vanish (`cycleComponentSmoothSupportCohomologySheaf_isZero_of_ne`), so upstream's `rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen X Z (V ⊓ U) _ _ (2p) _` identifies H^{2p}_Z(V ⊓ U) with sections of `𝓗_[Z]^{2p}` on V ⊓ U, and a section with zero germs is zero (`TopCat.Presheaf.section_ext`, as in `normalization_eq_coclassSection_of_product`). The germs vanish: at each y' ∈ e.source ⊓ U the checked `cycle-class-germ` gives W' with equality on W', and `chartNormalProjectionCoclass_restrict` moves the chart class from `e.source` to W'. So the difference of the two sides on `e.source` restricts to zero on `e.source ⊓ U`, hence is zero. The route transports only "= 0" through isomorphisms and an injective map, so a sign or a nonzero scalar in any comparison square would not change the conclusion; the identity it proves is exact, with the conventions of `cycle-class-germ`.

The `∃ W` form follows from the source form in one term (RT4), so the corollary has exactly the shape `cycle-class-multiplicative-no-reg` needs.

**Finding 8 (the consumer).** `hxreg`, `hwreg` reach `germ_transport_eq_of_chart` as `hyx := hxreg hyT`, `hyw := hwreg hyT` (`Multiplicative.lean:526`), used only at lines 435 to 440 by the three calls of `transport_supportedClass_eq_chartNormalProjectionCoclass`; lines 564 and 616 pass them on. `hyt` is the point of U_t over which `section_ext` runs and stays. Replacing the three calls by the `hyU`-free corollary removes `hyx`, `hyw` and then `hxreg`, `hwreg` everywhere. Nothing else in that file uses them.

## Findings on the file and the plan

**Finding 9 (the sorry scan reads docstrings).** `tools/check.py` flags lines 9 ("the sub-rungs carry `sorry`") and 39 ("(`sorry`)") of the module docstring. After every body is proved the file would still be REJECTED. Reword them ("open bodies").

**Finding 10 (the corollary in the file inherits R1's open bodies).** `transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted` is proved from the rung, so it carries sub-rungs 1, 2, 3a, 3b. Under R2 it needs its own proof in a module that does not import the R1 file. Since the scan covers every file in the tree, the R1 statements cannot land on `main` until proved; keep them on a branch or in the sketch.

**Finding 11 (needs split and kill criterion).** The split is right. Sub-rung 2 has no use without sub-rung 1 (its hypothesis is 1's conclusion), so group 1 and 2 into one rung; sub-rung 3 (3a with 3b) is useful alone, as the sketch says: it turns a regularity hypothesis into the computation of p differentials, which `p2-lines-transversal` now does by identifying a quotient ring by hand. The sketch's kill criterion ("if no Mathlib work on analytic local rings is underway") cannot be checked. Replace it with a test against the pinned Mathlib (change D). "Needs split" is not a ledger status (in `docs/harness.md` it marks a rung released three times); record it in the note and keep the status `open`.

## 5. Checker

Not a checked rung. Run in the worktree: every checked rung ACCEPTED with `propext`, `Classical.choice`, `Quot.sound`; REJECTED on the sorry scan of the statement file, including the two docstring lines (finding 9).

## 6. Conventions

| Convention | Used by | Truth depends on it? | Register |
|---|---|---|---|
| coheight = codimension (Mathlib's scheme order `a ≤ b ↔ b ⤳ a`) | `hx`, 3b | yes for 3b (p is the number of functions); the rung is insensitive | row "Cycle components", present |
| Z_sing = complement of Mathlib's `smoothLocus (cycleComponentι ≫ X.hom)` in Z; U = X(ℂ) ∖ Z_sing(ℂ) | rung, 3b, R2 | yes: the conclusion is about this set | row "Cycle components", present |
| holomorphic adapted chart (ω over ℂ, normal coordinate `(e ·).2`) | rung, 1, 2 | the rung is sign-free; a conjugated normal coordinate keeps `hS` and fails `he`, and without holomorphy the rung is false (cusp) | row "Holomorphic adapted chart", present |
| chart differential `chartDerivative` in `chartAt y`, residue field of a complex point identified with ℂ | 2, 3a | no sign: only linear independence, invariant under ℂ-linear changes of chart | **added** row "Chart differentials and the Zariski cotangent space" |
| local purity on an open and the nested-support sequence | R2 | no sign or scalar: vanishing, exactness and transport of zero only | **added** row "Local purity on an open" |
| complex orientation of ℂ^p, fundamental-class normalization, normalization iso | the corollary (an identity) | yes, inherited exactly from `cycle-class-germ`; R2 adds no sign | rows present |

No cited input is a `Prop` hypothesis. The cited literature (SGA1, Serre1956) states smoothness, which has no sign.

## 7. Equality first

The rung is an inclusion of sets. Its identity form is `e.source ∩ Z_sing = ∅`; the identity it is a step toward is `cycle-class-germ` without `hyU`, and from there `cycle-class-multiplicative-no-reg`. Route R2 proves that identity without the inclusion, exactly and on all of `e.source`, as the new rung `cycle-class-germ-no-reg` (change B). The rung `analytic-smooth-locus` then has no consumer on the ladder.

## 7b. Non-vacuity

The conclusion would be trivially true if U were ⊤ for every component. The smallest test that fails in that case: a component with a singular complex point, in upstream's API,

```lean
∃ (x : X.left) (y : ComplexPoint X),
  y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ∧
  y ∉ cycleComponentSmoothSupportAmbientOpen X x
```

for X = ℙ², x the generic point of the cuspidal cubic Y²Z = X³, y = [0 : 0 : 1]. It does not exist at the pin (searched the ledger, `HodgeLadder/` and upstream for cusp, node, singular witnesses). The same instance is the smallest one on which R2's purity lemma has nonzero supports in Z_sing. Proposed as an optional test rung (change G); it does not block R2, whose identity is non-vacuous through `cycle-class-germ`'s witnesses.

## 8. Pin drift

Written and read at `2ead713`, the current pin. No drift. For the next bump, add to the drift list: `cycleComponentSmoothSupportAmbientOpen`, `cycleComponentSingularAmbientClosedFiltration`, `singularLocusClosed`, `reducedSmoothClosedFiltration` (bodies), `analyticAt_localChart_symm_evaluate`, and for R2 `finiteNestedSupport_homology_isZero`, `nestedSupportRestrictionSectionsComplexShortComplex` and its short exactness, `sheafSectionsBetweenOpensOnOpenIso`, `sheafSectionsSupportedOutsideOnOpenIso`, `sectionCohomology_isZero_of_cofinal_lower_vanishing`, `cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing`, `cycleComponentSingularFiltrationLength`, `cycleComponentSingularAnalyticClosedFiltration_length`, `cycleComponentSmoothSupportCohomologySheaf_isZero_of_ne`, `rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen`, `supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality`, `chartNormalProjectionCoclass_restrict`.

## 9. Route recommendation

R2 first: it is the cheap sound route to the only consumer, it proves a stronger identity, and its inputs are at the pin. Estimate 350 to 650 lines: purity on V 150 to 250 (three `W`-general upstream lemmas plus the induction), injectivity 100 to 200 (the `W`-version of the last-complex iso and its `g`, naturality of the equivalence), the section argument and assembly 100 to 200. The main risk is the `W`-version of `nestedSupportRestrictionLastComplexIso_g`; the `TopCat.of V` alternative (finding 6) is the fallback. Then `cycle-class-multiplicative-no-reg`, which is mechanical (finding 8). Then, optionally, `jacobian-smooth-point`; its 3b waits on "regular local ring is a domain" in Mathlib. Park `analytic-normal-bound`.

## 10. Verdict

**Pass with changes.** The statement of `analytic-smooth-locus` stands as written. Changes:

| # | Change | Owner | Status |
|---|---|---|---|
| A | Split the Lean file. New module `HodgeLadder/Normalization/GermNoReg.lean` (imports `HodgeLadder.Normalization.Germ` only) for route R2: `singularBoundarySectionCohomology_isZero_of_lt` (text as in the statement file), `restrict_smoothSupportAmbientOpen_injective`, `transport_supportedClass_eq_chartNormalProjectionCoclass_source`, and `transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted` proved from the source form. The R1 statements stay in `AnalyticSmoothLocus.lean` on a branch until proved (finding 10) | prover | open |
| B | Ledger: add rung `cycle-class-germ-no-reg` (text below) | maintainer | open |
| C | Statements for change A, elaborated in RT4 (text below) | prover | open |
| D | Ledger: rewrite the note and `depends_on` of `analytic-smooth-locus`; add `jacobian-smooth-point` and `analytic-normal-bound` (text below) | maintainer | open |
| E | Ledger: re-point `cycle-class-multiplicative-no-reg` (text below) | maintainer | open |
| F | Add `source_subset_smoothSupportAmbientOpen` (`e.source ⊆ U`, from the rung and `mem_smoothSupportAmbientOpen_of_not_mem`) to the R1 file, and reword the module docstring lines 9 and 39 to avoid the token `sorry` (finding 9) | prover | open |
| G | Optional test rung `p2-cusp-singular-point` (section 7b) | maintainer | open, optional |
| H | `docs/references.md`: add `SGA1` = A. Grothendieck, Revêtements étales et groupe fondamental (SGA 1), LNM 224, Springer 1971, Exposé XII (M. Raynaud), comparison of algebraic and analytic properties (proposition numbers unverified) | librarian | open |
| I | `docs/gaps.md`, "To upstream": `W`-general versions of `finiteNestedSupport_homology_isZero`, `nestedSupportRestriction_middle_homology_isZero`, `nestedSupportRestrictionLastComplexIso(_g)`, and purity on an open; Mathlib: regular local ring is a domain | maintainer | open |
| J | Sketch: replace "Not tried" in R2 step 1 by the table of finding 6; replace the kill criterion by change D's | thinker | open |

Change C, exact text (elaborates against `HodgeLadder.Normalization.Germ`, RT4):

```lean
/-- Route R2, step 2: on every open `V`, restriction from `V` to `V ⊓ (X(ℂ) ∖ Z_sing(ℂ))` is
injective on `H^{2p}(·, · ∖ Z; ℚ)`. From `singularBoundarySectionCohomology_isZero_of_lt` at
`n = 2p` and the nested-support sequence on `V`. -/
theorem restrict_smoothSupportAmbientOpen_injective (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (V : Opens (ComplexPoint X)) :
    Function.Injective (relativeCohomologyMap ℚ (2 * p)
      (neighborhoodSupportInclusionPairMap
        (W := ((V ⊓ cycleComponentSmoothSupportAmbientOpen X x : Opens (ComplexPoint X)) :
          Set (ComplexPoint X)))
        (V := (V : Set (ComplexPoint X))) (fun _ h => h.1)
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))))

/-- `cycle-class-germ` without `hyU`, on the whole source: for a holomorphic chart adapted to
`Z`, the restriction to `e.source` of upstream's transport of `[Z]` is
`chartNormalProjectionCoclass` of `e` on `e.source`. Exact, no sign; conventions as in
`transport_supportedClass_eq_chartNormalProjectionCoclass`. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_source (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    relativeCohomologyMap ℚ (2 * p)
        (neighborhoodSupportInclusionPairMap
          (W := e.source)
          (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
          ⊤ (2 * p)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)
            (cycleComponentSupportedInjectiveClass X x hx))) =
      chartNormalProjectionCoclass E p e
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS e.source
          subset_rfl
```

and the `∃ W` corollary (statement unchanged from the file) by

```lean
  ⟨⟨e.source, e.open_source⟩, subset_rfl, hy,
    transport_supportedClass_eq_chartNormalProjectionCoclass_source X x hx e L he hS⟩
```

Change B, ledger entry:

```json
{
  "id": "cycle-class-germ-no-reg",
  "title": "cycle-class-germ without hyU: for a holomorphic chart adapted to Z, the transport of [Z] restricted to e.source is chartNormalProjectionCoclass of e, by local purity",
  "status": "open",
  "kind": "foundation",
  "module": null,
  "declarations": [],
  "depends_on": ["cycle-class-germ"],
  "contributors": [],
  "note": "Red team on analytic-smooth-locus (docs/sketches/analytic-smooth-locus.redteam.md, change B). Statement: transport_supportedClass_eq_chartNormalProjectionCoclass_source (x, hx, E, e, L, he, hS as in transport_supportedClass_eq_chartNormalProjectionCoclass; the identity on W = e.source), and transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted (the ∃ W form without hyU, one term from the source form). Exact, no sign; conventions as cycle-class-germ. Route R2: singularBoundarySectionCohomology_isZero_of_lt (supports in Z_sing vanish below 2(p+1) on every open V; upstream's ⊤ proof with the evaluation open V, the W-version of nestedSupportRestrictionLastComplexIso, and sectionCohomology_isZero_of_cofinal_lower_vanishing on V ⊓ O(k+1)); restrict_smoothSupportAmbientOpen_injective (nested-support sequence Z_sing ⊆ Z on V at degree 2p, transported by naturality of complexSupportInjectiveSectionCohomologyEquiv); on e.source ⊓ U, rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen and section_ext with the checked cycle-class-germ and chartNormalProjectionCoclass_restrict. Does not use analytic-smooth-locus."
}
```

Change D, ledger text. `analytic-smooth-locus`: `depends_on` `["jacobian-smooth-point", "analytic-normal-bound"]` (the dependency on `cycle-class-germ` belonged to the corollary, which moves to `cycle-class-germ-no-reg`); note:

> Red team on cycle-class-germ, change G; statement red team 2026-11-26, pass with changes (docs/sketches/analytic-smooth-locus.redteam.md). Statement: source_inter_analyticClosedSupport_subset_smoothSupportAmbientOpen: for x, hx, e, L, he, hS as in transport_supportedClass_eq_chartNormalProjectionCoclass, e.source ∩ cycleComponentAnalyticClosedSupport X x ⊆ cycleComponentSmoothSupportAmbientOpen X x; equivalently e.source ⊆ U (source_subset_smoothSupportAmbientOpen). Mathematics: Z reduced gives Z^an reduced, and Z smooth at y iff Z^an smooth at y (SGA1 Exp. XII, numbering unverified). Needs split: jacobian-smooth-point (sub-rung 3) and analytic-normal-bound (sub-rungs 1 and 2); the rung is a three-line assembly of them. No consumer: cycle-class-multiplicative-no-reg goes through cycle-class-germ-no-reg. Kill criterion: mark dead when cycle-class-germ-no-reg and jacobian-smooth-point are checked, unless the pinned Mathlib then has the ring of convergent power series in n variables as a Noetherian local ring with Weierstrass preparation; a revival takes a new id.

New rung `jacobian-smooth-point` (kind `foundation`, status `open`, `depends_on` `[]`):

> Sub-rung 3 of analytic-smooth-locus. Statement: mem_smoothSupportAmbientOpen_of_linearIndependent_chartDerivative: p = coheight x regular functions on V vanishing on closure {x}, with ℂ-independent differentials at y ∈ Z(ℂ) in upstream's chart (chartDerivative), put y in cycleComponentSmoothSupportAmbientOpen X x. From linearIndependent_cotangent_of_linearIndependent_chartDerivative (3a, elementary) and mem_smoothSupportAmbientOpen_of_linearIndependent_cotangent (3b, Jacobian criterion; needs 'a regular local ring is a domain', missing in Mathlib at the pin). hx is necessary: at p = 0 without it the statement would put every point of Z in U. Use: replaces hand computations of quotient rings in regularity hypotheses (p2-lines-transversal).

New rung `analytic-normal-bound` (kind `foundation`, status `open`, `depends_on` `[]`):

> Sub-rungs 1 and 2 of analytic-smooth-locus. Statements: exists_norm_normalCoordinate_le (near y ∈ e.source ∩ Z, regular functions g_j vanishing on Z with ‖(e z).2‖ ≤ C ∑ ‖g_j(z)‖; deep: excellence, Rückert's Nullstellensatz, convergent power series, none in Mathlib at the pin) and exists_linearIndependent_chartDerivative_of_norm_le (such a bound gives p of the g_j with independent chart differentials; elementary, chain rule and rank of the normal coordinate; exponent one is necessary). Sub-rung 2 has no use without sub-rung 1. Parked under the kill criterion of analytic-smooth-locus.

Change E, `cycle-class-multiplicative-no-reg`: `depends_on` `["cycle-class-multiplicative", "cycle-class-germ-no-reg"]`; replace the note's route sentences by:

> Route (red team on analytic-smooth-locus, change E): in germ_transport_eq_of_chart replace the three calls of transport_supportedClass_eq_chartNormalProjectionCoclass by transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted (rung cycle-class-germ-no-reg) and delete hyx, hyw; then delete hxreg, hwreg from normalization_eq_coclassSection_of_product, eq_supportedInjectiveClass_of_product and cycleComponentSheafClass_cup_of_transversal. hyt stays: it is the point of U_t over which section_ext runs. The mathematics sentence (htr implies hxreg, hwreg, rung analytic-smooth-locus) stays true and is no longer on the route.
