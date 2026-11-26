# Red team: `cup-singular-comparison` (supported case)

Date: 2026-11-26. Main at `4e1956f`. Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Target: `HodgeLadder.Cup.cup_singular_comparison_supported` (`HodgeLadder/Cup/SupportedFinal.lean`), rung `cup-singular-comparison`. Inputs read: `SupportedFinal.lean`, `SupportedVariety.lean` (`supCup`), `RelativeCup.lean` (`relCupSing`), `SupportedRawMap.lean` (`Θ`), the statements of `supported_singular_class` and `supported_relative_cup`, `RightMult.lean` (`rightMulApp`), the sketch `docs/sketches/cup-singular-comparison-supported.md`, the absolute verdict `docs/sketches/cup-singular-comparison-absolute.redteam.md`, and upstream `CohomologyFlasqueModel.lean`, `SingularSectionCohomology.lean`, `SingularFlasqueModel.lean`, `SupportedInjectiveModel.lean`, `SupportedSingularModel.lean`, `Cycle/Transport/CohomologySheaf.lean`, `Cycle/FundamentalClass.lean`, `RelativeCochainCone*.lean`, `MappingCoconeShortExact*.lean`, `SupportHypercohomology.lean`, `WithSupport.lean` (both), and Mathlib's `rotateHomotopyEquiv`. Four scratch files were compiled with `lake env lean` from the session scratchpad (A: instantiation, non-vacuity, `rfl` identifications, axioms; B: triviality attempts; C and D: statements of two proposed rungs with `sorry`). None is committed.

**Verdict: pass with changes.** The identity is exact, its objects are upstream's where upstream has them, the factor order matches the absolute case, and the hypotheses hold on ℙ¹ for every closed Z with a nonzero left side. The changes (section 9) concern what the rung does not identify: Φ is a local composite of two upstream equivalences, and it is not yet shown to agree with upstream's cycle-class transport or with Ψ after forgetting the support. Both gaps matter downstream (cycle classes, `local-class-product`), neither affects the truth of this theorem.

## 1. Is this the statement of the literature?

Literature fact: for Z closed in X, the cup product H^p_Z(X) × H^q(X) → H^{p+q}_Z(X) corresponds, under H^n_Z(X; ℚ) ≅ H^n(X, X ∖ Z; ℚ), to the relative cup product H^p(X, X ∖ Z) × H^q(X) → H^{p+q}(X, X ∖ Z), up to a sign fixed by conventions. Relative cup: `Hatcher2002` §3.2 (front face times back face, no sign). The sheaf side ([Bredon, Sheaf Theory, ch. II], [Iversen, Cohomology of Sheaves, ch. II]) is unverified, not opened, not in `docs/references.md`.

Elaborated type, from scratch A with `pp.fullNames`:

| Literature | Lean | Local or upstream |
|---|---|---|
| H^p_Z(X; ℚ) | `TopCat.Sheaf.supportH ↧X(ℂ) Z (constantFunctor.obj ℚ) p`, that is `relH` = Ext(ℤ[X, X ∖ Z], ℚ_X) | upstream statement library (`Definitions/AlgebraicTopology/Support/Cohomology.lean:53`). The `H_[Z]^p(X; ℚ)` in the source resolves to this, not to the singular `CohomologyWithSupport` notation that upstream scopes in `AlgebraicTopology.Singular` (that namespace is open in the file; where both notations are in scope, the singular reading would not typecheck against `flasqueModel`, and the printed type confirms the sheaf reading) |
| supported cup | `supCup α β (p+q) rfl` = α ≫ lift β (Yoneda, α first) | local, rung `supported-cup` |
| H^q(X; ℚ) ≅ H^q_sing(X) | `rationalCohomologyAddEquivSingularCohomology X q` (Ψ) | upstream, library `Other` |
| β on the open ⊤ | `homologyMap (singularCochainComplexIsoTopOpen ℚ _).hom q` | upstream; the linear dual of the chain isomorphism induced by `Opens.inclusionTopIso`, no sign |
| H^n_Z(X; ℚ) ≅ H^n(X, X ∖ Z) | Φ = `supportedRationalSingularSectionCohomologyEquivRelative _ Z.compl ⊤ n ∘ flasqueModel X Z n` | composite of two upstream equivalences; `flasqueModel` is a local `abbrev` for upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque` at K = S (sheafified singular cochains), ι = `iotaQ`, U = W = X ∖ Z, V = ⊤ |
| relative cup | `relCupSing (pairVU _ Z.compl ⊤)`: Tau Ceti cup along `relDiagonal` = Alexander-Whitney followed by (relative projection ⊗ id), relative factor in front | local, rung `relative-singular-cup`; matches `Hatcher2002` |
| pair | `openInclusionPair X (⊤.infLELeft Z.compl)` = (⊤, ⊤ ⊓ (X ∖ Z)) as subspaces | upstream |
| identity | LHS = `((p*q : ℤ).negOnePow : ℤ) • relCupSing (Φ α) (Ψ β on ⊤)` | exact |

On question 1 of the brief (is Φ defensible?):

- Domain. The cycle class of record lives in `supportH` (`cycleComponentSupportedInjectiveClass`, forgotten by `forgetSupport` in `FundamentalClass.lean:88`). Upstream's other equivalence, `rationalCohomologyWithSupportAddEquivSingular` (`Other/.../SupportHypercohomology.lean:234`), starts from `RationalCohomologyWithSupport` (`Other/.../WithSupport.lean:251`), the hypercohomology of Cone(ℚ → Rj_*ℚ) shifted by −1, a `Type 1` with its own forget map through a connecting morphism. No statement of record, no cycle-class definition and no ladder rung uses it (grep of `ledger/`, `docs/`, `HodgeLadder/`). Using it would require a separate identification of `relH` with the cone model, with its own sign. Choosing the `relH`-side model is correct.
- Route. Upstream's cycle-class transport `complexSupportInjectiveSectionCohomologyEquiv` (`Lemmas/.../Cycle/Transport/CohomologySheaf.lean:37`) composes `rationalSupportAddEquivSupportedInjectiveHomology` (Ext to supported sections of the ambient injective resolution I) with the inverse of `complexSupportedSingularInjectiveHomologyIso` (supported sections of S to those of I) and then `supportedRationalSingularSectionCohomologyEquivSupportComplement`. Φ shares the last step (at V = ⊤ before the pair isomorphism) and replaces the first two by the flasque model, which compares S with a different injective resolution (`injectiveResolutionComplex`) through `resolutionToInjective`.
- What is identified. Scratch A checks `iotaQ ℙ¹ = rationalSingularAugmentation ℙ¹` and `singularCochainSheafComplexInt ℙ¹ ℚ = rationalSingularCochainComplex _` by `rfl`, and upstream's S → I is augmentation-preserving on the nose (`constants_comp_singularToConstantInjectiveResolution`). So Φ and upstream's transport should agree exactly, by the same resolution-independence argument as `relHSupported_mk`. That agreement is not proved. The statement typechecks (scratch C):

```lean
example (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    (complexSupportedSingularInjectiveHomologyIso X Z.compl ⊤ (n : ℤ)).hom (flasqueModel X Z n α) =
      rationalSupportAddEquivSupportedInjectiveHomology X Z n α
```

  (with `IsProjective X.hom`, since upstream's iso is stated there.) Without it, `cup_singular_comparison_supported` cannot be combined with upstream's normalization of supported cycle classes (`normalizedRelativeCoclass` through the local-cohomology sheaf), which `local-class-product` needs.
- Ψ against Φ. `forgetRel (Φ α) = Ψ (forgetSupport α)` on ⊤ is not proved either (scratch D typechecks the statement). The supported and absolute theorems together determine this compatibility only up to a factor c_n with c_{p+q} = c_p whenever the products are nonzero; they do not force c_n = 1. For cycle classes the degree is n = 2c, and a twist like ε(n) = (−1)^{n(n−1)/2} would be −1 in degree 2. So this compatibility is a sign-bearing input for any statement that moves a supported cycle class to H^{2c}(X; ℚ) through Φ.

## 2. Are the hypotheses satisfiable?

Yes. Scratch A compiles, no `sorry`:

```lean
local instance : ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

example {p q : ℕ} (Z : Closeds (ComplexPoint projectiveLine)) (α : H_[Z]^p(projectiveLine; ℚ))
    (β : H^q(projectiveLine; ℚ)) : True := by
  have := cup_singular_comparison_supported projectiveLine Z α β
  trivial
```

The four instance hypotheses are those of the absolute case (IsIntegral and Smooth from `HodgeLadder.Tests.ProjectiveLine`, T2 from upstream's `IsProjective.complexPoint_t2Space`, paracompact opens from upstream's theorem `openParacompactSpace` supplied by a local instance). Z is arbitrary. All four are used: IsIntegral and Smooth by Ψ and by the quasi-isomorphism `iotaQ`, T2 and paracompactness by `supportedRationalSingularSectionCohomologyEquivRelative`, all of which appear in the statement. `IsProjective` is not required.

## 3. Trivially true?

Scratch B, on the goal of the theorem: `rfl`, `subsingleton`, `simp [supCup, relCupSing, supCupY]; done`, `exact Subsingleton.elim _ _`: all fail. `infer_instance` for `Subsingleton (RelativeCohomology ℚ (pairVU _ Z.compl ⊤) n)` fails. Neither side is zero by definition: `supCup` is `Ext.comp` through additive equivalences, `relCupSing` the Alexander-Whitney formula, Φ an additive equivalence. No `ℕ∞` coercion, no empty index type, the sign is `Int.negOnePow` of `(p : ℤ) * q`.

Edge cases: Z = ∅ gives `relH` of the pair (X, X), zero on both sides (correct and harmless). Z = ⊤ gives U = ⊥ and reduces to an absolute-type statement on (⊤, ∅).

The left side is nonzero on an instance (scratch A, compiles):

```lean
example : supCup (cycleComponentSupportedInjectiveClass projectiveLine infty coheight_infty')
    (one projectiveLine) (2 * 1 + 0) rfl ≠ 0 := by
  rw [supCup_one]
  intro h
  apply class_infty_ne_zero_of acyclic_compl_infty
  rw [cycleComponentSheafClass_eq_forgetSupport, h, map_zero]
```

Φ is injective, so Φ of this class is nonzero and the theorem gives `relCupSing (Φ α) (Ψ 1 on ⊤) = Φ α ≠ 0` on ℙ¹ with Z the point at infinity. Both sides cannot be forced to zero.

## 4. Interface rung?

Not applicable: no structure, no axioms (decision 0003).

## 5. Checker

`python3 tools/check.py --no-build`: `ACCEPTED: all checks passed`. The eight declarations of rung `cup-singular-comparison` (`cup_singular_comparison_supported`, `exists_supported_rep`, `supCup_flasque_chosen`, `supportedSection_eq_pairEval`, `cls_zsmul`, `exists_cls`, `globalSections_of_singClass`, `topOpen_singClass`) report `[Classical.choice, Quot.sound, propext]`; `#print axioms` in scratch A agrees for the main theorem. Each is the declaration the ledger means. Not listed in the ledger, though the statement depends on them: `flasqueModel` (it appears in the statement) and `supCocycle`; also the primed helpers `supportedSection_eq_pairEval'`, `pairSheafEvaluation_cocycleComp_rightMul'`. They are covered transitively by the axiom check, so this is bookkeeping only.

## 6. Conventions

| Convention | Register row | Truth depends on it? |
|---|---|---|
| Yoneda order: `supCup α β` = α followed by lift β | "Cup product" | yes; consistent with the absolute case (`supCup` against `cup` by `forgetSupport_supCup`) |
| Relative cup: relative factor in front, absolute at back, `relDiagonal` = AW then (relative projection ⊗ id), no sign | **missing**: proposed row "Relative singular cup product" (section 9, change 5) | yes, through order; it matches `rightMulApp` (Tau Ceti `cupCochain` with c in front, `resQ b` at the back), so the right multiplication used in the proof and `relCupSing` have the same order, and `Hatcher2002`'s relative cup |
| R_b components (−1)^{pq}·(c ↦ c ∪ b) | "Right multiplication as a Hom-complex cocycle" | yes; the only sign source, entering through `pairSheafEvaluation_cocycleComp_rightMul` exactly as `named-cocycle-comp` in the absolute case |
| Hom-complex composition, `equivHomShift`, `homComplexPairSheafIsoSupportedSections` | "Hom-complex composition and derived classes" | yes; kernel-checked in `supCup_flasque_chosen` and `supportedSection_eq_pairEval` |
| Cone steps of `supportedRationalSingularSectionCohomologyEquivRelative` | "Supported comparison Φ" | no for the identity. Both ends use the same upstream construction `shortExactHomologyIsoCone` (`shiftedLiftShortComplex`, then the shift isomorphism of homology), related by `shortExactHomologyIsoCone_naturality`; `supported_singular_class` checks that the composite sends the class of Θ₁ c to the relative class of c with no sign. The row's phrase "positive lift `(inclusion, 0)`" repeats upstream's docstring; the construction passes through Mathlib's `rotateHomotopyEquiv`, whose `hom` has components `−(ofHom φ).leftShift 1 1` and `−(inl φ).leftShift 1 0`. Reading the `leftShift` sign (`(a·n' + a(a−1)/2).negOnePow`, here −1 for the first) gives a positive first component, but the claim is not kernel-checked in isolation and does not need to be: any sign there cancels between the two ends |
| Θ₁, Θ₂, Θ₃: sheafification units and upstream's raw-to-dual isomorphisms, no sign; `relSeq.f` = linear dual of the relative chain projection, no sign | "Supported comparison Φ" | no for the identity (proof devices; do not occur in the statement) |
| Φ against upstream's cycle-class transport | **missing** from "Supported comparison Φ" | no for this identity; yes for any combination with upstream's supported cycle classes (section 1) |
| Φ against Ψ under forgetting support | **missing** | no for this identity; yes, in degree 2 mod 4, for moving supported cycle classes to H^{2c}(X; ℚ) (section 1) |
| `singularCochainComplexIsoTopOpen` (X ≅ ⊤ via `Opens.inclusionTopIso`) | not registered; no sign | no |

Sign sensitivity downstream: for supported cycle classes p = 2c is even, so (−1)^{pq} = 1 and the sign of this theorem is invisible there. The order of factors is fixed by the types (`relCupSing` takes the relative class first). The sign-bearing risks for cycle classes are the two unidentified compatibilities above.

October 2026 failure mode (`LekiliSheridan2026`): every borrowed result enters through its Lean statement (upstream equivalences by name, Tau Ceti's cup through `relDiagonal` and `cup_naturality`, the sign through a kernel-checked lemma). The residual risk is interpretive and sits in sections 1 and 9: a later rung that uses Φ as if it were upstream's cycle-class transport, or as if `forgetRel ∘ Φ = Ψ ∘ forgetSupport`, without proving it.

## 7. Equality first

The theorem is an exact identity with an explicit sign, proved without any scalar. It is itself the equality the supported front aims at; `cup-comparison-supported-pair` (open) transports it to the pair (X, X ∖ Z).

## 7b. Non-vacuity

Smallest test that would fail if the statement were trivially satisfied: the example in section 3 (`supCup_one`, `class_infty_ne_zero_of`, `acyclic_compl_infty`, `cycleComponentSheafClass_eq_forgetSupport`, all existing). It compiles in scratch; it is not a checked declaration. It exercises only q = 0 (the unit), so it cannot see the sign or a nonunit β. A (0, 2) test with Z = ⊤, α the lift of `one` (via `forgetSupport_surjective_of_subsingleton` at the empty complement) and β = [∞] would exercise a nonunit β. A sign-visible test needs p and q odd, for example H^1 classes on a curve of positive genus, which nothing at the pin computes (as in the absolute verdict).

## 8. Pin drift

None: the rung and its whole chain were checked at the current pin `2ead713` (`lakefile.toml` line 15). Definitions to diff on the next bump:

- upstream statement library: `supportH`, `CategoryTheory.Sheaf.relH`, `pairSheaf'`, `homComplexPairSheafIsoSupportedSections`, `relHAddEquivSupportedSectionsHomology`, `relHAddEquivSupportedSectionsHomologyOfFlasque`, `injectiveResolutionComplex`, `injectiveResolutionAugmentation`, `resolutionToInjective`, `sheafSectionsSupportedOutside`, `supportEvaluation`, `supportedRationalSingularSectionCohomologyEquivRelative`, `supportedSectionHomologyIsoRestrictionCone`, `sectionComplexRestrictionExtendConeIso`, `openSingularSheafRestrictionConeCohomologyEquivRelative`, `relativeCochainConeCohomologyEquivCanonical`, `relativeDualCochainHomologyIsoCone`, `relativeDualCochainCohomologyEquiv`, `relativeDualCochainShortComplexInt`, `shortExactHomologyIsoCone`, `shiftedLiftShortComplex`, `openInclusionPair`, `RelativeCohomology`, `relativeChainFunctor`, `chainPairFunctor`, `openRawSingularCochainComplexIntIsoDual`, `openRawToSingularCochainSheafComplex`, `singularCochainComplexIsoTopOpen`, `rationalToSingularCochainComplexInt`, `constantFieldSheafComplexIntIsoSingle`, `singularCochainSheafComplexInt_isFlasque`
- for the proposed agreement rung: `complexSupportInjectiveSectionCohomologyEquiv`, `complexSupportedSingularInjectiveHomologyIso`, `rationalSupportAddEquivSupportedInjectiveHomology`, `singularToConstantInjectiveResolution`, `rationalSingularAugmentation`
- upstream `Other`: Ψ and its steps (list in the absolute verdict)
- Mathlib: `mappingCone.rotateHomotopyEquiv`, `mappingCone.map`, the cochain-complex shift, `Abelian.Ext.comp`

## 9. Verdict: pass with changes

Findings:

1. The statement is about upstream's `supportH` (the type of supported cycle classes), upstream's Ψ and upstream's supported singular equivalence; Φ is a local composite of two upstream equivalences. The cone model `RationalCohomologyWithSupport` is a different object that nothing downstream uses; no change needed for it.
2. Order and sign are consistent with the absolute case: relative class in front, (−1)^{pq} from `rightMulCochain`, no sign from the supported models (checked by `supported_singular_class` and `supported_relative_cup`).
3. Hypotheses hold on ℙ¹ for every closed Z; the left side is nonzero for the supported class of a point times 1.
4. Φ is not shown to agree with upstream's cycle-class transport, and not shown to commute with forgetting the support against Ψ. Both are expected to hold exactly; neither is a defect of this rung, both are needed before cycle classes use it.
5. The pair (⊤, ⊤ ⊓ (X ∖ Z)) and β read on ⊤ lose nothing: every identification to (X, X ∖ Z) and to upstream's `CohomologyWithSupport ℚ X Z n = RelativeCohomology ℚ (TopPair.ofSubset Zᶜ) n` is induced by identity-on-points homeomorphisms of pairs (`openIntersectionPairIsoSupportComplement`, `Opens.inclusionTopIso`), so `cup-comparison-supported-pair` needs only naturality of `relCupSing` for maps of pairs plus the matching transport of β; that is enough for the literature form. It is not enough for `local-class-product`, which needs either a supported-times-supported product (relative cup into (X, (X ∖ Z) ∪ (X ∖ W))) or the comparison on a general open V (local classes are sections over small opens), and `supCup` is defined only at V = ⊤.

Changes:

1. **New rung `supported-model-agreement`**: the statement in section 1 (scratch C), exact, no scalar; route `relHSupported_mk`-style resolution independence, `iotaQ = rationalSingularAugmentation` (rfl), `constants_comp_singularToConstantInjectiveResolution`. Then Φ followed by the pair isomorphism equals upstream's `complexSupportInjectiveSectionCohomologyEquiv ∘ rationalSupportAddEquivSupportedInjectiveHomology` at V = ⊤. Add it to `depends_on` of `local-class-product`.
2. **New rung `supported-forget-compat`**: `forgetRel (Φ α) = Ψ (forgetSupport α)` on ⊤, no sign (scratch D typechecks). Sign-bearing for cycle classes in degree 2 mod 4. Add it to `depends_on` of `local-class-product` (or of `cycle-class-multiplicative`).
3. **`local-class-product` dependencies**: record in its note that it needs a supported-times-supported product or a V-general supported comparison, beyond `cup-singular-comparison`; open the missing rung when the route is chosen.
4. **Wording**: the ledger title of `cup-singular-comparison` says "Upstream's sheaf-singular equivalence carries the supported cup product"; Φ is a local composite of upstream equivalences, so say "the composite of upstream's flasque supported-sections model and supported singular equivalence". In the docstring of `cup_singular_comparison_supported`, replace "the supported comparison of record" by "the supported comparison used here" until change 1 is checked (the sketch left the choice of record to the orchestrator; no decision record names it).
5. **Conventions register**: add a row "Relative singular cup product" (`HodgeLadder.Cup.relCupSing`: Tau Ceti cup along `relDiagonal`, relative factor in front, absolute at back, no sign, `Hatcher2002` §3.2; same order as `rightMulApp`; checked compatibility `forgetRel_relCupSing`). Amend "Supported comparison Φ": replace "both cone steps use upstream's positive lift `(inclusion, 0)`" by "both cone steps use upstream's `shortExactHomologyIsoCone`, so any sign of the lift (Mathlib `rotateHomotopyEquiv`) cancels; the composite is sign-free on classes of Θ₁ c (`supported_singular_class`)", and add "not yet identified with upstream's `complexSupportInjectiveSectionCohomologyEquiv` route (rung `supported-model-agreement`) nor shown to commute with forgetting support against Ψ (rung `supported-forget-compat`)". Not done in this pass: the brief for this pass restricts edits to this file.
6. **Ledger bookkeeping**: list `HodgeLadder.Cup.flasqueModel` and `HodgeLadder.Cup.supCocycle` under `cup-singular-comparison`. Rung `supported-sections-right-mult` is off the route used; mark it `dead` with that note, or keep it `open` with the note it already has.
7. **Test**: add the non-vacuity example of section 3 as a checked declaration in `HodgeLadder.Tests` (for example `projectiveLine_supCup_one_ne_zero`), together with the ℙ¹ instantiation of `cup_singular_comparison_supported`, so a change to Φ's instance arguments breaks the build.

## 10. Attempts that failed or were not completed

- Scratch B: `rfl`, `subsingleton`, `simp [supCup, relCupSing, supCupY]; done`, `Subsingleton.elim` on the main goal: no closure. `infer_instance` for subsingleton relative cohomology: fails.
- Did not prove `supported-model-agreement` or `supported-forget-compat`; only their statements were typechecked (C and D, with `sorry`). The first is estimated at 50 to 100 lines from `exists_supported_rep`, `relHSupported_mk` and the cocycle-class composition lemmas; not attempted.
- Did not compute the component sign of `shiftedLiftShortComplex` in Lean; the reading in section 6 is by hand from Mathlib's `leftShift` sign formula and does not affect the identity.
- Did not open Bredon or Iversen; the sheaf-side literature comparison is unverified.
- No odd-degree supported class exists at the pin, so no sign-visible instance was attempted.
