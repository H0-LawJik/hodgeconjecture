# Red team: `normalization-singular`

Date: 2026-11-26. Branch `track/normalization-singular` at `5d32a63` (parent `aae9e1e`). Pin: `Paul-Lez/HodgeConjecture@2ead713`, Lean and Mathlib `v4.35.0-rc4`. Target: `HodgeLadder.Normalization.normalization_singular` in `HodgeLadder/Normalization/Singular.lean`; statement of record for the rung in `docs/sketches/cycle-class-multiplicative.md`, "Glue statements".

Read: the Lean file, the handoff `docs/handoffs/2026-11-26-normalization-singular.md`, the ledger entries of `normalization-singular`, `cycle-class-germ`, `supported-open-naturality`, `supported-model-agreement-open`, the sketch and its red team, decision 0010, `docs/conventions.md`, `docs/references.md`, and at the pin: `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean`, `Definitions/AlgebraicTopology/Support/RelativeCohomologySheaf.lean`, `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean`, `Lemmas/AlgebraicGeometry/Cycle/Transport/CohomologySheaf.lean`, `Lemmas/AlgebraicGeometry/Cohomology/SupportedInjectiveModel.lean`, `Lemmas/AlgebraicTopology/Support/SingularSectionNaturality.lean`, `Definitions/AlgebraicTopology/Support/SingularSectionCohomology.lean`, and in `Other`: `Cohomology/SupportSheafNormalization.lean`, `Cycle/Component/PointClassNormalization.lean`, `Sheaf/OpenRestrictedLowestCohomology.lean`.

Scratch (all inside the worktree, deleted afterwards): RT1 instances and non-vacuity; RT2 the statement without the local instance, and composition with `transport_eq_flasqueModel` and upstream's naturality; RT3 `rfl` and a `Subsingleton` instance; RT4 and RT6 the `Other` closure of the proof and the constants of the statement; RT7 the entry point of `cycle-class-germ`; RT8 the file without its local instance.

**Verdict: pass with changes.** The checked statement is the sketch's text character for character. It is exact, carries no sign, and composes with the checked `transport_eq_flasqueModel` and upstream's naturality in the spelling `cycle-class-germ` needs (elaborated). The changes are to the record and one docstring. None touches the statement.

## 1. Is this the statement the literature makes?

The rung is glue between two upstream models, so the literature has no statement of it as such. The fact behind it: on the smooth locus U of Z, the restriction of a class in H^{2p}_Z(X) lands in the sections of the local cohomology sheaf ℋ^{2p}_Z over U, and by purity below degree 2p that restriction is an isomorphism [`Iversen1986`, `Bredon1997`; chapters unverified]. Upstream fixes the fundamental class through this isomorphism (`cycleComponentSupportedInjectiveClass` is N⁻¹ of the normalized coclass section). The rung reads N in the singular model.

Diff against the sketch (lines 61 to 75 of `cycle-class-multiplicative.md` against lines 48 to 62 of the Lean file): one line differs, the trailing `:= by`. The statement is the sketch's text.

| Sketch (words) | Lean | Source |
|---|---|---|
| X smooth integral projective over ℂ | `[IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]` | upstream |
| x of coheight p | `(x : X.left) {p : ℕ} (hx : Order.coheight x = p)` | Mathlib |
| a ∈ H^{2p}_Z(X; ℚ) | `CycleComponentSupportedCohomology X x p` (`AddCommGrpCat.of (H_[Z]^(2p)(X; ℚ))`) | upstream statement library |
| N | `cycleComponentSupportedClassNormalizationIso X x hx` | upstream statement library |
| U = X ∖ Z_sing | `cycleComponentSmoothSupportAmbientOpen X x` | upstream statement library |
| injective-model image of a | `rationalSupportAddEquivSupportedInjectiveHomology X Z (2p) a` | upstream `Lemmas` |
| transport at ⊤ | `complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2p)` into H^{2p}(⊤, ⊤ ∖ Z) on `neighborhoodSupportComplementPair` | upstream `Lemmas` |
| restriction (X, X ∖ Z) → (U, U ∖ Z) | `relativeCohomologyMap ℚ (2p) (neighborhoodSupportInclusionPairMap (U ⊆ ⊤) Z)` | upstream; the presheaf map of `supportRelativeCohomologyPresheaf` by definition |
| sheafification unit at U | `(supportRelativeCohomologyToSheaf _ Z (2p)).app (op U)` | upstream |

RT6 lists every non-Mathlib constant in the statement's type. All are in upstream's `HodgeConjecture` library (`Definitions` and `Lemmas`); none is in `Other` or in this repository.

Two record discrepancies, no change to the statement: the sketch says the text was elaborated against `Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization`, the file imports `Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization` (which re-exports it); the sub-rungs row names the route `complexSupportInjectiveCohomologySheafIsoRelative_section_apply` and "upstream naturality in V", the checked route is `openRestrictedLowestSectionCohomologyIso_hom`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` and naturality of the sheafification unit (finding 1).

## 2. Can the hypotheses be satisfied?

The only hypothesis beyond the instances is `hx : Order.coheight x = p`, with p implicit; any point of finite coheight meets it. RT1 instantiated the theorem on `HodgeLadder.Tests.point` (Spec ℂ) at its generic point with upstream's `coheight_genericPoint_eq_zero`, and on `HodgeLadder.Tests.projectiveLine` at `infty` with `coheight_infty` (cast through `Nat.cast_one`). Both elaborate.

## 3. Trivially true?

- `rfl` fails at default transparency (RT3): the two sides are not definitionally equal there. The proof is four upstream equations; the second (`openRestrictedLowestSectionCohomologyIso_hom`) is a `simp` and rewrite proof in upstream's `Other`, not an unfolding.
- No side is forced to zero. RT1, on every X: at the generic point, `cycleComponentSupportedInjectiveClass` has N-image ≠ 0, because a zero image would make the class zero (N is an equivalence) and then `cycleComponentSheafClass_genericPoint_ne_zero` (upstream `Other`) fails. So both sides take a nonzero value. RT3: no `Subsingleton` instance on `CycleComponentSmoothCoclassSections`.
- Every hypothesis is used: `hx` enters N through purity; `a` is the argument on both sides.
- No ℕ∞ coercion problem: `p : ℕ` enters only as `(p : ℕ∞)` in `hx` and as `2 * p` in degrees, the same spelling upstream uses in `CycleComponentSupportedCohomology` and `cycleComponentSupportedClassNormalizationIso`.
- The local instance `∀ V : Opens (ComplexPoint X), ParacompactSpace V` is unused. RT2 elaborates the statement without it and closes it by the checked theorem, so the type does not depend on it; RT8 compiles the whole file without it. Its docstring ("as the transport needs") is inaccurate: `complexSupportInjectiveSectionCohomologyEquiv` installs `openParacompactSpace X` itself with `letI`. Harmless; finding 2.

## 4. Interface rung

Not applicable: no structure, no axioms.

## 5. Checker and axioms

`python3 tools/check.py --no-build` exits 0 in about 16 seconds: `ACCEPTED (axioms: HodgeLadder.Normalization.normalization_singular [Classical.choice, Quot.sound, propext])`, "all checks passed". `#print axioms` in RT1 gives the same three. The ledger names one declaration, `HodgeLadder.Normalization.normalization_singular`, module `HodgeLadder.Normalization.Singular`, imported from `HodgeLadder.lean` (line 104). It is the declaration the sketch states.

## 6. Conventions

| Convention | Where it enters | In the register | Truth depends on it |
|---|---|---|---|
| N: support extension (excision to U ⊓ (X ∖ Z) = X ∖ Z) then the lowest-section equivalence | LHS | new row "Normalization iso against the singular transport" | yes, an identity |
| Lowest-section equivalence on U equals `sectionCohomologyToSheafSection` at U, with no transport factor | step 2 (`openRestrictedLowestSectionCohomologyIso_hom`) | new row | yes |
| Cohomology-sheaf iso `complexSupportInjectiveCohomologySheafIsoRelative` | step 3 | new row: built from `complexSupportedSingularToAmbientInjective` and `supportedSingularCohomologySheafIsoRelative`, the two pieces of the transport | yes |
| Transport `complexSupportInjectiveSectionCohomologyEquiv` (cone steps of `shortExactHomologyIsoCone`) | RHS | row "Supported comparison Φ": the cone-step signs cancel; with `transport_eq_flasqueModel` the transport is Φ's flasque model, no sign | yes |
| Ext model to injective model | RHS (`rationalSupportAddEquivSupportedInjectiveHomology`) | row "Ext model to injective model": additive equivalence, no scalar | yes |
| Restriction of pairs | RHS (`neighborhoodSupportInclusionPairMap`) | identity on points (upstream definition: `fun w => ⟨w.1, hWV w.2⟩`) | no sign possible |

Each step is a kernel-checked equation between the maps upstream defines; no cited result and no hypothesis carries a convention into the proof. The October 2026 failure mode (a borrowed result applied with the opposite sign) needs a result used as an assumption, and this proof has none. One watch item for downstream rungs: the module docstring of upstream's `PointClassNormalization.lean` says that the comparison of its point class "with the legacy ordinary class has its own cone sign". That comparison is not used here, and the ladder's forget compatibility (`supported_forget_compat`) is checked without a sign; a rung that cites the legacy point class directly must read that sign from source.

## 7. Equality first

The rung is an identity, proved exactly. The docstring says "with no sign", and the ledger note says "Exact, no sign". No scalar enters. It is a step toward `cycle-class-germ` and `cycle-class-multiplicative` (both open, in the ledger).

## 7b. Non-vacuity and composition

Smallest test that fails if the statement were trivial: the RT1 example `∃ a : CycleComponentSupportedCohomology X (genericPoint X.left) 0, (cycleComponentSupportedClassNormalizationIso X (genericPoint X.left) (coheight_genericPoint_eq_zero X)).toAddMonoidHom a ≠ 0`, proved from `cycleComponentSupportedInjectiveClass`, `cycleComponentSheafClass_genericPoint_ne_zero` and injectivity of N. It is not in the repository. Upstream's `cycleComponentSheafClass_genericPoint_ne_zero` exists (`Other/AlgebraicGeometry/Hodge/CodimensionZeroNonvanishing.lean:47`).

Composition (elaborated in RT2 and RT7):

- With `transport_eq_flasqueModel`: N a = toSheaf_U (restrict (`supportedRationalSingularSectionCohomologyEquivSupportComplement` ⊤ (2p) (`flasqueModel` X Z (2p) a))). The degree, the support argument and the `AddCommGrpCat` carrier all match; no cast. Use `(normalization_singular X x hx a).trans (congrArg … (transport_eq_flasqueModel X Z (2 * p) a))`, or `refine (normalization_singular …).trans ?_` and then `rw [transport_eq_flasqueModel]`. A goal-level `rw [normalization_singular X x hx a, …]` with N on the left times out in `whnf` at 200000 heartbeats, the same failure the prover hit.
- Restriction from ⊤ to U through upstream's `supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality` (statement library, `Lemmas/AlgebraicTopology/Support/SingularSectionNaturality.lean:102`): it is stated with `neighborhoodSupportInclusionPairMap`, the spelling on the RHS, so it closes by `congr 1` and the lemma. No spelling gap on this path.
- With the supported cycle class: `cycleComponentSmoothSupportCoclassSection X x hx` equals the RHS at a = `cycleComponentSupportedInjectiveClass X x hx`, by `apply_symm_apply` and the theorem (RT7). This is where `cycle-class-germ` starts.
- The at-U agreement `transport_eq_flasqueModelOpen` (rung `supported-model-agreement-open`) uses `injectiveModelOpen` at U, and the ladder's `comparisonOpen_restrict` (rung `supported-open-naturality`) uses `openInclusionPairMap` on (V, V ⊓ (X ∖ Z)). Reaching them from this theorem needs one more step: upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque_restrict` for the flasque model, and the `⊤ ⊓ (X ∖ Z)` against `X ∖ Z` spelling at V = ⊤ that the register already records (`subst` on the generalized form). Not tried. The ⊤-form path above has no such gap; prefer it in `cycle-class-germ`.
- Downstream spelling to watch (not this rung): `cycle-class-multiplicative` applies N at T in degree `2 * (a + b)`, and `relCup2` and the cap model produce degree `2 * a + 2 * b` (the sketch's `orient` already casts by `Nat.mul_add`).

## 8. Pin drift and the `Other` closure

Checked at the current pin `2ead713`; the sketch was read at the same commit. No drift to diff.

The statement uses only upstream's statement library (RT6), so a change in `Other` can break the build of this file and cannot change what the theorem says. The proof depends on 28 non-internal `Other` declarations (RT4, transitive closure through `Other` and this repository, read with `value? (allowOpaque := true)`):

| `Other` file | Declarations |
|---|---|
| `AlgebraicGeometry/Cohomology/SupportSheafNormalization.lean` | `cycleComponentSupportedClassNormalizationIso_apply`, `cycleComponentSupportSectionRestriction`, `complexSupportInjectiveCohomologySheafIsoRelative_section`, `_section_assoc`, `_comp`, `complexSupportCohomologySheafNormalizationParacompact` |
| `AlgebraicGeometry/Cycle/Component/PointClassNormalization.lean` | `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section` |
| `AlgebraicTopology/Support/SingularCohomologySheafComparison.lean` | `supportedSingularCohomologySheafIsoRelative_section` |
| `AlgebraicTopology/Sheaf/OpenRestrictedLowestCohomology.lean` | `openRestrictedLowestSectionCohomologyIso_hom`, `openRestrictionTopSectionComplexIso_homology_section`, `sectionComplexEqIso`, `sectionComplexEqIso_hom_refl`, `sectionComplexEqIso_homology_section`, `supportEvaluationEqIso` |
| `AlgebraicTopology/Sheaf/CohomologyOpenRestriction.lean` | `sectionCohomologyToSheafSection_openRestriction`, `_openRestriction_assoc`, `sectionCohomologyPresheafToSheaf_openRestriction`, `openRestrictionSectionCohomologyPresheafIso_onOpen` |
| `AlgebraicTopology/Sheaf/CohomologyOpenComparison.lean` | `cohomologyOpenPresheafRestriction` and its `_additive`, `_preservesFiniteLimits`, `_preservesFiniteColimits`, `openRestrictionSectionCohomologyPresheafIso`, `openRestrictionSectionCohomologySheafificationIso` |
| `AlgebraicTopology/Sheaf/CohomologySectionRestriction.lean` | `sectionCohomologyToSheafSection_restriction`, `_restriction_assoc` |
| `AlgebraicTopology/Sheaf/CohomologySectionNaturality.lean` | `sectionCohomologyToSheafSection_naturality` |
| `AlgebraicTopology/Sheaf/HomologySection.lean` | `CategoryTheory.ShortComplex.mapHomologyIso_comp_hom` |

The three the proof names directly (`cycleComponentSupportedClassNormalizationIso_apply`, `openRestrictedLowestSectionCohomologyIso_hom`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`) and `complexSupportInjectiveCohomologySheafIsoRelative_section` are now in the `Other` row of "What exists" in `docs/sketches/cycle-class-multiplicative.md`, which points to this table for the rest. Two of the `Other` lemmas (`openRestrictedLowestSectionCohomologyIso_hom`, `sectionComplexEqIso_homology_section`) set `backward.isDefEq.respectTransparency false` and `backward.defeqAttrib.useBackward true` upstream; a Lean bump that removes those options is a build risk for this file.

## 9. Verdict

**Pass with changes.**

Findings:

1. The sketch's sub-rungs row for `normalization-singular` names a route that differs from the checked one, and its "Glue statements" line names a different import. Record only.
2. The local instance in `Singular.lean` is unused by the statement and the proof (RT2, RT8), and its docstring says the transport needs it, which is false at the pin.
3. No test lemma in the repository exhibits a nonzero value of either side.
4. Composition with `transport_eq_flasqueModel` and upstream's naturality holds in the needed spelling; a goal-level `rw` of the theorem times out, `.trans` works.
5. The proof's `Other` closure (28 declarations, 9 files) was not on the drift list; it is now (the sketch's "What exists" row and section 8 here).
6. Conventions: no sign enters; a register row was missing and is added.

Changes:

| # | Change | Who | Status |
|---|---|---|---|
| A | Conventions row "Normalization iso against the singular transport" | red team | done (`docs/conventions.md`) |
| B | Drift items in the `Other` row of "What exists" | red team | done (`docs/sketches/cycle-class-multiplicative.md`) |
| C | Sub-rungs row of `normalization-singular`: route `cycleComponentSupportedClassNormalizationIso_apply`, `openRestrictedLowestSectionCohomologyIso_hom`, `complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`, naturality of `supportRelativeCohomologyToSheaf`; "Glue statements" import line: `PointClassNormalization` | maintainer | open |
| D | Drop the local instance from `Singular.lean`, or correct its docstring; the statement's type is unchanged either way (RT2) | prover | open, optional |
| E | Add the non-vacuity example of section 7b and the RT7 identity (`cycleComponentSmoothSupportCoclassSection` in singular form) as named lemmas, at the start of `cycle-class-germ` | prover of `cycle-class-germ` | open |
| F | In `cycle-class-germ`, stay on the ⊤ form with `transport_eq_flasqueModel` and upstream's `…SupportComplement_naturality`; use `.trans`, not goal-level `rw`, on N | prover of `cycle-class-germ` | open (advice) |
