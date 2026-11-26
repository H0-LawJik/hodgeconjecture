# Sketch: `cup-singular-comparison` (supported case)

Date: 2026-11-25. Front `cup`, decision 0009, rung 4 second half. The absolute case is checked (`cup-singular-comparison-absolute`, `HodgeLadder.Cup.cup_singular_comparison`): `Ψ (x ∪ y) = (−1)^{pq} · cupSing (Ψ x) (Ψ y)`.

## Target

For a closed `Z ⊆ X(ℂ)`, upstream's `rationalCohomologyWithSupportAddEquivSingular X Z hZ n : H_[Z]^n(X; ℚ) ≃+ CohomologyWithSupport ℚ X(ℂ) Z n` (`Other/AlgebraicGeometry/Cohomology/SupportHypercohomology.lean`), with `CohomologyWithSupport` the relative singular cohomology `H^n(X(ℂ), X(ℂ) ∖ Z)`. The statement: `Ψ_Z (supCup α y) = (−1)^{pq} · relCupSing (Ψ_Z α) (Ψ y)`, where `relCupSing : H^p(X, X ∖ Z) × H^q(X) → H^{p+q}(X, X ∖ Z)` is the relative singular cup product.

## How upstream's supported equivalence is built

1. support hypercohomology of the natural singular support cone (the mapping cone of the restriction `S → j_* (S|_{X∖Z})`, shifted by `−1`), through `rationalSupportHypercohomologyAddEquivNaturalSingularCone`;
2. global sections of that cone (flasque terms), `hypercohomologyAddEquivGlobalSections`;
3. the raw restriction cone of top-open cochains, `globalRawSupportConeToGlobalNaturalSingularCone` (a quasi-isomorphism);
4. the relative cochain cone, `globalRawSingularRestrictionConeCohomologyEquivSupport`.

## Route

The absolute proof transfers once right multiplication is defined on the cone: `R_b` on `S` and on `j_*(S|_{X∖Z})` (multiplication by `b|_{X∖Z}`) commute with the restriction, so they induce a cocycle of the Hom complex of the cone. The endomorphism-class identity `ε_y ≫ ι = ι ≫ R_b` is the absolute one (`end-class-right-mult`) and is reused.

| Id | Statement | Route |
|---|---|---|
| `relative-singular-cup` | the relative cup `H^p(X, A) × H^q(X) → H^{p+q}(X, A)` on upstream's `RelativeCochainComplex` (duals of the chain cokernel), compatible with forgetting `A` and `cupSing` | the cochain cup of a cochain vanishing on `A`-chains with any cochain vanishes on `A`-chains (front faces of simplices in `A` lie in `A`); Tau Ceti `cupCochain` |
| `support-cone-right-mult` | `R_b` on the support cone, as a Hom-complex cocycle, compatible with the cone's inclusion and projection | naturality of `rightMulApp` under restriction (`rightMulApp_naturality`), mapping-cone functoriality |
| `support-ab-yoneda` | `supCup α y = α ≫ forgetEnd (e y)` in sheaves of abelian groups, read through upstream's relative `Ext` | as `ab-ext-yoneda`, with `supCupY` in place of `cupY` |
| `support-named-class` | upstream's supported steps send the class named by a relative cocycle to its relative singular class | as `step3-named-class`, through the four steps above |
| `cup-singular-comparison` (supported) | the target statement | as `cup-singular-comparison-absolute` |

## What could go wrong

- The support cone is shifted by `−1`; the shift sign of `CochainComplex.mappingCone` enters the comparison, and the predicted sign `(−1)^{pq}` may acquire a further factor. Register the cone convention in `docs/conventions.md` before posting the target statement.
- Upstream's raw cone uses top-open cochains of `X ∖ Z` (pushforward), so `cup-top-open` needs a relative version through the open `X ∖ Z` as well as `⊤`.

## Revision (2026-11-25): the cone route fails, use supported sections

Reading upstream further shows two problems with the route above.

- The support cone is `Cone(S → j_* I_U)` with `I_U` a chosen injective resolution of `ℚ_U` (`complementSingularToInjectiveResolution`). Right multiplication is defined on `S` and on the singular cochains of the complement, not on `I_U`, and mapping cones are not functorial in the derived category. So `support-cone-right-mult` is retired.
- `supCup` is defined on `H_[Z]^n(X; ℚ) = relH`, the `Ext` out of the pair sheaf, while `rationalCohomologyWithSupportAddEquivSingular` starts from `RationalCohomologyWithSupport`, the hypercohomology of the cone. The two models of cohomology with support are different objects at the pin.

Upstream's statement library has a strict model for `relH`: `relHAddEquivSupportedSectionsHomologyOfFlasque` (`Definitions/AlgebraicTopology/Support/CohomologyFlasqueModel.lean`) identifies `relH` with the cohomology of the sections supported in `Z` of a flasque resolution `F[0] → K` with mono augmentation. For `K = S_ℤ` (flasque, `singularCochainSheafComplexInt_isFlasque`; mono, `rationalToSingularCochainComplexInt_mono`), right multiplication by a global cocycle preserves supported sections, so the absolute argument transfers without cones.

| Id | Statement | Route |
|---|---|---|
| `supported-sections-right-mult` | `R_b` preserves the sections of `S` supported in `Z`, as a map of complexes `Γ_Z(S) → Γ_Z(S)[q]` | supported sections are the kernel of restriction to `X ∖ Z`; `rightMulApp_naturality` |
| `supported-sections-class` | through `relHAddEquivSupportedSectionsHomologyOfFlasque`, `supCup α y` is the class of the supported cocycle of `α` times `b` | as `cup-global-comparison`, with `relH` in place of `H` and `support-ab-yoneda` |
| `supported-singular-model` | the cohomology of `Γ_Z(S)` is relative singular cohomology `H^n(X, X ∖ Z)`, compatibly with `relCupSing` | upstream `Other/AlgebraicTopology/Support/SingularCohomologySheafComparison.lean`; `relative-singular-cup` |
| `cup-singular-comparison` (supported) | `supCup` against `relCupSing` through the composite of the two models | the three rows above |

Which equivalence `H_[Z]^n(X; ℚ) ≃ H^n(X, X ∖ Z)` is the one of record for the supported statement is a decision for the orchestrator: the composite above, or upstream's cone equivalence after a separate identification of `relH` with `RationalCohomologyWithSupport`.

### Refinement of the supported-sections route

Upstream's `relHAddEquivSupportedSectionsHomology` (`Definitions/AlgebraicTopology/Support/CohomologyInjectiveModel.lean`) has the shape of the absolute step 2, with the pair sheaf `P` in place of `ℤ_X`: `Ext.homAddEquiv`, postcomposition with `Q(ι)`, `kInjectiveDerivedHomAddEquivCohomologyClass`, `homologyAddEquiv`, then `homComplexPairSheafIsoSupportedSections`. `relHAddEquivSupportedSectionsHomologyOfFlasque` transports it to a flasque resolution `K` through `resolutionToInjective`. So the absolute lemmas transfer:

| Absolute input | Supported analogue |
|---|---|
| `step2-cocycle-class` (`globalSectionsOfResolution_mk`) | the flasque model sends the class of a cocycle `z : P[0] → S_ℤ` to the supported-sections class of `z` |
| `cocycle-class-mul` | unchanged (general) |
| `end-class-right-mult` | unchanged: `ε_y ≫ ι = ι ≫ R_b` is a statement about `ℚ_X` |
| `named-cocycle-comp` | `cocycleComp z R_b` is, in supported sections, `(−1)^{pq}` times right multiplication by `b` on the supported cocycle |

Right multiplication on supported sections is `sheafSectionsSupportedOutside` applied to `rightMulHom`, since that functor acts on morphisms of sheaves. The step from `Ψ_Z α`'s representing cocycle to an Ext class with `α.hom ≫ Q(ι)⟦p⟧ = [z]` is where `support-ab-yoneda` enters.

### Progress (2026-11-25)

- `supported-step2-cocycle-class` checked (`HodgeLadder/Cup/SupportedStep2.lean`).
- `supported-sections-class` checked (`HodgeLadder/Cup/SupportedClass.lean`). The argument is the absolute one with the hypercohomology bridge removed: the supported class `α` lives directly in `Ext(P, ℚ_X)`, so only `end-class-right-mult` and the shifted-hom algebra enter, and no sign appears at this step. The sign `(−1)^{pq}` enters in `supported-named-cocycle-comp`, as in the absolute case.
- Still to show: every supported class is represented by a cocycle out of the pair sheaf. This follows from the bijectivity of upstream's flasque model together with `relHSupportedOfFlasque_mk`, and is part of the final supported rung.
