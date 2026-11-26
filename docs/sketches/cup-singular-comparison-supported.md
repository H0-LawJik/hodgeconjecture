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
