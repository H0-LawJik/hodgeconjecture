# Sketch: `cup-singular-comparison`

Date: 2026-11-25. Front `cup`, decision 0009. The go/no-go rung: upstream's sheaf–singular equivalence carries the Yoneda cup product (`HodgeLadder.Cup.cup`) to the singular cup product, with the sign fixed exactly.

## How upstream's equivalence is built

`rationalCohomologyAddEquivSingularCohomology` (upstream `Other/AlgebraicGeometry/Cohomology/GlobalSections.lean:310`) is a composite:

1. `Hⁿ(X; ℚ) = Extⁿ(ℤ_X, ℚ_X) ≅` hypercohomology of the sheafified singular cochain complex `S•`, through the quasi-isomorphism `constantsToSingularCochainSheafComplex : ℚ_X → S•` (upstream `Definitions/AlgebraicTopology/Singular/Sheaf/Cochain.lean:335`);
2. hypercohomology of `S•` `≅` cohomology of global sections, since `S•` is flasque (`singularCochainSheafComplexInt_isFlasque`), through a K-injective resolution chosen by choice (`GlobalSections.lean:211`);
3. global sections of `S•` `≅` singular cochains of `X(ℂ)` up to the forgotten-cochain comparison (`topOpenForgottenSingularCochainHomologyIso`, `ordinaryRationalSingularCohomologyEquivGlobalSections`).

None of these steps is multiplicative or natural in `X` at the pin.

## Route: right multiplication by a global cocycle

The classical argument avoids the chosen resolution. Let `ι : ℚ_X → S•` be the quasi-isomorphism and `b ∈ Γ(X, S^q)` a cocycle with class `[b]`.

- Right multiplication `r_b : S• → S•[q]`, `c ↦ c ∪ b|_V` on each open `V`, is a chain map up to the sign of the shift convention. It is defined on the presheaf of cochains `V ↦ C•(V; ℚ)` from the cochain cup product, which is natural under restriction, and it passes to the sheafification.
- `r_b ∘ ι` sends the constant section `1` to `b`. In the derived category this gives `r_b ∘ ι = ι[q] ∘ ε([b])`, where `ε([b]) : ℚ_X → ℚ_X[q]` is the `Ext` class of `[b]` under step 1.
- For `a` represented by `ι[p] ∘ ε([a])`, the Yoneda product `ε([a]) ≫ ε([b])[p]` then equals `ε` of the class of `a ∪ b` or `b ∪ a`, up to a sign `±1` depending only on `p`, `q` and Mathlib's shift conventions. The exact order and sign are the rung's content.

## Sub-rungs

| Id | Statement | Needs |
|---|---|---|
| `tauceti-cup-backport` | Tau Ceti's singular cup product and graded commutativity, vendored at the pin | batch H2 of `docs/port-tauceti.md` (in progress) |
| `cochain-cup-upstream` | the cup product on upstream's singular cochains (`linearDualCochainComplex`), through a cochain isomorphism with Tau Ceti's `linearYonedaObj` model | the backport; the isomorphism is short (red team: about ten lines) |
| `cochain-sheaf-right-mult` | for a global cocycle `b`, right multiplication `r_b : S• → S•[q]` as a morphism of complexes of sheaves | cochain cup natural under restriction; sheafification is a functor |
| `ext-class-right-mult` | `r_b ∘ ι = ι[q] ∘ ε([b])` in the derived category | step 1 of upstream's equivalence, unfolded at degree `q` |
| `cup-singular-comparison` | the equivalence carries `cup` to the singular cup product, with order and sign fixed exactly | the four rungs above, and step 2 made compatible with `r_b` |
| `cup-singular-comparison-supported` | the same for `supCup` and the relative singular cup product | Tau Ceti `Cup/Relative` (130 modules) or a direct relative version of `r_b` |

## What could go wrong

- Step 2 uses a resolution chosen by choice. The route above stays in the derived category until global sections, where flasqueness gives the identification; the comparison must not depend on which resolution was chosen.
- Order and sign: Mathlib's `Ext.comp` is diagrammatic, and shifting `ε([b])` by `p` introduces the shift signs of `CochainComplex`. A product identity that holds only up to an unidentified sign does not discharge this rung (decision 0004). Graded commutativity transferred through a wrong sign would still hold, so the sign must be checked against an independent computation: on ℙ¹ × ℙ¹ the product of the two fibre classes is the positive point class (`cup-positive-degree-test`).
- The singular cup product's own convention (front face times back face, no sign) is the one registered in `docs/conventions.md`; the comparison is stated against it.

## Refinement (2026-11-25, after sub-rung 3)

Upstream's step 2 (`rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution`) passes through Mathlib's Hom-complex cohomology classes: a degree-`q` cocycle of `Hom(ℤ[0], K)` is a chain map `ℤ[0] → K⟦q⟧` (`Cocycle.equivHomShift`), and its class in the derived category is `CohomologyClass.toSmallShiftedHom` (no K-injective resolution needed in this direction). This fixes the sign bookkeeping and splits sub-rung 4:

| Id | Statement | Route |
|---|---|---|
| `right-mult-cocycle` | for a global cocycle `b`, right multiplication is a degree-`q` cocycle `R_b` of the Hom complex `Hom(S_ℤ, S_ℤ)`, components `v_p = (−1)^{pq} r_p` for `p ≥ 0` and `0` below | `δ R_b = 0` from `rightMulSheaf_comp_coboundary` (`r ≫ d = d ≫ r`) and Mathlib's formula for `δ`; `S_ℤ` is `S.extend embeddingUpNat` |
| `right-mult-unit` | `ι ≫ R_b`, as a Hom-complex cocycle `ℤ[0] → S_ℤ` of degree `q`, is the cocycle of the global section `b` | `1 ∪ b = b` on cochains (Tau Ceti `cupCochain_constCochain_left`) and naturality of the sheafification unit |
| `ext-class-right-mult` | the class of that cocycle is sent by upstream's step 2 to `[b]`, and `ι[q] ∘ ε([b]) = R_b ∘ ι` in the derived category | unfold `homComplexSingleIntegerIsoGlobalSections` and the K-injective step `e₁` (postcomposition with the resolution commutes with `toSmallShiftedHom`) |

The order and sign of the final comparison then come out of Mathlib's `Cocycle.equivHomShift` and `ShiftedHom.comp` conventions; `cup-positive-degree-test` checks them independently.

Progress: `right-mult-cocycle` and `right-mult-unit` are checked. The unit rung is stated at the level of sheaf maps and global sections (ι⁰ ≫ r_b is the sheafification of r ↦ r · b|_U, and sends the section 1 to b); the passage to upstream's integer-constant Hom complex, through `integerConstantHomAddEquivGlobalSections`, moves into `ext-class-right-mult`.

Progress: `cocycle-class-comp` and `step2-cocycle-class` are checked. Upstream's step 2, applied to the class of a Hom-complex cocycle `z : ℤ[0] → S_ℤ`, gives the homology class of the global section `z` names, whatever resolution was chosen (`globalSectionsOfResolution_mk`). What remains for `ext-class-right-mult`: the cocycle of `b` in that form (from `constTimes_sheafify_one` through `integerConstantHomAddEquivGlobalSections`), and the derived-category identity `ι[q] ∘ ε([b]) = R_b ∘ ι`.
