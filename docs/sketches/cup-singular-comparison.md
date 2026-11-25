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
