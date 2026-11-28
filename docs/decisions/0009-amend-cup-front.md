# 0009. Amend the cup-product front: comparison with the singular cup product

Date: 2026-11-25. Status: accepted; amended by decision 0010; closed by decision 0012. Amends decision 0008.

## Context

The red team on front `cup` (`docs/sketches/cup-front.redteam.md`) found:

- Upstream, at the pin, has a checked ℚ-linear equivalence between `H^n(X; ℚ)` and singular cohomology (`rationalCohomologyLinearEquivSingularCohomology`). It is not natural in `X` and nothing about it is multiplicative.
- Tau Ceti has a singular cup product with graded commutativity, a relative cup product on complements of closed supports, and naturality in `X`. These are AI-written and checked with the standard axioms at Tau Ceti's own pin. Their cochains differ from upstream's by a short isomorphism.
- Upstream's cycle classes live on the `Ext` side, with their normalization on the singular side. The equivalences connecting the two sides are only additive.
- Every route to `cycle-class-multiplicative`, the front's kill criterion, needs the sheaf-to-singular equivalences to carry the Yoneda product to the singular cup product, with an exactly fixed sign.
- The checked laws of `cup-product` (associative, unital, biadditive) are also satisfied by the square-zero product. The present non-vacuity test uses only the unit law, so it does not rule that product out.

## Decision

Keep the Yoneda definition of the cup product. Add the comparison as an explicit rung, and order the front:

1. `cup-pullback`: pullback along a morphism on `H^*(X; ℚ)` is multiplicative (from the port's `H.pullback` and `Ext.mapExactFunctor_comp`).
2. `sheaf-tensor-exact`: the tensor product of sheaves of ℚ-vector spaces is exact in each variable.
3. `supported-cup`: product of a supported class with an absolute class.
4. `cup-singular-comparison`: upstream's equivalences carry the Yoneda product to Tau Ceti's singular cup product, absolute and supported, with the sign fixed exactly. It needs a backport of Tau Ceti's cup files into `port/`.
5. `local-class-product`: product of normalized local classes.
6. `cycle-class-multiplicative`: the transversal case on ℙ¹ × ℙ¹ first.
7. `cup-graded-commutative`: transferred through rung 4, or by Hilton–Eckmann if its interchange lemma becomes available.
8. `cup-hodge-filtration`: products respect the Hodge filtration, so products of Hodge classes are Hodge.

A test rung `cup-positive-degree-test` (pr₁*[pt] ∪ pr₂*[pt] ≠ 0 on ℙ¹ × ℙ¹) closes the vacuity gap.

## Consequences

- Kill criterion changed: the front closes if the sign in `cup-singular-comparison` cannot be fixed exactly, or if `cycle-class-multiplicative` fails on upstream definitions.
- T1 of the Markman inventory needs rungs 1, 7 and 8.
- Conventions to register before rung 4: the factor order of the Yoneda product, the singular cup (front face times back face, no sign), the coboundary (δφ = φ ∘ ∂, no sign), upstream's cap product, and the sign of the cross product of complex orientations.
- Amended by decision 0010 (2026-11-26): rungs 5 and 6 form the product of two supported classes on the singular side with `relCup2` on upstream's triad excision, and the general-V product formula is off the critical path of rung 6; ℙ² with two coordinate lines is the first transversal case and the first positive-degree test, before ℙ¹ × ℙ¹; a reopening on a corrected normalization is a new rung, with the original marked `refuted`.
