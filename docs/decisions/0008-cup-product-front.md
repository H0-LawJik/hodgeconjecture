# 0008. Open the cup-product front

Date: 2026-11-25. Status: accepted.

## Context

The Markman inventory (`docs/notes/2026-11-25-markman-inventory.md`) found one gap that blocks every step toward Weil classes and also blocks M3 (`hard-lefschetz`, `dimension-le-three`): upstream's rational cohomology `H^n(X; ℚ)` has no ring structure. A library survey found no cup product on `Sheaf.H` in Mathlib at the pin, in upstream, or in this repository's port.

Upstream defines `H^n(X; ℚ)` as `Ext^n(ℤ_X, ℚ_X)` in sheaves of abelian groups on `X(ℂ)`. Three routes to a product were compared: Yoneda composition of `Ext` classes, a tensor product of sheaves, and cochain-level cup products on singular cohomology.

## Decision

Open front `cup` on the Yoneda route. Through the adjunction between sheaves of ℚ-vector spaces and sheaves of abelian groups, `H^n(X; ℚ) ≅ Ext^n(ℚ_X, ℚ_X)` in sheaves of ℚ-vector spaces; Mathlib's `Ext.comp` on the right side is associative, unital and ℚ-bilinear. The cup product is defined through this isomorphism. Graded commutativity is a separate rung, because none of the three routes has it at the pin.

The tensor route is kept as the expected input for graded commutativity. The cochain route is set aside: a cochain product would also need a multiplicative comparison with `Sheaf.H`, which nothing at the pin provides.

## Consequences

- Rungs, in order: `rational-ext-equiv` (the isomorphism), `cup-product` (definition, associativity, unit, bilinearity), `cup-graded-commutative`, then `cycle-class-multiplicative`.
- The order of the factors and the sign of graded commutativity go into `docs/conventions.md` with the first definition.
- Kill criterion: the front is closed if the product cannot be shown compatible with the cycle class map (`cycle-class-multiplicative`) on upstream definitions, since products of algebraic classes are the reason to have it.
- Mathlib-level pieces (exactness of `sheafCompose (forget₂ (ModuleCat ℚ) AddCommGrpCat)`, the `Ext` comparison) are logged in `docs/gaps.md` for upstreaming.
