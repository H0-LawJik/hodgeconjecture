# Conventions register

Every sign and normalization choice that a statement or proof on this ladder depends on, where it is fixed, and whether a result's truth depends on it. The red team fills and maintains this file; a rung that relies on a convention not listed here does not pass review.

## Why this exists

In October 2026 three manuscripts claiming cases of the Hodge conjecture were withdrawn because a cited result's sign convention was applied with the wrong sign (Lekili and Sheridan, arXiv:2610.30976). A kernel-checked Lean proof cannot pass with that kind of error inside it. A convention can still hurt a checked result in three ways, and each one is a red-team target:

1. **Definition drift.** A definition fixes a convention different from the literature's, so the checked theorem is about a different object. Example to test: a fundamental class normalized with the opposite orientation is harmless for a span, harmful for an equality of classes or a degree.
2. **Assumed results.** A `Prop` hypothesis or a cited input encodes a convention from a paper. If a theorem is conditional on such an input, the input's convention must match the definitions it is stated against.
3. **Statement-of-record drift between pins.** A proof checked against one upstream commit proves the statement as defined at that commit. A later refactor can change the definition under the same name.

## Register

| Convention | Fixed where | Choice | Results whose truth depends on it | Status |
|---|---|---|---|---|
| Exponential sequence | upstream Lefschetz stack, PR [6/11] | ℤ → 𝒪 by n ↦ n; 𝒪 → 𝒪ˣ by f ↦ exp(2πi f) | none for span statements; equalities between c₁ and cycle classes | read from source (red team 2026-11-24) |
| Connecting homomorphism sign | Mathlib `CategoryTheory.Sheaf.H.δ` (`ExactSequences.lean`) | c₁ is `δ` with no extra sign | same as above | read from source |
| Complex orientation of ℂ^p | upstream `Definitions/AlgebraicTopology/LocalHomology/ComplexClass.lean` | consecutive real and imaginary coordinates; the reference simplex carries sign (−1)^d, positive for d = 2p | fundamental-class equalities and degrees | read from source |
| Fundamental-class normalization | upstream `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean` | local classes evaluate to 1 on complex orientation classes of normal spaces | equalities and degrees | recorded |
| Cycle-class model | upstream main `2ead713` (Ext and `relH`) versus Lefschetz branch `c7d5c94b` (injective-resolution model) | the two `cycleComponentSheafClass` constructions agree up to a nonzero rational scalar, by an argument not yet formalized; the branch itself proves a −1 between two support models (`BettiSupportedOrdinarySign.lean:35`) | none for the inclusion `LefschetzOneOne`; every identity that mentions the cycle class, including [D] = c₁, must be re-proved exactly on the pinned model (rung `divisor-chern-exact`); a bridge up to scalar does not satisfy decision 0004 | **open hazard; the port resolves it** |
| Winding number | upstream Lefschetz stack, PR [6/11] | (1/2πi)∮ d log g | the divisor–Chern identity | read from source |
| Divisor–Chern identity | upstream Lefschetz stack, PR [9/11] | for every Cartier datum c representing L (L ≅ 𝒪(D)) with L^an matching the extension: cycle class of `c.divisor` equals the rational image of `firstChernClass`, sign + | an equality; holds on the branch's cycle-class model only until re-proved on main's | read from source |
| Hodge filtration | upstream `Definitions/AlgebraicGeometry/Hodge/Filtration.lean` | `F^p` is the image of hypercohomology of holomorphic forms of degree ≥ p (stupid truncation) | which classes are Hodge classes | recorded |
| Hodge classes | same file, `hodgeClasses` | rational classes whose de Rham image lies in `F^p ∩ conj F^p` | the statement | recorded |

## Rules

- Identities between classes are proved exactly (decision 0004). A rung whose statement is an identity is not discharged by "equal up to a nonzero scalar"; the sign and the normalization go in its docstring and in a row here.

- A rung statement that is an equality of classes names its sign convention in the docstring and cites the row here.
- A conditional theorem lists every assumed input and the convention each input uses.
- On every upstream pin bump, the red team diffs the definitions in this table between the old and new pin and records the result in the handoff.
