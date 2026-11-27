module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
import Other.AlgebraicGeometry.Hodge.Filtration

/-!
# The rational-to-de Rham map is injective

Rung `de-rham-injective` (red team `docs/sketches/cup-hodge-filtration.redteam.md`, 7b and
recommended change 9). Upstream defines, for a smooth integral scheme `X` over `ℂ`, the map
`ι = fieldToDeRhamCohomology ℚ X n : H^n(X(ℂ); ℚ) →+ H_dR^n(X)` as the hypercohomology map of
`ℚ_X[0] → ℂ_X[0] → Ω^•` (by `algebraMap ℚ ℂ`, then constants into zero-forms; no Tate twist, row
"Rational-to-de Rham map and the range of F^p" of `docs/conventions.md`). This file proves that `ι`
is injective in every degree `n`.

The proof is upstream's `fieldToDeRhamCohomology_injective` in its `Other` library, at `K = ℚ`:
`ι` factors as `H^n(X; ℚ) → H^n(X; ℂ)` followed by `complexConstantCohomologyDeRhamEquiv`, an
equivalence from the holomorphic Poincaré lemma; the first map has a left inverse induced by a
`ℚ`-linear retraction `ℂ → ℚ` of `algebraMap` on constant sheaves (`complexToFieldLinear`,
chosen with `Classical.choose`). No finiteness hypothesis on `X` or on the cohomology is used.

## Main results

* `HodgeLadder.fieldToDeRhamCohomology_rat_injective`: `Function.Injective
  (fieldToDeRhamCohomology ℚ X n)` for every smooth integral `X` over `ℂ` and every `n : ℕ`.
* `HodgeLadder.ker_fieldToDeRhamCohomologyLinear_rat`: the same statement as a kernel of the
  `ℚ`-linear map `fieldToDeRhamCohomologyLinear ℚ X n`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- For a smooth integral scheme `X` over `ℂ` and every degree `n`, the map
`ι : H^n(X(ℂ); ℚ) → H_dR^n(X)` induced by `ℚ_X → ℂ_X → Ω⁰` is injective. The hypotheses
`IsIntegral X.left` and `Smooth X.hom` are the ones upstream's definition of `ι` takes. -/
theorem fieldToDeRhamCohomology_rat_injective [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Function.Injective (fieldToDeRhamCohomology ℚ X n) :=
  AlgebraicGeometry.ComplexPoint.fieldToDeRhamCohomology_injective ℚ X n

/-- The kernel of the `ℚ`-linear map `ι : H^n(X(ℂ); ℚ) →ₗ[ℚ] H_dR^n(X)` is zero. -/
theorem ker_fieldToDeRhamCohomologyLinear_rat [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    LinearMap.ker (fieldToDeRhamCohomologyLinear ℚ X n) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (fieldToDeRhamCohomology_rat_injective X n)

end HodgeLadder
