module

public import HodgeLadder.Weil.Space
public import HodgeLadder.Divisor.LefschetzEquality

/-!
# Algebraic Weil classes are Hodge Weil classes

Rung `weil-space`, second file. On a smooth projective integral `X`, the Weil space of an
endomorphism lies in the span of algebraic classes exactly when it lies in `Hdg^1(X; ℚ)`: this is
`le_algebraicCycleClassSpan_one_iff` (Lefschetz (1,1) as an equality) at `S = weilSpace X f d`,
with nothing specific to the Weil space.

Degrees. Upstream's `Hdg^1(X; ℚ)` and `algebraicCycleClassSpan X 1` live in `H^(2 * 1)(X; ℚ)`,
which is `H^2(X; ℚ)` by definitional unfolding of `2 * 1`; the comparison uses the submodule
order directly, with no transport.

## Main results

* `HodgeLadder.Weil.weilSpace_le_algebraic_iff_le_hodge`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Weil

/-- On a smooth projective integral `X`, the Weil space consists of algebraic classes exactly
when it consists of Hodge classes: `Hdg^1(X; ℚ) = algebraicCycleClassSpan X 1` by Lefschetz
(1,1) as an equality. -/
theorem weilSpace_le_algebraic_iff_le_hodge (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (f : X ⟶ X) (d : ℚ) :
    weilSpace X f d ≤ algebraicCycleClassSpan X 1 ↔ weilSpace X f d ≤ Hdg^1(X; ℚ) :=
  le_algebraicCycleClassSpan_one_iff X (weilSpace X f d)

end HodgeLadder.Weil
