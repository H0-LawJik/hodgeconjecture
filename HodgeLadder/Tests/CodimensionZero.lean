module

public import HodgeLadder.CycleClass.Statements
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing

/-!
# The equality form holds non-vacuously in codimension zero

For every smooth projective integral `X` over `ℂ`, the rational Hodge classes of degree zero equal
the span of cycle classes in codimension zero, and that span is not zero: it contains the class of
`X` itself, which upstream proves nonzero. This is the equality form of decision 0004 in one
codimension, on upstream definitions, from upstream's sanity theorems in its `Other` library.

## Main results

* `HodgeLadder.Tests.hodge_eq_span_zero`: `Hdg^0(X; ℚ) = algebraicCycleClassSpan X 0`.
* `HodgeLadder.Tests.span_zero_ne_bot`: `algebraicCycleClassSpan X 0 ≠ ⊥`.
* `HodgeLadder.Tests.hodge_zero_ne_bot`: `Hdg^0(X; ℚ) ≠ ⊥`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- In codimension zero, the Hodge classes are exactly the span of cycle classes. -/
theorem hodge_eq_span_zero : Hdg^0(X; ℚ) = algebraicCycleClassSpan X 0 :=
  rationalHodgeClasses_zero_eq_algebraicCycleClassSpan X

/-- The codimension-zero span is not zero: it contains the nonzero class of `X`. -/
theorem span_zero_ne_bot : algebraicCycleClassSpan X 0 ≠ ⊥ := by
  intro h
  have hle : Submodule.span ℚ
      {cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint_eq_zero X)} ≤
      algebraicCycleClassSpan X 0 := by
    unfold algebraicCycleClassSpan
    exact le_sSup ⟨genericPoint X.left, coheight_genericPoint_eq_zero X, rfl⟩
  have hmem := hle (Submodule.mem_span_singleton_self _)
  rw [h, Submodule.mem_bot] at hmem
  exact cycleComponentSheafClass_genericPoint_ne_zero X hmem

/-- Hence the degree-zero Hodge classes are not zero either. -/
theorem hodge_zero_ne_bot : Hdg^0(X; ℚ) ≠ ⊥ := by
  rw [hodge_eq_span_zero]; exact span_zero_ne_bot X

end HodgeLadder.Tests
