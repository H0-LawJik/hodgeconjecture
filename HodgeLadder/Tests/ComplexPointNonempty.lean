module

public import HodgeLadder.General.ComplexPoint
public import HodgeLadder.Hodge.WedgeSheafify
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Nonvacuity tests without a complex-point hypothesis

Rung `complex-point-nonempty`, corollaries. The general nonvacuity tests of rung
`de-rham-unit-nonzero` (`HodgeLadder.Tests.DeRhamUnitNonzero`) and `wedgeSheaf_ne_zero` (rung
`wedge-sheafify`) take `[Nonempty (ComplexPoint X)]` as an argument. With
`HodgeLadder.nonempty_complexPoint` they hold on every smooth integral `X`. Each primed form is
its original with that binder deleted and nothing else changed.

Wherever `Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected` is imported (the library
root reaches it through `HodgeLadder.Tests.CodimensionZero`), the unprimed originals already apply on a smooth integral `X`, with the point
found by upstream's instance `AlgebraicGeometry.ComplexPoint.instNonemptyComplexPoint`. The
primed forms record that the hypothesis is removable more than they add reach.

The file also checks that `Nonempty X.left` cannot be dropped from
`HodgeLadder.nonempty_complexPoint_of_locallyOfFiniteType`: the empty scheme over `Spec ℂ` has
no complex point.

## Main results

* `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_ne_zero'`,
  `HodgeLadder.Tests.rationalDeRhamUnit_ne_zero'`, `HodgeLadder.wedgeSheaf_ne_zero'`: the
  nonvacuity tests on every smooth integral `X`
* `HodgeLadder.Tests.nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero'`,
  `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_ne_neg'`,
  `HodgeLadder.Tests.rationalDeRhamUnit_ne_neg'`: the non-torsion form and the sign separations
* `HodgeLadder.Tests.not_nonempty_complexPoint_empty`: the empty scheme has no complex point
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder

namespace Tests

/-- Upstream's unit `K_X[0] ⟶ Ω•(X)` is nonzero on every smooth integral `X`, for every field
`K` embedded in `ℂ`: `fieldToHolomorphicDeRhamComplexInt_ne_zero` with the complex point
supplied by `nonempty_complexPoint`. Where upstream's `instNonemptyComplexPoint` is imported, the
original applies directly; this form records that the hypothesis is removable. -/
theorem fieldToHolomorphicDeRhamComplexInt_ne_zero' (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    fieldToHolomorphicDeRhamComplexInt K X ≠ 0 :=
  have := nonempty_complexPoint X
  fieldToHolomorphicDeRhamComplexInt_ne_zero K X

/-- The rational unit `rationalDeRhamUnit X` is nonzero on every smooth integral `X`. Where
upstream's `instNonemptyComplexPoint` is imported, the original applies directly. -/
theorem rationalDeRhamUnit_ne_zero' (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    rationalDeRhamUnit X ≠ 0 :=
  have := nonempty_complexPoint X
  rationalDeRhamUnit_ne_zero X

/-- Non-torsion form of upstream's unit on every smooth integral `X`: `n • ι ≠ 0` for
`n ≠ 0`. Where upstream's `instNonemptyComplexPoint` is imported, the original applies
directly. -/
theorem nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero' (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] {n : ℕ} (hn : n ≠ 0) :
    n • fieldToHolomorphicDeRhamComplexInt K X ≠ 0 :=
  have := nonempty_complexPoint X
  nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero K X hn

/-- **Sign separation** on every smooth integral `X`: upstream's unit is not its own
negative. Where upstream's `instNonemptyComplexPoint` is imported, the original applies
directly. -/
theorem fieldToHolomorphicDeRhamComplexInt_ne_neg' (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    fieldToHolomorphicDeRhamComplexInt ℚ X ≠ -fieldToHolomorphicDeRhamComplexInt ℚ X :=
  have := nonempty_complexPoint X
  fieldToHolomorphicDeRhamComplexInt_ne_neg X

/-- **Sign separation for the rational unit** on every smooth integral `X`. Where upstream's
`instNonemptyComplexPoint` is imported, the original applies directly. -/
theorem rationalDeRhamUnit_ne_neg' (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    rationalDeRhamUnit X ≠ -rationalDeRhamUnit X :=
  have := nonempty_complexPoint X
  rationalDeRhamUnit_ne_neg X

/-- **The nonemptiness hypothesis is needed.** The empty scheme over `Spec ℂ`, which is locally
of finite type, has no complex point: a complex point evaluated at the closed point of `Spec ℂ`
would be a point of the empty scheme. -/
theorem not_nonempty_complexPoint_empty :
    ¬ Nonempty (ComplexPoint (Over.mk (Scheme.emptyTo (Spec ↧ℂ)))) := by
  rintro ⟨z⟩
  exact (z.left (IsLocalRing.closedPoint ℂ)).elim

end Tests

/-- The sheafified wedge `Ω⁰_ℚ ⊗ Ω⁰_ℚ ⟶ Ω⁰_ℚ` is nonzero on every smooth integral `X`. Where
upstream's `instNonemptyComplexPoint` is imported, the original applies directly. -/
theorem wedgeSheaf_ne_zero' (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    wedgeSheaf X (dim X.left) 0 0 ≠ 0 :=
  have := nonempty_complexPoint X
  wedgeSheaf_ne_zero X

end HodgeLadder
