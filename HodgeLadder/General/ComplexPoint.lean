module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A nonempty scheme locally of finite type over `ℂ` has a complex point

Rung `complex-point-nonempty` (red team of `de-rham-unit-nonzero`, change 5). Upstream's
`ComplexPoint X` is `Point ℂ X`, the morphisms `Spec ℂ ⟶ X.left` over `Spec ℂ`. This file shows
that this type is inhabited as soon as `X.left` is nonempty and `X.hom` is locally of finite type,
and so on every smooth integral `X`. The corollaries that drop the `Nonempty (ComplexPoint X)`
hypotheses of the nonvacuity tests of rungs `de-rham-unit-nonzero` and `wedge-sheafify` are in
`HodgeLadder.Tests.ComplexPointNonempty`.

## Route

A scheme locally of finite type over a field is a Jacobson space
(`LocallyOfFiniteType.jacobsonSpace`), so every nonempty locally closed subset, here the whole
space, contains a closed point (`nonempty_inter_closedPoints`). Since `ℂ` is algebraically closed,
Mathlib's `pointEquivClosedPoint` (the Nullstellensatz form: the residue field of a closed point
is finite over `ℂ`, hence equal to `ℂ`) turns that closed point into a section
`Spec ℂ ⟶ X.left` of the structure morphism, which is a complex point.

## Relation to upstream

This file imports no `Other` module and no ladder module. Upstream's instance
`AlgebraicGeometry.ComplexPoint.instNonemptyComplexPoint` (in
`Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected`) proves `nonempty_complexPoint` by
`inferInstance` and is already in the library root's closure, through
`HodgeLadder.Tests.CodimensionZero`. The local copy is kept for the weaker hypothesis
`Nonempty X.left`, the `iff`, and the light import.

## Main results

* `HodgeLadder.nonempty_complexPoint_of_locallyOfFiniteType`: `Nonempty X.left` and
  `LocallyOfFiniteType X.hom` give `Nonempty (ComplexPoint X)`
* `HodgeLadder.nonempty_complexPoint_iff`: under `LocallyOfFiniteType X.hom`, complex points
  exist exactly when `X.left` is nonempty
* `HodgeLadder.nonempty_complexPoint`: the rung's statement, from `IsIntegral X.left` and
  `Smooth X.hom`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLadder

/-- **Complex points exist.** A nonempty scheme locally of finite type over `ℂ` has a complex
point: its space is Jacobson, so it has a closed point, and the residue field there is `ℂ`
because `ℂ` is algebraically closed (`pointEquivClosedPoint`). -/
theorem nonempty_complexPoint_of_locallyOfFiniteType (X : Over (Spec ↧ℂ)) [Nonempty X.left]
    [LocallyOfFiniteType X.hom] : Nonempty (ComplexPoint X) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := X.left) (Z := Set.univ)
    Set.univ_nonempty isOpen_univ.isLocallyClosed
  let z := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
  exact ⟨Over.homMk z.1 z.2⟩

/-- **Sharpness.** For `X.hom` locally of finite type, `X` has a complex point exactly when
`X.left` is nonempty; the converse direction evaluates a complex point at the closed point of
`Spec ℂ`. -/
theorem nonempty_complexPoint_iff (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] :
    Nonempty (ComplexPoint X) ↔ Nonempty X.left :=
  ⟨fun ⟨z⟩ => ⟨z.left (IsLocalRing.closedPoint ℂ)⟩, fun _ =>
    nonempty_complexPoint_of_locallyOfFiniteType X⟩

/-- **The rung's statement.** A smooth integral scheme over `ℂ` has a complex point. Integral
schemes are nonempty and smooth morphisms are locally of finite type. Upstream's instance
`AlgebraicGeometry.ComplexPoint.instNonemptyComplexPoint` proves the same statement. -/
theorem nonempty_complexPoint (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Nonempty (ComplexPoint X) :=
  nonempty_complexPoint_of_locallyOfFiniteType X

end HodgeLadder
