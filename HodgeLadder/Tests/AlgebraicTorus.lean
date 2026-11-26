module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The algebraic torus `𝔾ₘ²` over ℂ

Rung `gm2-witness` (sub-rung of `cup-odd-degree-gm2`). The algebraic torus
`𝔾ₘ² = Spec ℂ[x, y][(xy)⁻¹]`, as an object of `Over (Spec ℂ)` through upstream's
`ComplexPoint.affineSpecStructureMap`, is integral and smooth, and its analytification is
Hausdorff (upstream's `ComplexPoint.t2Space_of_isAffine`). Smoothness: `ℂ[x, y]` is formally
smooth and of finite presentation over ℂ, and both properties pass to a localization away from
an element (Mathlib instances). It is affine and not projective; the comparison theorem
`cup_singular_comparison` does not ask for projectivity.

## Main definitions

* `HodgeLadder.Tests.gmRing`, `HodgeLadder.Tests.gm2`

## Main results

* instances `IsDomain gmRing`, `IsIntegral gm2.left`, `Smooth gm2.hom`, `IsAffine gm2.left`,
  `T2Space (ComplexPoint gm2)`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLadder.Tests

/-- The coordinate ring `ℂ[x, y][(xy)⁻¹]` of `𝔾ₘ²`. -/
abbrev gmRing : Type :=
  Localization.Away (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)

/-- The algebraic torus `𝔾ₘ²` over `Spec ℂ`. -/
abbrev gm2 : Over (Spec ↧ℂ) := Over.mk (ComplexPoint.affineSpecStructureMap gmRing)

instance : IsDomain gmRing :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)))

instance : IsIntegral gm2.left := by dsimp [gm2]; infer_instance

instance : Smooth gm2.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ gmRing)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap ℂ gmRing).Smooth
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

instance : IsAffine gm2.left := by dsimp [gm2]; infer_instance

instance : T2Space (ComplexPoint gm2) := ComplexPoint.t2Space_of_isAffine gm2

end HodgeLadder.Tests
