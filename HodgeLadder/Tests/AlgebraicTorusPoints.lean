module

public import HodgeLadder.Tests.AlgebraicTorus
public import HodgeLadder.Tests.TorusSingular
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# The complex points of `𝔾ₘ²` are `ℂˣ × ℂˣ`

Rung `gm2-points` (sub-rung of `cup-odd-degree-gm2`). Upstream identifies the complex points of
an affine scheme `Spec R` with the complex algebra homomorphisms `R → ℂ`, with the topology of
pointwise convergence (`ComplexPoint.affineSpecHomeomorph`). For `R = ℂ[x, y][(xy)⁻¹]` such a
homomorphism is determined by its values `(φ x, φ y)`, which are nonzero, and every pair of
nonzero numbers occurs (`IsLocalization.liftAlgHom` of polynomial evaluation). Every element of
`R` is a quotient `q / (xy)ⁿ`, so its value is a rational function of `(φ x, φ y)` with
nonvanishing denominator, and the bijection is a homeomorphism onto the subspace
`puncturedSquare` of `ℂ × ℂ`. Consequently every open subset of `𝔾ₘ²(ℂ)` is metrizable, hence
paracompact: the last hypothesis of `cup_singular_comparison` holds for `𝔾ₘ²`.

## Main definitions

* `HodgeLadder.Tests.gmToPair`, `HodgeLadder.Tests.gmOfPair`,
  `HodgeLadder.Tests.gmAlgHomHomeomorph`, `HodgeLadder.Tests.gmHomeomorph`

## Main results

* `HodgeLadder.Tests.gmToPair_gmOfPair`, `HodgeLadder.Tests.gmOfPair_gmToPair`,
  `HodgeLadder.Tests.continuous_gmOfPair`
* instance `ParacompactSpace U` for every open `U` of `ComplexPoint gm2`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLadder.Tests

open MvPolynomial

/-- The element `xy` inverted in `gmRing`. -/
abbrev gmXY : MvPolynomial (Fin 2) ℂ := X 0 * X 1

/-- The coordinate function `x`. -/
abbrev gmX : gmRing := algebraMap (MvPolynomial (Fin 2) ℂ) gmRing (X 0)

/-- The coordinate function `y`. -/
abbrev gmY : gmRing := algebraMap (MvPolynomial (Fin 2) ℂ) gmRing (X 1)

/-- `x` is a unit of `gmRing`. -/
theorem isUnit_gmX : IsUnit gmX := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := gmRing) gmXY
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- `y` is a unit of `gmRing`. -/
theorem isUnit_gmY : IsUnit gmY := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := gmRing) gmXY
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- The coordinates of a complex algebra homomorphism. -/
def gmToPair (φ : gmRing →ₐ[ℂ] ℂ) : puncturedSquare :=
  ⟨(φ gmX, φ gmY), (isUnit_gmX.map φ).ne_zero, (isUnit_gmY.map φ).ne_zero⟩

/-- The point vector of a pair. -/
abbrev pairVec (p : puncturedSquare) : Fin 2 → ℂ := ![p.1.1, p.1.2]

/-- The powers of `xy` evaluate to units at a point of `ℂˣ × ℂˣ`. -/
theorem isUnit_aeval_powers (p : puncturedSquare) (m : Submonoid.powers gmXY) :
    IsUnit (aeval (pairVec p) (m : MvPolynomial (Fin 2) ℂ)) := by
  obtain ⟨_, n, rfl⟩ := m
  simp only [map_pow, map_mul, aeval_X]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero p.2.1 p.2.2))

/-- The complex algebra homomorphism with given coordinates. -/
def gmOfPair (p : puncturedSquare) : gmRing →ₐ[ℂ] ℂ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers gmXY) (f := aeval (pairVec p))
    (isUnit_aeval_powers p)

/-- `gmOfPair p` evaluates polynomials at `p`. -/
theorem gmOfPair_algebraMap (p : puncturedSquare) (q : MvPolynomial (Fin 2) ℂ) :
    gmOfPair p (algebraMap _ gmRing q) = aeval (pairVec p) q := by
  rw [gmOfPair, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- `gmToPair` is a left inverse of `gmOfPair`. -/
theorem gmToPair_gmOfPair (p : puncturedSquare) : gmToPair (gmOfPair p) = p := by
  apply Subtype.ext
  simp [gmToPair, gmOfPair_algebraMap]

/-- `gmOfPair` is a left inverse of `gmToPair`. -/
theorem gmOfPair_gmToPair (φ : gmRing →ₐ[ℂ] ℂ) : gmOfPair (gmToPair φ) = φ := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers gmXY)
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [gmOfPair_algebraMap]
    simp only [aeval_C]
    rw [← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin 2) ℂ) gmRing, AlgHom.commutes]
  · intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [gmOfPair_algebraMap, aeval_X]
    fin_cases i <;> rfl

/-- `gmToPair` is continuous for the topology of pointwise convergence. -/
theorem continuous_gmToPair : Continuous gmToPair :=
  ((ComplexPoint.continuous_affineAlgebraHom_apply gmRing gmX).prodMk
    (ComplexPoint.continuous_affineAlgebraHom_apply gmRing gmY)).subtype_mk _

/-- `pairVec` is continuous. -/
theorem continuous_pairVec : Continuous pairVec := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst.comp continuous_subtype_val
  · exact continuous_snd.comp continuous_subtype_val

/-- `gmOfPair` is continuous: each value is a quotient of two polynomials in the coordinates,
with nonvanishing denominator. -/
theorem continuous_gmOfPair : Continuous gmOfPair := by
  rw [continuous_induced_rng]
  refine continuous_pi fun r => ?_
  obtain ⟨⟨q, m⟩, hr⟩ := IsLocalization.surj (Submonoid.powers gmXY) r
  have key : ∀ p, gmOfPair p r =
      eval (pairVec p) q / eval (pairVec p) (m : MvPolynomial (Fin 2) ℂ) := by
    intro p
    have h := congrArg (gmOfPair p) hr
    rw [map_mul, gmOfPair_algebraMap, gmOfPair_algebraMap] at h
    rw [← coe_aeval_eq_eval]
    change gmOfPair p r = aeval (pairVec p) q / aeval (pairVec p) (m : MvPolynomial (Fin 2) ℂ)
    rw [eq_div_iff (isUnit_aeval_powers p m).ne_zero, ← h]
  change Continuous fun p => gmOfPair p r
  simp_rw [key]
  refine ((MvPolynomial.continuous_eval q).comp continuous_pairVec).div
    ((MvPolynomial.continuous_eval _).comp continuous_pairVec) (fun p => ?_)
  rw [← coe_aeval_eq_eval]
  exact (isUnit_aeval_powers p m).ne_zero

/-- Complex algebra homomorphisms out of `gmRing` are pairs of nonzero complex numbers. -/
def gmAlgHomHomeomorph : (gmRing →ₐ[ℂ] ℂ) ≃ₜ puncturedSquare where
  toFun := gmToPair
  invFun := gmOfPair
  left_inv := gmOfPair_gmToPair
  right_inv := gmToPair_gmOfPair
  continuous_toFun := continuous_gmToPair
  continuous_invFun := continuous_gmOfPair

/-- The complex points of `𝔾ₘ²` are `ℂˣ × ℂˣ`. -/
def gmHomeomorph : ComplexPoint gm2 ≃ₜ puncturedSquare :=
  (ComplexPoint.affineSpecHomeomorph gmRing).trans gmAlgHomHomeomorph

/-- Every open subset of `𝔾ₘ²(ℂ)` is metrizable, hence paracompact. -/
instance (U : TopologicalSpace.Opens (ComplexPoint gm2)) : ParacompactSpace U := by
  have : TopologicalSpace.MetrizableSpace U :=
    (gmHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal).metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric U
  infer_instance

end HodgeLadder.Tests
