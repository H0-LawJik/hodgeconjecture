module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Complex points of a hypersurface quotient

Complex algebra homomorphisms out of `ℂ[Y₁, …, Yₙ] ⧸ (f)`, with upstream's topology of
pointwise convergence (`AlgebraicGeometry.ComplexPoint.affineAlgebraHomTopology`), are the
zeros of `f` with the subspace topology of `ℂⁿ`. Upstream's `mvPolynomialAlgHomHomeomorph` is
the case `f = 0` without the quotient.

## Main definitions

* `HodgeLadder.QuotAlgHom.zeroSet`: `{v ∈ ℂⁿ : f(v) = 0}`.
* `HodgeLadder.QuotAlgHom.quotAlgHomHomeomorph`: `(ℂ[Y] ⧸ (f) →ₐ[ℂ] ℂ) ≃ₜ zeroSet f`.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace HodgeLadder.QuotAlgHom

section ZeroSet

variable {n : ℕ} (f : MvPolynomial (Fin n) ℂ)

/-- The zero set `{v ∈ ℂⁿ : f(v) = 0}`. -/
abbrev zeroSet : Set (Fin n → ℂ) := {v | eval v f = 0}

/-- The coordinates of a complex algebra homomorphism out of `ℂ[Y] ⧸ (f)`. -/
def quotAlgHomCoord (φ : (MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}) →ₐ[ℂ] ℂ) : zeroSet f :=
  ⟨fun j => φ (Ideal.Quotient.mk _ (X j)), by
    have h : φ.comp (Ideal.Quotient.mkₐ ℂ (Ideal.span {f})) =
        aeval fun j => φ (Ideal.Quotient.mk _ (X j)) :=
      MvPolynomial.algHom_ext fun j => by simp
    have h1 := congrArg (fun ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => ψ f) h
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
    change eval _ f = 0
    rw [← aeval_eq_eval, ← h1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f),
      map_zero]⟩

/-- The complex algebra homomorphism `ℂ[Y] ⧸ (f) → ℂ` of evaluation at a zero `v` of `f`. -/
def quotAlgHomOfZero (v : zeroSet f) : (MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (aeval v.1) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hv : eval v.1 f = 0 := v.2
    rw [map_mul, aeval_eq_eval, hv, mul_zero]

/-- `quotAlgHomOfZero v` evaluates polynomials at `v`. -/
@[simp]
theorem quotAlgHomOfZero_mk (v : zeroSet f) (p : MvPolynomial (Fin n) ℂ) :
    quotAlgHomOfZero f v (Ideal.Quotient.mk _ p) = eval v.1 p := by
  rfl

/-- Complex algebra homomorphisms out of `ℂ[Y] ⧸ (f)` are the zeros of `f`, homeomorphically
(pointwise convergence on the left, the subspace topology of `ℂⁿ` on the right). -/
def quotAlgHomHomeomorph :
    ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {f}) →ₐ[ℂ] ℂ) ≃ₜ zeroSet f where
  toFun := quotAlgHomCoord f
  invFun := quotAlgHomOfZero f
  left_inv φ := by
    apply AlgHom.toRingHom_injective
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [quotAlgHomCoord, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
        quotAlgHomOfZero_mk, eval_C]
      exact (φ.commutes c).symm
    · intro j
      simp [quotAlgHomCoord]
  right_inv v := by
    apply Subtype.ext
    funext j
    simp [quotAlgHomCoord]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    exact AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply _ _
  continuous_invFun := by
    rw [continuous_induced_rng]
    refine continuous_pi fun r => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    change Continuous fun v : zeroSet f => quotAlgHomOfZero f v (Ideal.Quotient.mk _ p)
    simp_rw [quotAlgHomOfZero_mk]
    exact (MvPolynomial.continuous_eval p).comp continuous_subtype_val

end ZeroSet

end HodgeLadder.QuotAlgHom
