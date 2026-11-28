module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Affine hypersurfaces with nowhere vanishing gradient are smooth

A Jacobian criterion for one equation, by explicit presentations. Let `f ∈ R[Xᵢ | i ∈ σ]` with
`σ` finite and `A = R[Xᵢ] ⧸ (f)`. Inverting the partial derivative `∂f/∂Xᵢ` in `A` gives a
submersive presentation of `A[1/∂ᵢf]` over `R`: the naive presentation of `A` (variables `σ`,
one relation `f`, attached to the variable `Xᵢ`) composed with the presentation of the localization
away from `∂ᵢf` (one variable `T`, one relation `(∂ᵢf) T − 1`). Its Jacobian is
`∂ᵢf · ∂ᵢf`, a unit in `A[1/∂ᵢf]`, and its dimension is `#σ − 1`. So, when the classes of the
partial derivatives generate the unit ideal of `A`, the map `R → A` is locally standard smooth of
relative dimension `#σ − 1`, and `Spec A ⟶ Spec R` is smooth of that relative dimension.

Mathlib at the pin has the presentations (`Algebra.PreSubmersivePresentation.naive`,
`localizationAway`, `comp`) and no Jacobian criterion phrased through the ideal of partial
derivatives; this file is that step for a single equation.

## Main definitions

* `HodgeLadder.HypersurfaceSmooth.naivePresentation`, `awayPresentation`

## Main results

* `HodgeLadder.HypersurfaceSmooth.naivePresentation_jacobian`: the Jacobian of the naive
  presentation is the class of `∂ᵢf`.
* `HodgeLadder.HypersurfaceSmooth.isStandardSmoothOfRelativeDimension_away`
* `HodgeLadder.HypersurfaceSmooth.locally`, `smoothOfRelativeDimension_spec`: if the classes of
  `∂ᵢf` generate the unit ideal of `R[Xᵢ] ⧸ (f)`, then `Spec (R[Xᵢ] ⧸ (f)) ⟶ Spec R` is smooth of
  relative dimension `#σ − 1`.
-/

@[expose] public noncomputable section

open Algebra MvPolynomial

namespace HodgeLadder.HypersurfaceSmooth

universe u

variable {R : Type u} [CommRing R] {σ : Type u} (f : MvPolynomial σ R)

/-- The naive presentation of `R[Xᵢ] ⧸ (f)` with variables `σ` and the single relation `f`,
attached to the variable `Xᵢ` (so its Jacobian is `∂ᵢf`). -/
def naivePresentation (i : σ) :
    PreSubmersivePresentation R (MvPolynomial σ R ⧸ Ideal.span {f}) σ Unit :=
  (PreSubmersivePresentation.naive (v := fun _ : Unit => f) (fun _ => i)
    (Function.injective_of_subsingleton _)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq R (by rw [Set.range_const]))

/-- The Jacobian of `naivePresentation f i` is the class of `∂f/∂Xᵢ` in `R[Xᵢ] ⧸ (f)`. -/
theorem naivePresentation_jacobian (i : σ) :
    (naivePresentation f i).jacobian = Ideal.Quotient.mk _ (pderiv i f) := by
  rw [naivePresentation, PreSubmersivePresentation.jacobian_ofAlgEquiv,
    PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  simp only [PreSubmersivePresentation.naive, Presentation.naive_relation_apply]
  rfl

/-- The submersive presentation of `(R[Xᵢ] ⧸ (f))[1/∂ᵢf]` over `R`: the localization away from
`∂ᵢf` composed with `naivePresentation f i`. The Jacobian is `∂ᵢf · ∂ᵢf`, a unit after inverting
`∂ᵢf`. -/
def awayPresentation [Finite σ] (i : σ) :
    SubmersivePresentation R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) (Unit ⊕ σ)
      (Unit ⊕ Unit) where
  __ := (PreSubmersivePresentation.localizationAway _
    (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))).comp (naivePresentation f i)
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      naivePresentation_jacobian, PreSubmersivePresentation.localizationAway_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit _).mul (IsLocalization.Away.algebraMap_isUnit _)

/-- Inverting `∂ᵢf` in `R[Xᵢ] ⧸ (f)` gives a standard smooth `R`-algebra of relative dimension
`#σ − 1`. -/
theorem isStandardSmoothOfRelativeDimension_away [Fintype σ] (i : σ) :
    IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) :=
  (awayPresentation f i).isStandardSmoothOfRelativeDimension (by
    change ((PreSubmersivePresentation.localizationAway _
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))).comp (naivePresentation f i)).dimension = _
    rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    simp [Presentation.dimension])

/-- **Jacobian criterion, one equation, ring form.** If the classes of the partial derivatives
`∂ᵢf` generate the unit ideal of `R[Xᵢ] ⧸ (f)`, then `R → R[Xᵢ] ⧸ (f)` is locally standard smooth of
relative dimension `#σ − 1`. -/
theorem locally [Fintype σ] (h : Ideal.span (Set.range fun i : σ =>
      Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1))
      (algebraMap R (MvPolynomial σ R ⧸ Ideal.span {f})) := by
  refine ⟨_, h, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_away f i

open AlgebraicGeometry CategoryTheory in
/-- **Jacobian criterion, one equation, scheme form.** If the classes of the partial derivatives
`∂ᵢf` generate the unit ideal of `R[Xᵢ] ⧸ (f)`, then `Spec (R[Xᵢ] ⧸ (f)) ⟶ Spec R` is smooth of
relative dimension `#σ − 1`. -/
theorem smoothOfRelativeDimension_spec [Fintype σ] (h : Ideal.span (Set.range fun i : σ =>
      Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)) = ⊤) :
    SmoothOfRelativeDimension (Fintype.card σ - 1)
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial σ R ⧸ Ideal.span {f})))) := by
  have hP : HasRingHomProperty (@SmoothOfRelativeDimension.{u} (Fintype.card σ - 1))
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1))) :=
    inferInstance
  rw [@HasRingHomProperty.Spec_iff _ _ hP]
  exact locally f h

end HodgeLadder.HypersurfaceSmooth
