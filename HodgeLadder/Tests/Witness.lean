module

public import HodgeConjecture.Statement

/-!
# A variety satisfying the hypotheses of the statement

The upstream statements quantify over `X : Over (Spec ↧ℂ)` with `[IsIntegral X.left]`,
`[Smooth X.hom]` and `[IsProjective X.hom]`. This file exhibits one: `Spec ℂ` over itself. It
rules out the reading in which the hypotheses can never hold, so that the statements would be
vacuous.

## Main results

* `HodgeLadder.Tests.point`: `Spec ℂ` as an object of `Over (Spec ↧ℂ)`.
* `HodgeLadder.Tests.exists_smooth_projective_integral`: some `X` satisfies all three hypotheses.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HodgeLadder.Tests

/-- `Spec ℂ` over itself. -/
noncomputable abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))

instance : IsIntegral (point.left) := by dsimp [point]; infer_instance

instance : Smooth (point.hom) := by dsimp [point]; infer_instance

/-- The grading on `ℤ[x₀]` (one homogeneous coordinate) used by upstream's `ℙ(Fin 1; -)`. -/
noncomputable abbrev grading : ℕ → Submodule (ULift.{0} ℤ) (MvPolynomial (Fin 1) (ULift.{0} ℤ)) :=
  homogeneousSubmodule (Fin 1) (ULift.{0} ℤ)

lemma X_mem : (X 0 : MvPolynomial (Fin 1) (ULift.{0} ℤ)) ∈ grading 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _)

/-- Evaluation of `ℤ[x₀]` at `x₀ = 1`, with values in `ℂ`. -/
noncomputable def evalOne : MvPolynomial (Fin 1) (ULift.{0} ℤ) →+* ℂ :=
  eval₂Hom ((Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom) fun _ => 1

/-- The degree-zero part of `ℤ[x₀]` localized at `x₀`, mapped to `ℂ` by `x₀ ↦ 1`. -/
noncomputable def chartPoint : HomogeneousLocalization.Away grading (X 0) →+* ℂ :=
  (IsLocalization.Away.lift (S := Localization.Away (X 0 : MvPolynomial (Fin 1) (ULift.{0} ℤ)))
      (X 0 : MvPolynomial (Fin 1) (ULift.{0} ℤ))
      (show IsUnit (evalOne (X 0)) by simp [evalOne])).comp
    (algebraMap (HomogeneousLocalization.Away grading (X 0))
      (Localization.Away (X 0 : MvPolynomial (Fin 1) (ULift.{0} ℤ))))

/-- A `ℂ`-point of `Proj ℤ[x₀]`, through the chart where `x₀` is invertible. -/
noncomputable def projPoint : Spec ↧ℂ ⟶ Proj grading :=
  Spec.map (CommRingCat.ofHom chartPoint) ≫ Proj.awayι grading (X 0) X_mem (by norm_num)

/-- The corresponding section of `ℙ(Fin 1; Spec ℂ) → Spec ℂ`. -/
noncomputable def section₀ : Spec ↧ℂ ⟶ ℙ(Fin (0 + 1); Spec ↧ℂ) :=
  pullback.lift (𝟙 _) projPoint (terminal.hom_ext _ _)

lemma section₀_toBase : section₀ ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ) = 𝟙 _ :=
  pullback.lift_fst _ _ _

instance : IsClosedImmersion section₀ := by
  have : IsClosedImmersion (section₀ ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ)) := by
    rw [section₀_toBase]; infer_instance
  exact IsClosedImmersion.of_comp section₀ (toBase (Fin (0 + 1)) (Spec ↧ℂ))

instance : IsProjective (point.hom) :=
  ⟨⟨{ ambientDimension := 0
      immersion := section₀
      immersion_toBase := section₀_toBase }⟩⟩

/-- The hypotheses of the upstream statements can be met: `Spec ℂ` over itself is integral,
smooth and projective in upstream's sense. -/
theorem exists_smooth_projective_integral :
    ∃ X : Over (Spec ↧ℂ), IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom :=
  ⟨point, inferInstance, inferInstance, inferInstance⟩

end HodgeLadder.Tests
