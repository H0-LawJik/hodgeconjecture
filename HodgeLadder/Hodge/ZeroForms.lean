module

public import LefschetzPort.AlgebraicGeometry.HolomorphicZeroForms

/-!
# Holomorphic zero-forms are holomorphic functions

Upstream defines holomorphic `p`-forms as Kähler forms of the ring of holomorphic functions,
modulo forms that vanish in every chart, and sheafifies. The stack defines evaluation of
zero-forms, `holomorphicZeroFormToFunctionSheaf : Ω⁰ ⟶ 𝒪`. This file proves it is an
isomorphism: on each open, a Kähler zero-form is its coefficient function, so evaluation is
bijective before sheafification, and the presheaf of zero-forms is already a sheaf.

## Main results

* `HodgeLadder.holomorphicZeroFormToFunction_bijective`
* `HodgeLadder.isIso_holomorphicZeroFormToFunctionSheaf`
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- On each open, evaluation of holomorphic zero-forms is bijective. -/
theorem holomorphicZeroFormToFunction_bijective (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Function.Bijective (holomorphicZeroFormToFunction X d U) := by
  have hinj : LinearMap.ker (algebraicZeroFormToFunction X d U) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective
      (exteriorPower.zeroEquiv (OpenHolomorphicFunctions X d U)
        Ω[OpenHolomorphicFunctions X d U⁄ℂ]).injective
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [hinj]; exact bot_le)
  · rw [← LinearMap.range_eq_top]
    unfold holomorphicZeroFormToFunction
    rw [Submodule.range_liftQ, LinearMap.range_eq_top]
    exact (exteriorPower.zeroEquiv (OpenHolomorphicFunctions X d U)
      Ω[OpenHolomorphicFunctions X d U⁄ℂ]).surjective

/-- Before sheafification, evaluation of zero-forms is an isomorphism of presheaves. -/
theorem isIso_holomorphicZeroFormToFunctionPresheaf :
    IsIso (holomorphicZeroFormToFunctionPresheaf X d) := by
  have (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
      IsIso ((holomorphicZeroFormToFunctionPresheaf X d).app U) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (holomorphicZeroFormToFunction_bijective X d U)
  exact NatIso.isIso_of_isIso_app _

/-- The presheaf of holomorphic zero-forms is a sheaf. -/
theorem isSheaf_holomorphicDeRhamPresheaf_zero :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 0) :=
  (Presheaf.isSheaf_of_iso_iff (@asIso _ _ _ _ (holomorphicZeroFormToFunctionPresheaf X d)
    (isIso_holomorphicZeroFormToFunctionPresheaf X d))).2
    (holomorphicAdditiveSheaf X d).property

/-- **Holomorphic zero-forms are holomorphic functions**: evaluation `Ω⁰ ⟶ 𝒪` is an isomorphism
of sheaves. -/
instance isIso_holomorphicZeroFormToFunctionSheaf :
    IsIso (holomorphicZeroFormToFunctionSheaf X d) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  have h1 := isIso_toSheafify J (isSheaf_holomorphicDeRhamPresheaf_zero X d)
  have hcomp : toSheafify J (holomorphicDeRhamPresheaf X d 0) ≫
      (sheafToPresheaf J AddCommGrpCat).map (holomorphicZeroFormToFunctionSheaf X d) =
        holomorphicZeroFormToFunctionPresheaf X d :=
    toSheafify_sheafifyLift J _ _
  have h2 : IsIso (toSheafify J (holomorphicDeRhamPresheaf X d 0) ≫
      (sheafToPresheaf J AddCommGrpCat).map (holomorphicZeroFormToFunctionSheaf X d)) := by
    rw [hcomp]; exact isIso_holomorphicZeroFormToFunctionPresheaf X d
  have : IsIso ((sheafToPresheaf J AddCommGrpCat).map (holomorphicZeroFormToFunctionSheaf X d)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h2
  exact (fullyFaithfulSheafToPresheaf J AddCommGrpCat).isIso_of_isIso_map _

end HodgeLadder
