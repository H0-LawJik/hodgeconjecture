module

public import HodgeLadder.Hodge.FilteredOneInjective
public import HodgeLadder.Tests.Witness

/-!
# The hypothesis of `filtered-one-injective` holds at `Spec ℂ`

At the point `Spec ℂ` the holomorphic de Rham complex is `𝒪` in degree zero (`Ω^p = 0` for
`p > dim = 0`), so the projection `Ω^• → 𝒪[0]` is an isomorphism of complexes and
`H_dR^0 → ℍ⁰(𝒪[0])` is onto. This makes `filteredToDeRhamCohomology_one_one_injective` applicable
at the pin; the conclusion there is degenerate, since `F¹Ω^•` is zero at the point.

## Main results

* `HodgeLadder.Tests.smoothOfRelativeDimension_point`, `HodgeLadder.Tests.dim_point`
* `HodgeLadder.Tests.isIso_holomorphicDeRhamToFunctionsComplexInt_point`
* `HodgeLadder.Tests.deRhamToHolomorphicFunctionCohomology_point_surjective`
* `HodgeLadder.Tests.filteredToDeRhamCohomology_point_injective`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

/-- `Spec ℂ → Spec ℂ` is smooth of relative dimension zero. -/
instance smoothOfRelativeDimension_point : SmoothOfRelativeDimension 0 point.hom := by
  dsimp [point]; infer_instance

/-- The point has dimension zero. -/
theorem dim_point : TopologicalSpace.dim point.left = 0 :=
  SmoothOfRelativeDimension.dim_eq (f := point.hom) 0

/-- At the point, the projection `Ω^• → 𝒪[0]` is an isomorphism of complexes. -/
theorem isIso_holomorphicDeRhamToFunctionsComplexInt_point :
    IsIso (holomorphicDeRhamToFunctionsComplexInt point) := by
  have hc : ∀ j, IsIso ((holomorphicDeRhamToFunctionsComplexInt point).f j) := by
    intro j
    by_cases hj : j = 0
    · subst hj; exact isIso_holomorphicDeRhamToFunctionsComplexInt_f_zero point
    · have hs : IsZero ((holomorphicDeRhamComplexInt point).X j) := by
        rcases lt_or_gt_of_ne hj with hneg | hpos
        · exact CochainComplex.isZero_of_isStrictlyGE (holomorphicDeRhamComplexInt point) 0 j
            (by omega)
        · exact holomorphicDeRhamComplexInt_isZero_X_of_lt point j (by
            rw [dim_point]; exact_mod_cast hpos)
      apply isIso_of_source_target_iso_zero
      · exact hs.isoZero
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j hj).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

attribute [local instance] isIso_holomorphicDeRhamToFunctionsComplexInt_point

/-- At the point, `H_dR^0 → ℍ⁰(𝒪[0])` is onto: the hypothesis of
`filteredToDeRhamCohomology_one_one_injective` holds at `Spec ℂ`. -/
theorem deRhamToHolomorphicFunctionCohomology_point_surjective :
    Function.Surjective (deRhamToHolomorphicFunctionCohomology point 0) := by
  intro γ
  refine ⟨hypercohomologyMap point (inv (holomorphicDeRhamToFunctionsComplexInt point)) 0 γ, ?_⟩
  change hypercohomologyMap point (holomorphicDeRhamToFunctionsComplexInt point) 0
    (hypercohomologyMap point (inv (holomorphicDeRhamToFunctionsComplexInt point)) 0 γ) = γ
  rw [← hypercohomologyMap_comp_apply, IsIso.inv_hom_id, hypercohomologyMap_id]
  rfl

/-- `filteredToDeRhamCohomology_one_one_injective` applied at the point. -/
theorem filteredToDeRhamCohomology_point_injective :
    Function.Injective (filteredToDeRhamCohomology point 1 1) :=
  filteredToDeRhamCohomology_one_one_injective point
    deRhamToHolomorphicFunctionCohomology_point_surjective

end HodgeLadder.Tests
