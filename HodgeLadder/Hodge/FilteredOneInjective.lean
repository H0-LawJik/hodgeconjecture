module

public import HodgeLadder.General.TriangleShiftedHom
public import HodgeLadder.Hodge.FirstFiltration

/-!
# `ℍ¹(F¹Ω^•) → H_dR^1` is injective when `H_dR^0 → ℍ⁰(𝒪[0])` is onto

The triangle of `0 → F¹Ω^• → Ω^• → 𝒪[0] → 0` (`firstFiltrationShortComplex_shortExact`) gives
the exact segment `ℍ⁰(Ω^•) → ℍ⁰(𝒪[0]) → ℍ¹(F¹Ω^•) → ℍ¹(Ω^•)`. If the first map is onto, the
connecting map vanishes, so the last map is injective. Only the vanishing of the connecting map
is used; its sign plays no role.

The hypothesis holds at `Spec ℂ`, where `Ω^•` is `𝒪` in degree zero, and there the conclusion
is degenerate (`HodgeLadder.Tests.deRhamToHolomorphicFunctionCohomology_point_surjective`). On a
compact `X(ℂ)` of positive dimension, sub-rung S2a of `elliptic-curve-holomorphic-form`
(`de-rham-functions-surjective-zero`, open) is to supply it.

## Main results

* the general step is `CategoryTheory.Pretriangulated.Triangle.shifted_coyoneda_injective₁` in
  `HodgeLadder.General.TriangleShiftedHom`.
* `HodgeLadder.filteredToDeRhamCohomology_one_one_injective`
* `HodgeLadder.filteredOneOneEquivHodgeFiltration`,
  `HodgeLadder.filteredOneOneEquivHodgeFiltrationComplexSubmodule`: under the hypothesis,
  `ℍ¹(X; F¹Ω^•) ≃+ F¹ H_dR^1(X)`, given by `filteredToDeRhamCohomology X 1 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  ComplexPoint

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

local instance filteredOneInjectiveHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- In the derived category, a hypercohomology map is postcomposition with the image of the
morphism of complexes. -/
private lemma equiv_hypercohomologyMap' {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (n : ℤ) (β : Hypercohomology X K n) :
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (hypercohomologyMap X f n β) =
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) β).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map f)) (zero_add n) := by
  change (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
    (β.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀]

/-- **S2b.** If `H_dR^0(X) → ℍ⁰(X; 𝒪[0])` is onto, then `ℍ¹(X; F¹Ω^•) → H_dR^1(X)` is
injective: the connecting map `ℍ⁰(𝒪[0]) → ℍ¹(F¹Ω^•)` of the triangle of
`firstFiltrationShortComplex_shortExact` vanishes on the image of `ℍ⁰(Ω^•)`. -/
theorem filteredToDeRhamCohomology_one_one_injective
    (h : Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)) :
    Function.Injective (filteredToDeRhamCohomology X 1 1) := by
  let hS := firstFiltrationShortComplex_shortExact X
  let E := fun (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) =>
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (X := constantIntegerSheafComplexInt X) (Y := K) (m := n))
  rw [injective_iff_map_eq_zero]
  intro β hβ
  apply (E _ 1).injective
  rw [hypercohomologyEquiv_zero]
  refine Triangle.shifted_coyoneda_injective₁ _
    (DerivedCategory.triangleOfSES_distinguished hS) _ 0 1 rfl ?_ (E _ 1 β) ?_
  · intro γ
    obtain ⟨α, hα⟩ := h ((E _ 0).symm γ)
    refine ⟨E _ 0 α, ?_⟩
    change (E _ 0 α).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
      (DerivedCategory.Q.map (holomorphicDeRhamToFunctionsComplexInt X))) (zero_add 0) = γ
    rw [← equiv_hypercohomologyMap']
    change E _ 0 (deRhamToHolomorphicFunctionCohomology X 0 α) = γ
    rw [hα]
    exact (E _ 0).apply_symm_apply γ
  · change (E _ 1 β).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
      (DerivedCategory.Q.map (hodgeFilteredDeRhamInclusion X 1))) (zero_add 1) = 0
    rw [← equiv_hypercohomologyMap']
    change E _ 1 (filteredToDeRhamCohomology X 1 1 β) = 0
    rw [hβ]
    exact hypercohomologyEquiv_zero X _ 1

/-- Under the hypothesis of `filteredToDeRhamCohomology_one_one_injective`,
`filteredToDeRhamCohomology X 1 1` is an additive isomorphism `ℍ¹(X; F¹Ω^•) ≃+ F¹ H_dR^1(X)`
onto its range `hodgeFiltration X 1 1`. -/
def filteredOneOneEquivHodgeFiltration
    (h : Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)) :
    FilteredDeRhamHypercohomology X 1 1 ≃+ hodgeFiltration X 1 1 :=
  AddMonoidHom.ofInjective (filteredToDeRhamCohomology_one_one_injective X h)

/-- The isomorphism `filteredOneOneEquivHodgeFiltration` is `filteredToDeRhamCohomology X 1 1`. -/
@[simp]
theorem filteredOneOneEquivHodgeFiltration_apply
    (h : Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0))
    (β : FilteredDeRhamHypercohomology X 1 1) :
    (filteredOneOneEquivHodgeFiltration X h β : H_dR^1(X)) = filteredToDeRhamCohomology X 1 1 β :=
  rfl

/-- The same isomorphism with target the complex subspace `F^1 H_dR^1(X)`
(`hodgeFiltrationComplexSubmodule X 1 1`), whose carrier is `hodgeFiltration X 1 1`. -/
def filteredOneOneEquivHodgeFiltrationComplexSubmodule
    (h : Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0)) :
    FilteredDeRhamHypercohomology X 1 1 ≃+ F^1 H_dR^1(X) :=
  filteredOneOneEquivHodgeFiltration X h

/-- The isomorphism `filteredOneOneEquivHodgeFiltrationComplexSubmodule` is
`filteredToDeRhamCohomology X 1 1`. -/
@[simp]
theorem filteredOneOneEquivHodgeFiltrationComplexSubmodule_apply
    (h : Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0))
    (β : FilteredDeRhamHypercohomology X 1 1) :
    (filteredOneOneEquivHodgeFiltrationComplexSubmodule X h β : H_dR^1(X)) =
      filteredToDeRhamCohomology X 1 1 β :=
  rfl

end HodgeLadder
