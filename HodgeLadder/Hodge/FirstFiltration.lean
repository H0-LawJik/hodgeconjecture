module

public import HodgeLadder.Hodge.ZeroForms
public import LefschetzPort.AlgebraicGeometry.HolomorphicHodgeProjection
public import LefschetzPort.Supplement.AnalyticExt
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# The first Hodge filtration is the kernel of the projection to `𝒪`

The stupid truncation gives a short exact sequence of complexes `0 → F¹Ω^• → Ω^• → 𝒪[0] → 0`:
in degree zero it is `0 → Ω⁰ ≅ 𝒪`, in degrees `≥ 1` it is `Ωⁱ ≅ Ωⁱ → 0`. Its triangle in the
derived category gives the long exact hypercohomology sequence, and exactness at `ℍ^n(Ω^•)` says
that a de Rham class lies in `F¹` exactly when its image in `ℍ^n(𝒪[0])` vanishes. One inclusion
is in the stack (`deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem`); this file proves the
other.

## Main results

* `HodgeLadder.firstFiltrationShortComplex_shortExact`
* `HodgeLadder.mem_hodgeFiltration_one_iff`: `α ∈ F¹ H_dR^n ↔ α ↦ 0 ∈ ℍ^n(𝒪[0])`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  ComplexPoint

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the second object of a distinguished triangle in an arbitrary shifted degree. -/
lemma shifted_coyoneda_exact₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (I : C) (n : ℤ) (α : ShiftedHom I T.obj₂ n)
    (hα : α.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂) (zero_add n) = 0) :
    ∃ β : ShiftedHom I T.obj₁ n, β.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁) (zero_add n) = α := by
  let F := preadditiveCoyoneda.obj (Opposite.op I)
  have hexact := F.homologySequence_exact₂ T hT n
  rw [ShortComplex.ab_exact_iff] at hexact
  have hkernel : ((F.shift n).map T.mor₂) α = 0 := by
    change α ≫ T.mor₂⟦n⟧' = 0
    simpa only [ShiftedHom.comp_mk₀] using hα
  obtain ⟨β, hβ⟩ := hexact α hkernel
  refine ⟨β, ?_⟩
  change β ≫ T.mor₁⟦n⟧' = α at hβ
  simpa only [ShiftedHom.comp_mk₀] using hβ

end CategoryTheory.Pretriangulated.Triangle

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The short complex `F¹Ω^• → Ω^• → 𝒪[0]`. -/
def firstFiltrationShortComplex : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  ShortComplex.mk (hodgeFilteredDeRhamInclusion X 1) (holomorphicDeRhamToFunctionsComplexInt X)
    (hodgeFilteredDeRhamInclusion_one_comp_toFunctions X)

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the projection `Ω^• → 𝒪[0]` is an isomorphism. -/
theorem isIso_holomorphicDeRhamToFunctionsComplexInt_f_zero :
    IsIso ((holomorphicDeRhamToFunctionsComplexInt X).f 0) := by
  have h0 : (ComplexShape.embeddingUpNat).f 0 = (0 : ℤ) := rfl
  unfold holomorphicDeRhamToFunctionsComplexInt
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ h0]
  have hφ : (holomorphicDeRhamToFunctions X (TopologicalSpace.dim X.left)).f 0 =
      holomorphicZeroFormToFunctionSheaf X (TopologicalSpace.dim X.left) := by
    simp [holomorphicDeRhamToFunctions]
  rw [hφ]
  have := isIso_holomorphicZeroFormToFunctionSheaf X (TopologicalSpace.dim X.left)
  infer_instance

/-- A short complex with zero first object and invertible second map is short exact. -/
private lemma shortExact_of_isZero_X₁ {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h₁ : IsZero S.X₁) (hg : IsIso S.g) : S.ShortExact :=
  { exact := (S.exact_iff_mono (h₁.eq_of_src _ _)).2 inferInstance
    mono_f := ⟨fun u v _ => h₁.eq_of_tgt u v⟩
    epi_g := inferInstance }

/-- A short complex with zero third object and invertible first map is short exact. -/
private lemma shortExact_of_isZero_X₃ {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h₃ : IsZero S.X₃) (hf : IsIso S.f) : S.ShortExact :=
  { exact := (S.exact_iff_epi (h₃.eq_of_tgt _ _)).2 inferInstance
    mono_f := inferInstance
    epi_g := ⟨fun u v _ => h₃.eq_of_src u v⟩ }

set_option backward.isDefEq.respectTransparency false in
/-- `0 → F¹Ω^• → Ω^• → 𝒪[0] → 0` is short exact. -/
theorem firstFiltrationShortComplex_shortExact : (firstFiltrationShortComplex X).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : j = 0
  · subst hj
    refine shortExact_of_isZero_X₁ _ ?_ (isIso_holomorphicDeRhamToFunctionsComplexInt_f_zero X)
    exact HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun n => by
      change 1 + (n : ℤ) ≠ 0
      omega)
  · refine shortExact_of_isZero_X₃ _ (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j hj) ?_
    by_cases hpos : 1 ≤ j
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntGE 1).f n = j :=
        ⟨(j - 1).toNat, by change 1 + ((j - 1).toNat : ℤ) = j; omega⟩
      change IsIso ((hodgeFilteredDeRhamInclusion X 1).f j)
      unfold hodgeFilteredDeRhamInclusion
      rw [HomologicalComplex.stupidTruncInclusion_f _ _ hn]
      infer_instance
    · refine ⟨⟨0, ?_, ?_⟩⟩
      · exact (HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun n => by
          change 1 + (n : ℤ) ≠ j
          omega)).eq_of_src _ _
      · apply IsZero.eq_of_src
        change IsZero ((holomorphicDeRhamComplexInt X).X j)
        exact HomologicalComplex.isZero_extend_X _ _ _ (fun n => by
          change (n : ℤ) ≠ j
          omega)

local instance firstFiltrationHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- In the derived category, a hypercohomology map is postcomposition with the image of the
morphism of complexes. -/
private lemma equiv_hypercohomologyMap {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (n : ℤ) (β : Hypercohomology X K n) :
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (hypercohomologyMap X f n β) =
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) β).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map f)) (zero_add n) := by
  change (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
    (β.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀]

/-- A de Rham class whose image in `ℍ^n(𝒪[0])` vanishes lies in the first Hodge filtration. -/
theorem mem_hodgeFiltration_one_of_toHolomorphicFunction_eq_zero (n : ℤ)
    (α : DeRhamHypercohomology X n)
    (hα : deRhamToHolomorphicFunctionCohomology X n α = 0) :
    α ∈ hodgeFiltration X 1 n := by
  let hS := firstFiltrationShortComplex_shortExact X
  let E := fun (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) =>
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (X := constantIntegerSheafComplexInt X) (Y := K) (m := n))
  have hα' : (E _ α).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.triangleOfSES hS).mor₂)
      (zero_add n) = 0 := by
    change (E _ α).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
      (DerivedCategory.Q.map (holomorphicDeRhamToFunctionsComplexInt X))) (zero_add n) = 0
    rw [← equiv_hypercohomologyMap]
    change E _ (deRhamToHolomorphicFunctionCohomology X n α) = 0
    rw [hα]
    exact hypercohomologyEquiv_zero X _ n
  obtain ⟨b, hb⟩ := Triangle.shifted_coyoneda_exact₂ _
    (DerivedCategory.triangleOfSES_distinguished hS) _ n (E _ α) hα'
  refine ⟨(E _).symm b, ?_⟩
  apply (E _).injective
  change E _ (hypercohomologyMap X (hodgeFilteredDeRhamInclusion X 1) n ((E _).symm b)) = E _ α
  rw [equiv_hypercohomologyMap]
  erw [(E _).apply_symm_apply b]
  exact hb

/-- **`F¹` is the kernel of the projection to `𝒪`**: a de Rham class lies in the first Hodge
filtration exactly when its image in `ℍ^n(𝒪[0])` vanishes. -/
theorem mem_hodgeFiltration_one_iff (n : ℤ) (α : DeRhamHypercohomology X n) :
    α ∈ hodgeFiltration X 1 n ↔ deRhamToHolomorphicFunctionCohomology X n α = 0 :=
  ⟨deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem X n α,
    mem_hodgeFiltration_one_of_toHolomorphicFunction_eq_zero X n α⟩

end HodgeLadder
