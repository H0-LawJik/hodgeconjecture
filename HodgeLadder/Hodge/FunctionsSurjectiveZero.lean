module

public import HodgeLadder.Hodge.CompactHolomorphic
public import HodgeLadder.Hodge.FilteredOneInjective
public import HodgeLadder.General.LocallyConstantSheaf
public import LefschetzPort.AlgebraicGeometry.HolomorphicHodgeProjection
public import LefschetzPort.AlgebraicGeometry.AnalyticSheafCohomologyExt
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry ComplexPoint Opposite
open scoped ContDiff Manifold

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

theorem exists_comp_eq_of_surjective_app_top {F G : AnalyticAdditiveSheaf X} (c : F ⟶ G)
    (hc : Function.Surjective (c.hom.app (op ⊤)))
    (φ : 𝓒(↧(ComplexPoint X); ℤ) ⟶ G) : ∃ ψ : 𝓒(↧(ComplexPoint X); ℤ) ⟶ F, ψ ≫ c = φ := by
  let _ : AddCommGroup ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj
      (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint X))).homGroup _ _
  let _ : AddCommGroup ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj
      (AddCommGrpCat.of ℤ) ⟶ G) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint X))).homGroup _ _
  obtain ⟨t, ht⟩ := hc (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections G φ)
  refine ⟨(TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).symm t, ?_⟩
  apply (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections G).injective
  refine (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality c _).trans ?_
  rw [AddEquiv.apply_symm_apply]
  exact ht

theorem hypercohomologyMap_analyticSheafComplexIntMap_zero_surjective
    {F G : AnalyticAdditiveSheaf X} (c : F ⟶ G)
    (hc : Function.Surjective (c.hom.app (op ⊤))) :
    Function.Surjective (hypercohomologyMap X (analyticSheafComplexIntMap X c) 0) := by
  intro γ
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_surjective_app_top X c hc
    (Abelian.Ext.homEquiv₀ (analyticSheafCohomologyEquivExt X G 0 γ))
  refine ⟨(analyticSheafCohomologyEquivExt X F 0).symm (Abelian.Ext.mk₀ ψ), ?_⟩
  apply (analyticSheafCohomologyEquivExt X G 0).injective
  refine (analyticSheafCohomologyEquivExt_naturality X c 0 _).trans ?_
  rw [Equiv.apply_symm_apply, Abelian.Ext.mk₀_comp_mk₀, hψ, Abelian.Ext.mk₀_homEquiv₀_apply]

theorem constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToHolomorphicDeRhamComplexInt X ≫ holomorphicDeRhamToFunctionsComplexInt X =
      analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left)) ≫
        (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom := by
  have h := congrArg (fun f ↦ HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (constantsToHolomorphicDeRhamComplex_comp_toFunctions X (dim X.left))
  simp only [HomologicalComplex.extendMap_comp] at h
  exact (reassoc_of% h) (analyticSheafComplexIntIsoSingle X _).hom


variable (d : ℕ)

noncomputable def locallyConstantToHolomorphicSheaf [SmoothOfRelativeDimension d X.hom] :
    HodgeLadder.locallyConstantSheaf (TopCat.of (ComplexPoint X)) ℂ ⟶
      holomorphicAdditiveSheaf X d :=
  ⟨{ app U := AddCommGrpCat.ofHom
      { toFun f := show C^ω⟮𝓘(ℂ, Fin d → ℂ), U.unop; ℂ⟯ from
          ⟨(f : LocallyConstant U.unop ℂ), fun x ↦
            (contMDiffAt_const (c := (f : LocallyConstant U.unop ℂ) x)).congr_of_eventuallyEq
              ((f : LocallyConstant U.unop ℂ).isLocallyConstant.eventually_eq x)⟩
        map_zero' := rfl
        map_add' _ _ := rfl }
     naturality _ _ _ := rfl }⟩

set_option backward.isDefEq.respectTransparency false in
theorem complexConstantsToHolomorphicSheaf_eq [SmoothOfRelativeDimension d X.hom] :
    complexConstantsToHolomorphicSheaf X d =
      (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
        locallyConstantToHolomorphicSheaf X d := by
  apply Sheaf.hom_ext
  apply (sheafifyLift_unique _ _ _ _ _).symm
  rw [HodgeLadder.constantSheafIsoLocallyConstantSheaf_hom]
  change toSheafify _ _ ≫ (HodgeLadder.constantSheafToLocallyConstantSheaf _ ℂ).hom ≫
    (locallyConstantToHolomorphicSheaf X d).hom = _
  erw [← Category.assoc, HodgeLadder.toSheafify_constantSheafToLocallyConstantSheaf_hom]
  rfl

theorem complexConstantsToHolomorphicSheaf_app_top_surjective [SmoothOfRelativeDimension d X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Surjective ((complexConstantsToHolomorphicSheaf X d).hom.app (op ⊤)) := by
  intro s
  refine ⟨(HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv.hom.app (op ⊤)
    (HodgeLadder.holomorphicTopToLocallyConstant X d s), ?_⟩
  rw [complexConstantsToHolomorphicSheaf_eq]
  change ((HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
    (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
      locallyConstantToHolomorphicSheaf X d).hom.app (op ⊤) _ = s
  rw [show (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).inv ≫
    (HodgeLadder.constantSheafIsoLocallyConstantSheaf _ ℂ).hom ≫
      locallyConstantToHolomorphicSheaf X d = locallyConstantToHolomorphicSheaf X d from
        Iso.inv_hom_id_assoc _ _]
  rfl

theorem deRhamToHolomorphicFunctionCohomology_zero_surjective [IsIntegral X.left] [Smooth X.hom]
    [CompactSpace (ComplexPoint X)] :
    Function.Surjective (deRhamToHolomorphicFunctionCohomology X 0) := by
  intro γ
  let e := analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))
  obtain ⟨β, hβ⟩ := hypercohomologyMap_analyticSheafComplexIntMap_zero_surjective X _
    (complexConstantsToHolomorphicSheaf_app_top_surjective X (dim X.left))
    (hypercohomologyMap X e.inv 0 γ)
  refine ⟨hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) 0 β, ?_⟩
  change hypercohomologyMap X (holomorphicDeRhamToFunctionsComplexInt X) 0
    (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) 0 β) = γ
  rw [← hypercohomologyMap_comp_apply,
    constantsToHolomorphicDeRhamComplexInt_comp_toFunctionsComplexInt]
  refine (hypercohomologyMap_comp_apply X
    (analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left))) e.hom 0
      β).trans ?_
  rw [hβ]
  refine (hypercohomologyMap_comp_apply X e.inv e.hom 0 γ).symm.trans ?_
  rw [e.inv_hom_id, hypercohomologyMap_id]
  rfl

theorem filteredToDeRhamCohomology_one_one_injective_of_compact [IsIntegral X.left]
    [Smooth X.hom] [CompactSpace (ComplexPoint X)] :
    Function.Injective (filteredToDeRhamCohomology X 1 1) :=
  filteredToDeRhamCohomology_one_one_injective X
    (deRhamToHolomorphicFunctionCohomology_zero_surjective X)

end HodgeLadder
