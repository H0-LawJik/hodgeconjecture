module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyFlasqueModel
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturality
public import HodgeLadder.Cup.CocycleClass

/-!
# Upstream's supported-sections model on the class of a Hom-complex cocycle

Rung `supported-step2-cocycle-class`, part of `supported-sections-class` (front `cup`, supported comparison). Upstream identifies
`relH F n = Ext^n(ℤ[V, W], F)` with the cohomology of the sections over `V` supported outside `U`
of a resolution of `F` (`relHAddEquivSupportedSectionsHomology` for a K-injective one,
`relHAddEquivSupportedSectionsHomologyOfFlasque` for a flasque one). If the image of a class
`x` in `Ext^n(ℤ[V, W], K)` is the class of a Hom-complex cocycle `z`, both send `x` to the
supported-sections class of `z`; the result does not depend on the resolution chosen.

## Main results

* `HodgeLadder.Cup.homComplexPairSheafIsoSupportedSections_naturality`
* `HodgeLadder.Cup.relHSupported_mk`, `HodgeLadder.Cup.relHSupportedOfFlasque_mk`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TopCat.Sheaf

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable (X : TopCat.{0}) (U V W : Opens X) (hW : V ⊓ U = W)

set_option backward.isDefEq.respectTransparency false in
/-- `homComplexPairSheafIsoSupportedSections` is natural in the complex. -/
lemma homComplexPairSheafIsoSupportedSections_naturality
    {K L : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ}
    (f : K ⟶ L) :
    CochainComplex.HomComplex.postcompMap ((CochainComplex.singleFunctor _ 0).obj
        (pairSheaf' X U V W hW)) f ≫
      (homComplexPairSheafIsoSupportedSections X U V W hW L).hom =
    (homComplexPairSheafIsoSupportedSections X U V W hW K).hom ≫
      ((supportEvaluation X V).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h := CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda_naturality
    (pairSheaf' X U V W hW) f
  ext n : 1
  have hn := congrArg (fun g => HomologicalComplex.Hom.f g n) h
  simp only [HomologicalComplex.comp_f] at hn
  simp only [homComplexPairSheafIsoSupportedSections, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [← Category.assoc, hn, Category.assoc, Category.assoc]
  congr 1
  exact (pairSheafHomIsoSupportedSections_naturality X U V W hW (f.f n)).symm

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance supportedHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
/-- **The K-injective supported model on a cocycle class.** -/
lemma relHSupported_mk
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ (inf_le_left : V ⊓ U ≤ V) : W ≤ V)))
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) I n)
    (hx : x.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    relHAddEquivSupportedSectionsHomology X U V W hW F I ι n x =
      HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U V W hW I).hom n
        ((CochainComplex.HomComplex.homologyAddEquiv _ I n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk z)) := by
  unfold relHAddEquivSupportedSectionsHomology
  simp only [AddEquiv.trans_apply]
  have hin : (isoHomCongrAddEquiv (Iso.refl _) ((shiftFunctor _ (n : ℤ)).mapIso
      (asIso (DerivedCategory.Q.map ι)))) (Abelian.Ext.homAddEquiv x) =
      x.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' := by
    simp [isoHomCongrAddEquiv]
  erw [hin, hx]
  rw [← CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk, AddEquiv.apply_symm_apply]
  rfl

local instance supportedTopHasDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The flasque supported model on a cocycle class**, independent of the injective resolution. -/
lemma relHSupportedOfFlasque_mk (F : TopCat.Sheaf AddCommGrpCat X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n)) (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ (inf_le_left : V ⊓ U ≤ V) : W ≤ V)))
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) K n)
    (hx : x.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    relHAddEquivSupportedSectionsHomologyOfFlasque X F K ι U V W hW hK n x =
      HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections X U V W hW K).hom n
        ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk z)) := by
  haveI := injectiveResolutionComplex_isKInjective X F
  haveI := injectiveResolutionAugmentation_quasiIso X F
  have hx0 : x.hom ≫ (DerivedCategory.Q.map (injectiveResolutionAugmentation X F))⟦(n : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (z.postcomp (resolutionToInjective X F K ι)))
        DerivedCategory.Q := by
    rw [← comp_resolutionToInjective X F K ι, Functor.map_comp, Functor.map_comp, ← Category.assoc,
      hx, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp]
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
      Functor.commShiftIso_hom_naturality]
  unfold relHAddEquivSupportedSectionsHomologyOfFlasque
  erw [AddEquiv.trans_apply]
  rw [relHSupported_mk X U V W hW F _ _ n x (z.postcomp (resolutionToInjective X F K ι)) hx0]
  have h4 : (CochainComplex.HomComplex.homologyAddEquiv ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj (pairSheaf' X U V W hW)) _ n).symm
      (CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp (resolutionToInjective X F K ι))) =
      HomologicalComplex.homologyMap (CochainComplex.HomComplex.postcompMap ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj (pairSheaf' X U V W hW)) (resolutionToInjective X F K ι)) n
        ((CochainComplex.HomComplex.homologyAddEquiv ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj (pairSheaf' X U V W hW)) K n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk z)) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj (pairSheaf' X U V W hW)) _ n).injective
    rw [CochainComplex.HomComplex.homologyAddEquiv_postcompMap, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, CochainComplex.HomComplex.postcompClass_mk]
  erw [h4]
  have hΓ := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (homComplexPairSheafIsoSupportedSections_naturality X U V W hW (resolutionToInjective X F K ι))
  simp only [HomologicalComplex.homologyMap_comp] at hΓ
  have hΓy := ConcreteCategory.congr_hom hΓ
    ((CochainComplex.HomComplex.homologyAddEquiv ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).obj (pairSheaf' X U V W hW)) K n).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z))
  simp only [ConcreteCategory.comp_apply] at hΓy
  erw [hΓy]
  haveI := supportedSections_map_resolutionToInjective_quasiIso X F K ι U V hK
  exact ConcreteCategory.congr_hom (IsIso.hom_inv_id (HomologicalComplex.homologyMap
    (((supportEvaluation X V).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (resolutionToInjective X F K ι))) (n : ℤ))) _

end HodgeLadder.Cup
