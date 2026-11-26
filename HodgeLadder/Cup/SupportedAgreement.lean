module

public import HodgeLadder.Cup.SupportedFinal
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel

/-!
# The flasque supported-sections model against upstream's injective model

Rung `supported-model-agreement` (front `cup`). Upstream identifies `relH F n` with the cohomology
of supported sections both of a K-injective resolution and, through `resolutionToInjective`, of a
flasque one. For any map `g : K → I` from a flasque resolution to a K-injective one under the
augmentations, the injective model is the flasque model followed by `g` on supported sections.
For the singular cochain sheaves and upstream's ambient injective resolution, this identifies the
flasque model used by the supported comparison with upstream's cycle-class transport.

## Main results

* `HodgeLadder.Cup.relHSupported_eq_flasque`, `HodgeLadder.Cup.iotaQ_comp_singularToConstantInjective`,
  `HodgeLadder.Cup.flasqueModel_agreement`, `HodgeLadder.Cup.transport_eq_flasqueModel`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable (Y : TopCat.{0}) (U V W : Opens Y) (hW : V ⊓ U = W)
  [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)]

local instance agrHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance agrTopHasDerivedCategory : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Changing the resolution**: upstream's K-injective supported model is its flasque model
followed by any map of resolutions on supported sections. -/
theorem relHSupported_eq_flasque (F : TopCat.Sheaf AddCommGrpCat Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
    (hK : ∀ n, IsFlasque (K.X n))
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) [I.IsKInjective]
    (ι' : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι']
    (g : K ⟶ I) (hg : ι ≫ g = ι') (n : ℕ)
    (x : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ (inf_le_left : V ⊓ U ≤ V) : W ≤ V))) :
    relHAddEquivSupportedSectionsHomology Y U V W hW F I ι' n x =
      HomologicalComplex.homologyMap (((supportEvaluation Y V).mapHomologicalComplex _).map
        (((sheafSectionsSupportedOutside Y U).mapHomologicalComplex _).map g)) n
        (relHAddEquivSupportedSectionsHomologyOfFlasque Y F K ι U V W hW hK n x) := by
  set eK := homComplexPairSheafIsoSupportedSections Y U V W hW K
  set eI := homComplexPairSheafIsoSupportedSections Y U V W hW I
  obtain ⟨s, hs, hy⟩ := exists_cls _ (n : ℤ) ((n : ℤ) + 1) (by simp)
    (relHAddEquivSupportedSectionsHomologyOfFlasque Y F K ι U V W hW hK n x)
  let z : Cocycle ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' Y U V W hW)) K n :=
    Cocycle.mk (eK.inv.f n s) ((n : ℤ) + 1) rfl (map_d_eq_zero eK.inv s hs)
  have hes : eK.hom.f (n : ℤ) z.1 = s := by
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ)) eK.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s
  set xz : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ (inf_le_left : V ⊓ U ≤ V) : W ≤ V)) :=
    Abelian.Ext.homAddEquiv.symm (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q ≫
      inv ((DerivedCategory.Q.map ι)⟦(n : ℤ)⟧'))
  have hxz : xz.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
    rw [← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  have hF := relHSupportedOfFlasque_mk Y U V W hW F K ι hK n xz z hxz
  have hcls : HomologicalComplex.homologyMap eK.hom n
      ((homologyAddEquiv _ _ n).symm (CohomologyClass.mk z)) =
      cls _ (n : ℤ) ((n : ℤ) + 1) (by simp) s hs := by
    rw [← homologyAddEquiv_cls z, AddEquiv.symm_apply_apply, homologyMap_cls]
    exact cls_eq _ _ _ _ hes
  have hαx : x = xz := (relHAddEquivSupportedSectionsHomologyOfFlasque Y F K ι U V W hW hK n).injective
    (hy.trans (hF.trans hcls).symm)
  have hx' : x.hom ≫ (DerivedCategory.Q.map ι')⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm (z.postcomp g)) DerivedCategory.Q := by
    rw [← hg, Functor.map_comp, Functor.map_comp, ← Category.assoc, hαx, hxz,
      Cocycle.equivHomShift_symm_postcomp]
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
      Functor.commShiftIso_hom_naturality]
  rw [relHSupported_mk Y U V W hW F I ι' n x (z.postcomp g) hx', hy, homologyMap_cls,
    ← homologyAddEquiv_cls (z.postcomp g), AddEquiv.symm_apply_apply, homologyMap_cls]
  apply cls_eq
  have hn := congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ))
    (homComplexPairSheafIsoSupportedSections_naturality Y U V W hW g)
  simp only [HomologicalComplex.comp_f] at hn
  rw [← hes]
  have hz := ConcreteCategory.congr_hom hn z.1
  simp only [ConcreteCategory.comp_apply] at hz
  have hp : (postcompMap ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' Y U V W hW)) g).f
      (n : ℤ) z.1 = (z.postcomp g).1 := rfl
  rw [hp] at hz
  exact hz

section Variety

open AlgebraicGeometry ComplexPoint AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))

set_option backward.isDefEq.respectTransparency false in
/-- The singular augmentation followed by upstream's comparison to the ambient injective
resolution is the ambient augmentation. -/
lemma iotaQ_comp_singularToConstantInjective :
    iotaQ X ≫ singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
      (exists_contractibleOpen_le X) = ambientRationalInjectiveSingleAugmentation X := by
  change (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat ≫ HomologicalComplex.extendMap
      (singularToConstantInjectiveResolution (TopCat.of (ComplexPoint X))
        (exists_contractibleOpen_le X)) ComplexShape.embeddingUpNat = _
  rw [← HomologicalComplex.extendMap_comp, constants_comp_singularToConstantInjectiveResolution]
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The flasque model agrees with upstream's injective model** through upstream's comparison
of supported singular and supported injective sections. -/
theorem flasqueModel_agreement (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    (complexSupportedSingularInjectiveHomologyIso X Z.compl ⊤ (n : ℤ)).hom (flasqueModel X Z n α) =
      rationalSupportAddEquivSupportedInjectiveHomology X Z n α := by
  haveI := rationalToSingularCochainComplexInt_mono X
  exact (relHSupported_eq_flasque (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveSingleAugmentation X)
    (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X))
    (iotaQ_comp_singularToConstantInjective X) n α).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's cycle-class transport factors through the flasque model**: upstream's
`complexSupportInjectiveSectionCohomologyEquiv` after its injective model is upstream's
`supportedRationalSingularSectionCohomologyEquivSupportComplement` after the flasque model. -/
theorem transport_eq_flasqueModel (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology X Z n α) =
      supportedRationalSingularSectionCohomologyEquivSupportComplement (TopCat.of (ComplexPoint X))
        Z Z.isClosed ⊤ n (flasqueModel X Z n α) := by
  rw [← flasqueModel_agreement X Z n α]
  unfold complexSupportInjectiveSectionCohomologyEquiv
  rw [AddEquiv.trans_apply]
  congr 1
  exact Iso.hom_inv_id_apply (complexSupportedSingularInjectiveHomologyIso X Z.compl ⊤ (n : ℤ)) _

end Variety

end HodgeLadder.Cup
