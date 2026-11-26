module

public import HodgeLadder.Cup.ExtBridge
public import HodgeLadder.Cup.ExtRightMult

/-!
# The endomorphism class of `[b]` against right multiplication by `b`

Rung `end-class-right-mult` (front `cup`). For a class `β ∈ H^q(X; ℚ)` that upstream's comparison
sends to the class of a global singular cocycle `b`, the endomorphism class `ε = forgetEnd (e β)`
of `ℚ_X`, followed by the resolution `ι : ℚ_X[0] → S`, equals `ι` followed by right multiplication
`R_b`, in the derived category of sheaves of abelian groups on `X(ℂ)`.

## Main results

* `HodgeLadder.Cup.extendSingleIso_hom_naturality`, `HodgeLadder.Cup.ulift_comp_kappa`,
  `HodgeLadder.Cup.uliftIso_hom_kappa`, `HodgeLadder.Cup.kappa_cancel_derived`,
  `HodgeLadder.Cup.end_class_core`, `HodgeLadder.Cup.end_class_right_mult`
-/

@[expose] public noncomputable section

open CategoryTheory Localization AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder.Cup

section General

variable {C : Type*} [Category C] [Abelian C]

/-- `extendSingleIso` is natural in the object. -/
lemma extendSingleIso_hom_naturality {A B : C} (φ : A ⟶ B) :
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0
      (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)).hom ≫
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map φ =
      HomologicalComplex.extendMap ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map φ)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat B 0 0
          (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)).hom := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ _ (i := 0) (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)]
  simp only [HomologicalComplex.single_map_f_self, Category.assoc]
  simp
  erw [Iso.inv_hom_id_assoc]

end General

section Cancel

variable {Y : TopCat.{0}} [HasDerivedCategory (Sheaf (J Y) AddCommGrpCat.{0})]

/-- **`κ` cancels on shifted homs `ℚ_Y ⟶ ℚ_Y⟦q⟧` in the derived category.** -/
lemma kappa_cancel_derived {q : ℕ}
    (y₁ y₂ : ShiftedHom ((DerivedCategory.singleFunctor (Sheaf (J Y) AddCommGrpCat.{0}) 0).obj
        (constAb Y (AddCommGrpCat.of ℚ)))
      ((DerivedCategory.singleFunctor (Sheaf (J Y) AddCommGrpCat.{0}) 0).obj
        (constAb Y (AddCommGrpCat.of ℚ))) (q : ℤ))
    (h : (DerivedCategory.singleFunctor _ 0).map (kappaSheaf Y) ≫ y₁ =
      (DerivedCategory.singleFunctor _ 0).map (kappaSheaf Y) ≫ y₂) :
    y₁ = y₂ := by
  obtain ⟨x₁, rfl⟩ := Abelian.Ext.homEquiv.surjective y₁
  obtain ⟨x₂, rfl⟩ := Abelian.Ext.homEquiv.surjective y₂
  congr 1
  apply kappa_cancel_rational Y
  apply Abelian.Ext.homEquiv.injective
  change ((Abelian.Ext.mk₀ (kappaSheaf Y)).comp x₁ (zero_add q)).hom =
    ((Abelian.Ext.mk₀ (kappaSheaf Y)).comp x₂ (zero_add q)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.mk₀_comp]
  exact h

end Cancel

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (X : Over (Spec ↧ℂ))

/-- `ℤ_X → ℚ_X` in upstream's `ℤ` and in its `ULift ℤ` agree. -/
lemma ulift_comp_kappa :
    (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
        (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv ≫ kappaSheaf (TopCat.of (ComplexPoint X)) =
      intToRat (TopCat.of (ComplexPoint X)) := by
  rw [kappaSheaf, ← CategoryTheory.Functor.map_comp, intToRat]
  congr 1

/-- **The source comparisons and `κ`**: upstream's `ULift` comparison followed by `κ` is
`intToRatComplex` followed by upstream's comparison for `ℚ`. -/
lemma uliftIso_hom_kappa :
    (constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (kappaSheaf (TopCat.of (ComplexPoint X))) =
      intToRatComplex X ≫ (constantFieldSheafComplexIntIsoSingle ℚ X).hom := by
  rw [constantIntegerSheafComplexIntIsoSingleULift, Iso.trans_hom, Category.assoc,
    Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, Iso.symm_hom, Functor.mapIso_inv, ulift_comp_kappa]
  exact extendSingleIso_hom_naturality _

local instance endHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance endSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  endHasDerivedCategory X

local instance endHasExt : HasExt.{0} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  inferInstance

/-- The resolution `ℚ_X[0] ⟶ S` from the single complex. -/
abbrev iotaQ : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); ℚ) ⟶
    singularCochainSheafComplexInt X ℚ :=
  (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ rationalToSingularCochainComplexInt X

set_option maxHeartbeats 1000000 in
/-- **The algebra of `end-class-right-mult`**, in one spelling of the derived category. -/
lemma end_class_core [IsIntegral X.left] [Smooth X.hom] {q : ℕ}
    (E : DerivedCategory.Q.obj ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℚ)) ⟶
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℚ)))⟦(q : ℤ)⟧)
    (B : DerivedCategory.Q.obj ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constAb (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of (ULift.{0} ℤ)))) ⟶
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℚ)))⟦(q : ℤ)⟧)
    (a : DerivedCategory.Q.obj (constantIntegerSheafComplexInt X) ⟶
      (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X))⟦(q : ℤ)⟧)
    (R : DerivedCategory.Q.obj (singularCochainSheafComplexInt X ℚ) ⟶
      (DerivedCategory.Q.obj (singularCochainSheafComplexInt X ℚ))⟦(q : ℤ)⟧)
    (hb1 : B = inv (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom) ≫ a ≫
      (DerivedCategory.Q.map (constantFieldSheafComplexIntIsoSingle ℚ X).hom)⟦(q : ℤ)⟧')
    (hκ : B = DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ E)
    (h2 : a ≫ (DerivedCategory.Q.map (rationalToSingularCochainComplexInt X))⟦(q : ℤ)⟧' =
      DerivedCategory.Q.map (intToRatComplex X ≫ rationalToSingularCochainComplexInt X) ≫ R)
    (hcancel : ∀ y₁ y₂ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); ℚ)) ⟶
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); ℚ)))⟦(q : ℤ)⟧,
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ y₁ =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ y₂ → y₁ = y₂) :
    E ≫ (DerivedCategory.Q.map (iotaQ X))⟦(q : ℤ)⟧' = DerivedCategory.Q.map (iotaQ X) ≫ R := by
  have : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  have hiso : IsIso (DerivedCategory.Q.map (iotaQ X)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact inferInstanceAs (QuasiIso ((constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫
      rationalToSingularCochainComplexInt X))
  have ha : a = DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ E ≫
      (DerivedCategory.Q.map (constantFieldSheafComplexIntIsoSingle ℚ X).inv)⟦(q : ℤ)⟧' := by
    rw [← Category.assoc (DerivedCategory.Q.map _) E, ← hκ, hb1]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hr : DerivedCategory.Q.map (intToRatComplex X ≫ rationalToSingularCochainComplexInt X) =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ DerivedCategory.Q.map (iotaQ X) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← Category.assoc, uliftIso_hom_kappa, iotaQ,
      Category.assoc, Iso.hom_inv_id_assoc]
  rw [ha, hr] at h2
  simp only [Category.assoc] at h2
  have h3 := (cancel_epi (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom)).mp h2
  have hφ : (DerivedCategory.Q.map (constantFieldSheafComplexIntIsoSingle ℚ X).inv)⟦(q : ℤ)⟧' ≫
      (DerivedCategory.Q.map (rationalToSingularCochainComplexInt X))⟦(q : ℤ)⟧' =
      (DerivedCategory.Q.map (iotaQ X))⟦(q : ℤ)⟧' := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rw [hφ] at h3
  have key := hcancel E ((DerivedCategory.Q.map (iotaQ X) ≫ R) ≫
      (inv (DerivedCategory.Q.map (iotaQ X)))⟦(q : ℤ)⟧') (by
    calc _ = DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
            (kappaSheaf (TopCat.of (ComplexPoint X)))) ≫ E ≫
          (DerivedCategory.Q.map (iotaQ X))⟦(q : ℤ)⟧' ≫
            (inv (DerivedCategory.Q.map (iotaQ X)))⟦(q : ℤ)⟧' := by
          rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
            Category.comp_id]
      _ = _ := by
          rw [← Category.assoc E, ← Category.assoc, h3]
          simp only [Category.assoc])
  rw [key, Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The derived-category class of right multiplication by `b`, in upstream's spelling. -/
abbrev rightMulClass {q : ℕ} (b : AlgebraicTopology.Singular.OpenCochains ℚ
      (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) q)
    (hb : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) q).app (Opposite.op ⊤) b = 0) :
    SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) (singularCochainSheafComplexInt X ℚ)
      (singularCochainSheafComplexInt X ℚ) (q : ℤ) :=
  (CochainComplex.HomComplex.CohomologyClass.mk (rightMulCocycle b hb)).toSmallShiftedHom

set_option maxHeartbeats 1000000 in
/-- **The endomorphism class of `[b]`, followed by `ι`, is `ι` followed by `R_b`.** -/
theorem end_class_right_mult [IsIntegral X.left] [Smooth X.hom]
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    {q : ℕ} (β : H^q(X; ℚ)) (b : AlgebraicTopology.Singular.OpenCochains ℚ
      (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) q)
    (hb : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) q).app (Opposite.op ⊤) b = 0)
    (hβ : rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X ℚ)).hom q
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ q).symm (CochainComplex.HomComplex.CohomologyClass.mk
          ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X))))))) :
    (forgetEnd (TopCat.of (ComplexPoint X)) (rationalExtEquiv (TopCat.of (ComplexPoint X)) q β)).hom ≫
        (DerivedCategory.Q.map (iotaQ X))⟦(q : ℤ)⟧' =
      DerivedCategory.Q.map (iotaQ X) ≫
        SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (rightMulClass X b hb) := by
  have hcoc : ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))).precomp
      (constantIntegerSheafComplexIntIsoSingle X).hom =
      (rightMulCocycle b hb).precomp (intToRatComplex X ≫ rationalToSingularCochainComplexInt X) := by
    have hf := iso_hom_iotaZ X
    ext p r hpr
    have hfp := congrArg (fun f => HomologicalComplex.Hom.f f p) hf
    simp only [HomologicalComplex.comp_f] at hfp
    simp only [CochainComplex.HomComplex.Cocycle.precomp, CochainComplex.HomComplex.Cocycle.mk,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    erw [← Category.assoc, hfp, Category.assoc]
  have hstep1 := (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    X I i q).injective (hβ.trans (globalSectionsOfResolution_mk X I i q
      ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X))))).symm)
  have hstep1' := hstep1.trans ((congrArg
    (fun z => (CochainComplex.HomComplex.CohomologyClass.mk z).toSmallShiftedHom.{1}) hcoc).trans
      (toSmallShiftedHom_precomp (rightMulCocycle b hb)
        (intToRatComplex X ≫ rationalToSingularCochainComplexInt X)))
  have h2 := congrArg (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) hstep1'
  rw [rationalCohomologySingularCochainAddEquiv_apply] at h2
  change SmallShiftedHom.equiv _ _ (((hypercohomologyAddEquivConstantCohomology ℚ X q).symm β).comp
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (rationalToSingularCochainComplexInt X))
      (zero_add _)) = _ at h2
  have hR : SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      ((SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (intToRatComplex X ≫ rationalToSingularCochainComplexInt X)).comp
        (rightMulClass X b hb) (add_zero _)) =
      DerivedCategory.Q.map (intToRatComplex X ≫ rationalToSingularCochainComplexInt X) ≫
        SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (rightMulClass X b hb) := by
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp]
  replace h2 := h2.trans hR
  rw [SmallShiftedHom.equiv_comp] at h2
  simp only [SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    SmallShiftedHom.postcompEquiv_symm_apply, SmallShiftedHom.equiv_comp,
    SmallShiftedHom.equiv_mk₀Inv] at h2
  have hb1 := hyperEquiv_hom_comp X q ((hypercohomologyAddEquivConstantCohomology ℚ X q).symm β)
  rw [AddEquiv.apply_symm_apply, SmallShiftedHom.equiv_mk₀Inv, SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hb1
  have hinv : (Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).inv =
      inv (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom) :=
    (IsIso.inv_eq_of_hom_inv_id (Localization.isoOfHom_hom_inv_id DerivedCategory.Q
      (analyticQuasiIsomorphisms X) _ _)).symm
  rw [hinv] at hb1
  have hβκ : β.hom = (DerivedCategory.singleFunctor _ 0).map (kappaSheaf (TopCat.of (ComplexPoint X))) ≫
      (forgetEnd (TopCat.of (ComplexPoint X)) (rationalExtEquiv (TopCat.of (ComplexPoint X)) q β)).hom := by
    conv_lhs => rw [eq_kappa_comp_forgetEnd (TopCat.of (ComplexPoint X)) β]
    rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  exact end_class_core X _ _ _ _ hb1 hβκ h2
    (fun y₁ y₂ h => kappa_cancel_derived (Y := TopCat.of (ComplexPoint X)) y₁ y₂ h)

end HodgeLadder.Cup
