module

public import HodgeLadder.Cup.CocycleClass
public import Other.AlgebraicGeometry.Cohomology.GlobalSections
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturality

/-!
# Upstream's step 2 on the class of a Hom-complex cocycle

Part of rung `ext-class-right-mult` (front `cup`). Upstream's comparison of the hypercohomology of
the singular cochain sheaf complex `S` with the cohomology of its global sections
(`rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution`) passes through a
K-injective resolution `S ⟶ I`. On the class of a Hom-complex cocycle `z : ℤ[0] → S` of degree
`n` it does not depend on the resolution: it is the homology class of the global section that
`z` names, through `homComplexSingleIntegerIsoGlobalSections`.

## Main results

* `HodgeLadder.Cup.globalSectionsOfResolution_mk`
-/

@[expose] public noncomputable section

open CategoryTheory Localization CochainComplex HomComplex AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ))

set_option maxHeartbeats 800000 in
/-- **Step 2 on a cocycle class**: the class of `z`, pulled back to upstream's integer constant
complex, goes to the homology class of the global section named by `z`. -/
theorem globalSectionsOfResolution_mk
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    (n : ℤ)
    (z : Cocycle (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
      (singularCochainSheafComplexInt X ℚ) n) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i n
        (CohomologyClass.mk (z.precomp (constantIntegerSheafComplexIntIsoSingle X).hom)).toSmallShiftedHom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X ℚ)).hom n
        ((homologyAddEquiv _ _ n).symm (CohomologyClass.mk z)) := by
  dsimp only [rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution,
    AddEquiv.trans_apply]
  set e := constantIntegerSheafComplexIntIsoSingle X
  have hw : ((z.precomp e.hom).postcomp i).precomp e.inv = z.postcomp i := by
    ext p q hpq
    simp [Cocycle.precomp, Cocycle.postcomp]
  have h4 : (homologyAddEquiv _ I n).symm (CohomologyClass.mk (z.postcomp i)) =
      HomologicalComplex.homologyMap (postcompMap _ i) n
        ((homologyAddEquiv _ (singularCochainSheafComplexInt X ℚ) n).symm (CohomologyClass.mk z)) := by
    apply (homologyAddEquiv _ I n).injective
    rw [homologyAddEquiv_postcompMap, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      postcompClass_mk]
  have hΓ := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections_naturality
      (TopCat.of (ComplexPoint X)) i)
  simp only [HomologicalComplex.homologyMap_comp] at hΓ
  have hΓy := ConcreteCategory.congr_hom hΓ
    ((homologyAddEquiv _ (singularCochainSheafComplexInt X ℚ) n).symm (CohomologyClass.mk z))
  simp only [ConcreteCategory.comp_apply] at hΓy
  have h12 : SmallShiftedHom.precompEquiv e.inv
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      (SmallShiftedHom.postcompEquiv i ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
        (CohomologyClass.mk (z.precomp e.hom)).toSmallShiftedHom) =
      CohomologyClass.equivOfIsKInjective (CohomologyClass.mk (z.postcomp i)) := by
    change _ = (CohomologyClass.mk (z.postcomp i)).toSmallShiftedHom
    rw [← hw, toSmallShiftedHom_precomp ((z.precomp e.hom).postcomp i) e.inv,
      toSmallShiftedHom_postcomp (z.precomp e.hom) i]
    rfl
  simp only [AddEquiv.coe_mk, AddEquiv.symm_mk]
  erw [h12]
  rw [Equiv.symm_apply_apply, h4]
  erw [AddEquiv.trans_apply]
  set H := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i) n with hH
  set y := (homologyAddEquiv _ (singularCochainSheafComplexInt X ℚ) n).symm (CohomologyClass.mk z)
  show ConcreteCategory.hom (asIso H).inv (ConcreteCategory.hom (HomologicalComplex.homologyMap
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X)) I).hom n)
      (ConcreteCategory.hom (HomologicalComplex.homologyMap (postcompMap _ i) n) y)) = _
  rw [hΓy]
  erw [HomologicalComplex.homologyMap_comp]
  rw [ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (IsIso.hom_inv_id H) _

end HodgeLadder.Cup
