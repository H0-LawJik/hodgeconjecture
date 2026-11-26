module

public import HodgeLadder.Cup.SupportedOpen

/-!
# The product on an open in supported sections

Rung `supported-open-sections-class` (front `cup`, supported comparison on a general open). For an
open `V` of `X(ℂ)`, a class `α` of the pair `(V, V ⊓ (X ∖ Z))` and `β ∈ H^q(X; ℚ)`, the product
`α ∪ β = supCupY α β` (Yoneda composition with the lift of `β`, as for `V = ⊤`) goes, through
upstream's flasque supported-sections model at `V`, to the supported-sections class of `z`
composed with right multiplication by a global cocycle `b` naming `β`, where `z` is a
Hom-complex cocycle naming `α`. No sign enters at this step. This is `supCup_flasque_chosen` with
`⊤` replaced by `V`; the inputs (`supCupY_class`, `relHSupportedOfFlasque_mk`) are already
general in the pair sheaf.

## Main results

* `HodgeLadder.Cup.supCup_flasque_open`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))
  (V : Opens (ComplexPoint X))

local instance openClsHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance openClsSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  openClsHasDerivedCategory X

set_option maxHeartbeats 2000000 in
/-- **The product on an open, in upstream's supported-sections model at `V`.** -/
lemma supCup_flasque_open {p q : ℕ}
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) p (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) (β : H^q(X; ℚ))
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0)
    (hβ : rationalSingularCochainHypercohomologyAddEquivGlobalSections X q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      namedClass X ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))))
    (z : Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl) rfl))
      (singularCochainSheafComplexInt X ℚ) p)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q)
    (n : ℕ) (h : p + q = n) :
    flasqueModelOpen X Z V n (supCupY α β n h) =
      HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections
          (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl) rfl
          (singularCochainSheafComplexInt X ℚ)).hom n
        ((homologyAddEquiv _ _ n).symm
          (CohomologyClass.mk (cocycleComp z (rightMulCocycle b hb) (by omega)))) := by
  unfold rationalSingularCochainHypercohomologyAddEquivGlobalSections at hβ
  dsimp only at hβ
  let : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
    dsimp [singularCochainSheafComplexInt]
    infer_instance
  obtain ⟨hI, hi, hΓ⟩ : ∃ (_ : (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
        (singularCochainSheafComplexInt X ℚ) 0).choose.IsKInjective)
      (_ : QuasiIso (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
        (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose),
      QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
            (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose) := by
    have := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose
    have := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose_spec
    have := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose
    exact ⟨CochainComplex.isKInjective_of_injective _ 0, inferInstance,
      TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
        _ 0 0 (fun q => singularCochainSheafComplexInt_isFlasque X q) (fun _ => inferInstance)⟩
  exact relHSupportedOfFlasque_mk (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl) rfl
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) n (supCupY α β n h)
    (cocycleComp z (rightMulCocycle b hb) (by omega))
    (supCupY_class X _ _ α β b hb hβ z hα n h)

end Variety

end HodgeLadder.Cup
