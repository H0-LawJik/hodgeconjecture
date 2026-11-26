module

public import HodgeLadder.Cup.SupportedVariety
public import HodgeLadder.Cup.SupportAbYoneda
public import HodgeLadder.Cup.EndClass
public import HodgeLadder.Cup.SupportedStep2

/-!
# The supported cup product on a cocycle representative

Rung `supported-sections-class` (front `cup`, supported comparison). Let `P` be a sheaf of abelian
groups (for the supported comparison, the pair sheaf `ℤ[X, X ∖ Z]`) and `α ∈ Ext^p(P, ℚ_X)`. If
`α` followed by `ι : ℚ_X → S` (the singular cochain resolution) is the class of a Hom-complex
cocycle `z : P[0] → S` of degree `p`, and `b` is a global cocycle naming `β ∈ H^q(X; ℚ)`, then the
product `α · β` followed by `ι` is the class of `z` composed with right multiplication by `b`.
Through upstream's supported-sections model (`supported-step2-cocycle-class`), this computes
`supCup α β` in supported sections.

## Main results

* `HodgeLadder.Cup.shiftedHom_comp_core`, `HodgeLadder.Cup.supCupY_class`,
  `HodgeLadder.Cup.supCup_supportedSections`
-/

@[expose] public noncomputable section

open CategoryTheory Localization AlgebraicGeometry ComplexPoint TopologicalSpace

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section Core

variable {D : Type*} [Category D] [HasShift D ℤ]

/-- **The algebra of `supported-sections-class`**: if `x` followed by `φ` is `Zx` and `E` followed
by `φ` is `φ` followed by `R`, then `x · E` followed by `φ` is `Zx · R`. -/
lemma shiftedHom_comp_core {A T S : D} {p q n : ℤ} (h : q + p = n)
    (x : ShiftedHom A T p) (E : ShiftedHom T T q) (φ : T ⟶ S) (R : ShiftedHom S S q)
    (Zx : ShiftedHom A S p) (hx : x ≫ φ⟦p⟧' = Zx) (hend : E ≫ φ⟦q⟧' = φ ≫ R) :
    x.comp E h ≫ φ⟦n⟧' = Zx.comp R h := by
  rw [← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl, ← hx, ← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl]
  rw [ShiftedHom.comp_assoc _ _ _ h (zero_add q) (by omega),
    ShiftedHom.comp_assoc _ _ _ (zero_add p) (add_zero q) (by omega)]
  congr 1
  rw [ShiftedHom.comp_mk₀, hend, ← ShiftedHom.mk₀_comp (0 : ℤ) rfl]

end Core

variable (X : Over (Spec ↧ℂ))

local instance clsHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance clsSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  clsHasDerivedCategory X

set_option maxHeartbeats 1000000 in
/-- **The product of a represented class and a named absolute class is represented by the
composite cocycle.** -/
theorem supCupY_class [IsIntegral X.left] [Smooth X.hom]
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    {P : CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat.{0}} {p q : ℕ}
    (α : Abelian.Ext.{0} P (constAb (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)) p)
    (β : H^q(X; ℚ)) (b : AlgebraicTopology.Singular.OpenCochains ℚ
      (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) q)
    (hb : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) q).app (Opposite.op ⊤) b = 0)
    (hβ : rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X ℚ)).hom q
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ q).symm
          (CochainComplex.HomComplex.CohomologyClass.mk
            ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))))))
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj P)
      (singularCochainSheafComplexInt X ℚ) p)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) DerivedCategory.Q)
    (n : ℕ) (h : p + q = n) :
    (supCupY α β n h).hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (cocycleComp z (rightMulCocycle b hb) (by omega))) DerivedCategory.Q := by
  have hend := end_class_right_mult X I i β b hb hβ
  rw [supCupY_eq_comp_forgetEnd, Abelian.Ext.comp_hom]
  have hR : SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (rightMulClass X b hb) = ShiftedHom.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (rightMulCocycle b hb))
        DerivedCategory.Q :=
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk _
  rw [hR] at hend
  refine (shiftedHom_comp_core _ _ _ _ _ _ hα hend).trans ?_
  exact ((congrArg (fun f => ShiftedHom.map f DerivedCategory.Q)
    (equivHomShift_symm_cocycleComp z (rightMulCocycle b hb) (by omega))).trans
      (ShiftedHom.map_comp _ _ _ _)).symm

/-- `ι : ℚ_X[0] → S` is a monomorphism. -/
instance iotaQ_mono : Mono (iotaQ X) := by
  have := rationalToSingularCochainComplexInt_mono X
  dsimp only [iotaQ]
  infer_instance

/-- `ι : ℚ_X[0] → S` is a quasi-isomorphism. -/
instance iotaQ_quasiIso [IsIntegral X.left] [Smooth X.hom] : QuasiIso (iotaQ X) := by
  have := rationalToSingularCochainComplexInt_quasiIso X
  dsimp only [iotaQ]
  infer_instance

set_option maxHeartbeats 1000000 in
/-- **The supported cup product in upstream's supported-sections model**: if `α`, followed by `ι`,
is the class of the cocycle `z` out of the pair sheaf, then `supCup α β` goes to the
supported-sections class of `z` composed with right multiplication by `b`. -/
theorem supCup_supportedSections [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    {Z : Closeds (ComplexPoint X)} {p q : ℕ} (α : H_[Z]^p(X; ℚ))
    (β : H^q(X; ℚ)) (b : AlgebraicTopology.Singular.OpenCochains ℚ
      (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) q)
    (hb : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) q).app (Opposite.op ⊤) b = 0)
    (hβ : rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X ℚ)).hom q
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ q).symm
          (CochainComplex.HomComplex.CohomologyClass.mk
            ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))))))
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
      (singularCochainSheafComplexInt X ℚ) p)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) DerivedCategory.Q)
    (n : ℕ) (h : p + q = n) :
    TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
        𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X) Z.compl ⊤ Z.compl
        (top_inf_eq _) (singularCochainSheafComplexInt_isFlasque X) n (supCup α β n h) =
      HomologicalComplex.homologyMap (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
          (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
          (singularCochainSheafComplexInt X ℚ)).hom n
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ n).symm
          (CochainComplex.HomComplex.CohomologyClass.mk
            (cocycleComp z (rightMulCocycle b hb) (by omega)))) := by
  exact relHSupportedOfFlasque_mk (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) n (supCup α β n h)
    (cocycleComp z (rightMulCocycle b hb) (by omega)) (supCupY_class X I i α β b hb hβ z hα n h)

end HodgeLadder.Cup
