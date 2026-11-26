module

public import HodgeLadder.Cup.OneIsKappa
public import HodgeLadder.Cup.IotaUpstream

/-!
# Mathlib's `Ext` and upstream's hypercohomology in the derived category

Rung `ext-derived-bridge` (front `cup`, part of `end-class-right-mult`). Upstream identifies
`H^n(X; ℚ) = Ext^n(ℤ_X, ℚ_X)` with the hypercohomology of the integer-indexed constant complex
`ℚ_X[0]` (`hypercohomologyAddEquivConstantCohomology`), through the isomorphisms of extended and
single complexes. In the derived category of sheaves of abelian groups, the `Ext` class is the
hypercohomology class conjugated by these isomorphisms. This is upstream's private lemma
`hypercohomologyAddEquivConstantCohomology_hom`, restated publicly.

## Main results

* `HodgeLadder.Cup.hyperEquiv_hom`, `HodgeLadder.Cup.hyperEquiv_hom_comp`
-/

@[expose] public noncomputable section

open CategoryTheory Localization AlgebraicGeometry ComplexPoint TopologicalSpace

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ))

local instance bridgeHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bridgeSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  bridgeHasDerivedCategory X

local instance bridgeHasExt : HasExt.{0} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  inferInstance

/-- **Upstream's step-1 isomorphism in the derived category** (public form of upstream's private
`hypercohomologyAddEquivConstantCohomology_hom`). -/
lemma hyperEquiv_hom (n : ℕ) (α : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n) :
    (hypercohomologyAddEquivConstantCohomology ℚ X n α).hom =
      SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantIntegerSheafComplexIntIsoSingleULift X).hom
            ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).comp α (add_zero _)).comp
          (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantFieldSheafComplexIntIsoSingle ℚ X).hom) (zero_add _)) := by
  show SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (SmallShiftedHom.chgUniv.{0}
        (((SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantIntegerSheafComplexIntIsoSingleULift X).hom
            ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).comp α (add_zero _)).comp
          (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantFieldSheafComplexIntIsoSingle ℚ X).hom) (zero_add _))) = _
  exact SmallShiftedHom.equiv_chgUniv DerivedCategory.Q _

set_option maxHeartbeats 1000000 in
/-- **The same as a composite in the derived category**: the `Ext` class is the hypercohomology
class preceded by the inverse of the source comparison and followed by the target comparison. -/
lemma hyperEquiv_hom_comp (n : ℕ) (α : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n) :
    (hypercohomologyAddEquivConstantCohomology ℚ X n α).hom =
      (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantIntegerSheafComplexIntIsoSingleULift X).hom
            ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance))).comp
        ((SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q α).comp
          (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
            (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
              (constantFieldSheafComplexIntIsoSingle ℚ X).hom)) (zero_add _))
        (add_zero _) := by
  rw [hyperEquiv_hom, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_comp]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by simp)

end HodgeLadder.Cup
