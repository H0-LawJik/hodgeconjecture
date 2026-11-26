module

public import HodgeLadder.Cup.SupportedFinal
public import HodgeLadder.Cup.SupportedAgreement

/-!
# Forgetting the support against the absolute comparison

Rung `step1-of-hom`, part of `supported-forget-compat` (front `cup`). If an absolute class `y`,
followed by `ι : ℚ_X[0] → S`, is the class of a Hom-complex cocycle `w` out of `ℤ_X[0]`, then
upstream's step 1 of `Ψ` sends `y` to the class of `w` on upstream's integer constant complex. This
is the absolute comparison run from a cocycle representative, used to compute `Ψ` after
forgetting the support.

Rung `forget-support-cocycle`, also here: forgetting the support is precomposition with
`forgetMap : ℤ_X → ℤ[X, X ∖ Z]`, so on a cocycle representative it precomposes the cocycle.

## Main results

* `HodgeLadder.Cup.shiftedHom_step1_core`, `HodgeLadder.Cup.step1_of_hom`
* `HodgeLadder.Cup.forgetSupport_eq_comp`, `HodgeLadder.Cup.forgetSupport_named`
-/

@[expose] public noncomputable section

open CategoryTheory Localization AlgebraicGeometry ComplexPoint TopologicalSpace
  CochainComplex.HomComplex

namespace HodgeLadder.Cup

section Core

variable {D : Type*} [Category D] [HasShift D ℤ]

/-- The algebra of `step1_of_hom`: transport a shifted hom through isomorphisms of source and
target, then postcompose. -/
lemma shiftedHom_step1_core {Tz T Ae Fe S : D} (eA : Ae ≅ Tz) (eF : Fe ≅ T) (ι : Fe ⟶ S) {p : ℤ}
    (Xh : ShiftedHom Tz T p) (ax : ShiftedHom Ae Fe p)
    (hx : Xh = (ShiftedHom.mk₀ (0 : ℤ) rfl eA.inv).comp
      (ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p)) (add_zero p))
    (φ : T ⟶ S) (hφ : eF.inv ≫ ι = φ) (W : ShiftedHom Tz S p) (hW : Xh ≫ φ⟦p⟧' = W) :
    ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add p) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp W (add_zero p) := by
  have cancelA : ∀ {a : ℤ} (f : ShiftedHom Ae T a),
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp
        ((ShiftedHom.mk₀ (0 : ℤ) rfl eA.inv).comp f (add_zero a)) (add_zero a) = f := by
    intro a f
    rw [← ShiftedHom.comp_assoc _ _ _ (add_zero 0) (add_zero a) (by simp),
      ShiftedHom.mk₀_comp_mk₀, Iso.hom_inv_id, ShiftedHom.mk₀_id_comp]
  have hax : ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp Xh (add_zero p) := by
    rw [hx, cancelA]
  have e2 : ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add p) =
      (ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) (zero_add p) := by
    rw [ShiftedHom.comp_assoc _ _ _ (zero_add p) (add_zero 0) (by simp), ShiftedHom.mk₀_comp_mk₀,
      Iso.hom_inv_id_assoc]
  rw [e2, hax, ShiftedHom.comp_assoc _ _ _ (add_zero p) (zero_add p) (by simp), hφ,
    ShiftedHom.comp_mk₀, hW]

end Core

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

attribute [local instance] endHasDerivedCategory endSiteHasDerivedCategory endHasExt

variable (X : Over (Spec ↧ℂ))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Upstream's step 1 on a class named by a cocycle**: if `y` followed by `ι : ℚ_X[0] → S` is the
class of a Hom-complex cocycle `w` out of `ℤ_X[0]`, then step 1 of `Ψ y` is the class of `w`
pulled back to upstream's integer constant complex. -/
theorem step1_of_hom [IsIntegral X.left] [Smooth X.hom] {n : ℕ} (y : H^n(X; ℚ))
    (w : Cocycle ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)))) (singularCochainSheafComplexInt X ℚ) n)
    (hy : y.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm w) DerivedCategory.Q) :
    rationalCohomologySingularCochainAddEquiv X n y =
      (CohomologyClass.mk (w.precomp (constantIntegerSheafComplexIntIsoSingleULift X).hom)
        ).toSmallShiftedHom := by
  have : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  have hbx := hyperEquiv_hom_comp X n ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm y)
  rw [AddEquiv.apply_symm_apply, SmallShiftedHom.equiv_mk₀Inv, SmallShiftedHom.equiv_mk₀] at hbx
  have hcore := shiftedHom_step1_core
    (Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance))
    (DerivedCategory.Q.mapIso (constantFieldSheafComplexIntIsoSingle ℚ X))
    (DerivedCategory.Q.map (rationalToSingularCochainComplexInt X)) _ _ hbx
    (DerivedCategory.Q.map (iotaQ X)) (by rw [iotaQ, CategoryTheory.Functor.map_comp]; rfl) _ hy
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [rationalCohomologySingularCochainAddEquiv_apply, toSmallShiftedHom_precomp,
    SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
    CohomologyClass.equiv_toSmallShiftedHom_mk]
  change SmallShiftedHom.equiv _ _ (((hypercohomologyAddEquivConstantCohomology ℚ X n).symm y).comp
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (rationalToSingularCochainComplexInt X)) (zero_add _)) = _
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀]
  exact hcore

/-- The map `ℤ_X → ℤ[X, X ∖ Z]` along which upstream forgets the support. -/
abbrev forgetMap (Z : Closeds (ComplexPoint X)) :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
      TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) :=
  (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso Limits.isTerminalTop).inv ≫
    Limits.cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf _).map (homOfLE (le_top : Z.compl ≤ ⊤)))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the support is precomposition with `forgetMap`.** -/
lemma forgetSupport_eq_comp (Z : Closeds (ComplexPoint X)) {n : ℕ} (α : H_[Z]^n(X; ℚ)) :
    forgetSupport ℚ X Z n α = (Abelian.Ext.mk₀ (forgetMap X Z)).comp α (zero_add n) := by
  simp only [forgetSupport, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass]
  change (Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp α (zero_add n)) (zero_add n) = _
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the support on a cocycle representative**: if `α` followed by `ι` is the class of
`z`, then `forgetSupport α` followed by `ι` is the class of `z` precomposed with `forgetMap`. -/
lemma forgetSupport_named (Z : Closeds (ComplexPoint X)) {n : ℕ} (α : H_[Z]^n(X; ℚ))
    (z : Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
      (singularCochainSheafComplexInt X ℚ) n)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    (forgetSupport ℚ X Z n α).hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (z.precomp ((CochainComplex.singleFunctor _ 0).map (forgetMap X Z)))) DerivedCategory.Q := by
  rw [forgetSupport_eq_comp, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    ← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl,
    ShiftedHom.comp_assoc (a₂₃ := (n : ℤ)) _ _ _ (by simp) (by simp) (by simp),
    ShiftedHom.comp_mk₀, hα, ShiftedHom.mk₀_comp, Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rfl

end HodgeLadder.Cup
