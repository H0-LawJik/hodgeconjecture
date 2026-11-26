module

public import HodgeLadder.Cup.RightMultClass

/-!
# The resolution map `ι_ℤ` is upstream's

Rung `iota-upstream` (front `cup`). Upstream's step 1 compares `H^n(X; ℚ)` with the hypercohomology
of the singular cochain sheaves through `rationalToSingularCochainComplexInt : ℚ_X[0] ⟶ S_ℤ`.
Precomposed with the map `ℤ_X[0] ⟶ ℚ_X[0]` of constant sheaves, it is the map `ι_ℤ` of
`ext-class-right-mult`, after upstream's identification `constantIntegerSheafComplexIntIsoSingle`.

## Main definitions

* `HodgeLadder.Cup.intToRatComplex`

## Main results

* `HodgeLadder.Cup.extend_single_comp_f`, `HodgeLadder.Cup.iotaZ_eq`, `HodgeLadder.Cup.iso_hom_iotaZ`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular AlgebraicGeometry
  ComplexPoint TopCat.Sheaf

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable (X : Over (Spec ↧ℂ))

section General

variable {C : Type*} [Category C] [Abelian C]

/-- A map out of an extended single complex, computed in degree zero. -/
lemma extend_single_comp_f {A B : C} (φ : A ⟶ B) (S : CochainComplex C ℕ)
    (ψ : (CochainComplex.single₀ C).obj B ⟶ S) :
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0
        (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)).inv ≫
        HomologicalComplex.extendMap ((CochainComplex.single₀ C).map φ)
          ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ φ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 B).inv ≫ ψ.f 0 ≫
          (S.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 0 = 0)).inv := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (i := 0) (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl),
    HomologicalComplex.extendMap_f _ _ (i := 0) (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)]
  simp only [HomologicalComplex.single_map_f_self, CochainComplex.single₀, Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rfl

end General

/-- The map `ℤ_X[0] ⟶ ℚ_X[0]` of upstream's integer-indexed constant complexes. -/
def intToRatComplex : constantIntegerSheafComplexInt X ⟶ constantFieldSheafComplexInt ℚ X :=
  HomologicalComplex.extendMap ((CochainComplex.single₀ _).map
    (intToRat (TopCat.of (ComplexPoint X)))) ComplexShape.embeddingUpNat

/-- **`ι_ℤ` is upstream's map after `ℤ_X → ℚ_X`.** -/
theorem iotaZ_eq :
    iotaZ (TopCat.of (ComplexPoint X)) = (constantIntegerSheafComplexIntIsoSingle X).inv ≫
      intToRatComplex X ≫ rationalToSingularCochainComplexInt X := by
  apply HomologicalComplex.from_single_hom_ext
  rw [iotaZ, HomologicalComplex.mkHomFromSingle_f]
  erw [extend_single_comp_f]
  simp only [constantsToSingularCochainSheafComplex, CochainComplex.fromSingle₀Equiv,
    Equiv.coe_fn_symm_mk]
  rfl

/-- **The same, as upstream's map from its integer constant complex.** -/
theorem iso_hom_iotaZ :
    (constantIntegerSheafComplexIntIsoSingle X).hom ≫ iotaZ (TopCat.of (ComplexPoint X)) =
      intToRatComplex X ≫ rationalToSingularCochainComplexInt X := by
  rw [iotaZ_eq]
  erw [Iso.hom_inv_id_assoc]

end HodgeLadder.Cup
