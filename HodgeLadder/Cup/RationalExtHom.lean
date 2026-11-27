module

public import HodgeLadder.Cup.SheafExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The rational `Ext` identification as a composite in the derived category

Part of rung `rational-hypercohomology-equiv` (front `cup`). `HodgeLadder.Cup.rationalExtEquiv`
identifies `Hⁿ(Y; ℚ) = Extⁿ(ℤ_Y, ℚ_Y)` with `Extⁿ(ℚ_Y, ℚ_Y)` through the exact adjunction
`ℚ ⊗ − ⊣ forget`. Here its value is written as a morphism in the derived category of sheaves of
`ℚ`-vector spaces: the derived functor of `ℚ ⊗ −` applied to the class, followed by the counit.
The statement holds for a general space `Y`, with the `HasDerivedCategory` instances as
arguments; stating it at `TopCat.of (ComplexPoint X)` directly costs several minutes of kernel
time, against about one minute here plus a cheap instantiation.

## Main results

* `CategoryTheory.Adjunction.extEquiv_symm_hom`: Mathlib's `Adjunction.extEquiv.symm` in the
  derived category
* `HodgeLadder.Ext.postcompIsoAddEquiv_hom`, `HodgeLadder.Ext.precompIsoAddEquiv_hom`
* `HodgeLadder.Cup.rationalExtEquiv_hom`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

section General

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasExt.{0} C] [HasExt.{0} D] [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- `Adjunction.extEquiv.symm` as a composite in the derived category: the derived functor of
the left adjoint applied to the class, followed by the counit. -/
lemma CategoryTheory.Adjunction.extEquiv_symm_hom (adj : F ⊣ G) {X : C} {Y : D} {n : ℕ}
    (e : Abelian.Ext.{0} X (G.obj Y) n) :
    (adj.extEquiv.symm e).hom =
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ F.mapDerivedCategory.map e.hom ≫
        (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app _)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor _ 0).map (adj.counit.app Y))⟦(n : ℤ)⟧' := by
  simp only [Adjunction.extEquiv_symm_apply, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    Abelian.Ext.mapExactFunctor_hom, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc]

/-- `HodgeLadder.Ext.postcompIsoAddEquiv` in the derived category. -/
lemma HodgeLadder.Ext.postcompIsoAddEquiv_hom {X Y Z : C} (e : Y ≅ Z) (n : ℕ)
    (α : Abelian.Ext.{0} X Y n) :
    (HodgeLadder.Ext.postcompIsoAddEquiv e X n α).hom =
      α.hom ≫ ((DerivedCategory.singleFunctor _ 0).map e.hom)⟦(n : ℤ)⟧' := by
  simp only [HodgeLadder.Ext.postcompIsoAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]

/-- `HodgeLadder.Ext.precompIsoAddEquiv` in the derived category. -/
lemma HodgeLadder.Ext.precompIsoAddEquiv_hom {X Y Z : C} (e : X ≅ Y) (n : ℕ)
    (α : Abelian.Ext.{0} Y Z n) :
    (HodgeLadder.Ext.precompIsoAddEquiv e Z n α).hom =
      (DerivedCategory.singleFunctor _ 0).map e.hom ≫ α.hom := by
  simp only [HodgeLadder.Ext.precompIsoAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]

end General

namespace HodgeLadder.Cup

variable (Y : TopCat.{0}) [HasDerivedCategory (Sheaf (J Y) AddCommGrpCat.{0})]
  [HasDerivedCategory (Sheaf (J Y) (ModuleCat.{0} ℚ))]

/-- **`rationalExtEquiv` as a composite in the derived category of rational sheaves**:
`ℚ ⊗ ℤ ≅ ℚ`, then the derived `ℚ ⊗ −` of the class followed by `forgetQX⁻¹`, then the counit of
`ℚ ⊗ − ⊣ forget` at `ℚ_Y`. -/
lemma rationalExtEquiv_hom (n : ℕ) (α : Sheaf.H.{0} (constAb Y (AddCommGrpCat.of ℚ)) n) :
    (rationalExtEquiv Y n α).hom =
      (DerivedCategory.singleFunctor _ 0).map (tensorQSheafInt Y).inv ≫
      ((tensorQSheaf Y).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (tensorQSheaf Y).mapDerivedCategory.map
        (α.hom ≫ ((DerivedCategory.singleFunctor _ 0).map (forgetQX Y).inv)⟦(n : ℤ)⟧') ≫
      ((tensorQSheaf Y).mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
      (((tensorQSheaf Y).mapDerivedCategorySingleFunctor 0).hom.app _)⟦(n : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map
        ((adjQSheaf Y).counit.app (QX Y)))⟦(n : ℤ)⟧' := by
  change (extPrecompEquiv _ n ((extEquivQ Y _ _ n).symm
    (extPostcompEquiv _ n α))).hom = _
  rw [extPrecompEquiv, HodgeLadder.Ext.precompIsoAddEquiv_hom, extEquivQ,
    Adjunction.extEquiv_symm_hom, extPostcompEquiv, HodgeLadder.Ext.postcompIsoAddEquiv_hom]
  rfl

end HodgeLadder.Cup
