module

public import HodgeLadder.Cup.SupportedFinal

/-!
# Supported classes on an open: cocycle representatives

Rung `supported-open-rep` (front `cup`, supported comparison on a general open). Let `V` be an
open of `X(ℂ)`, `Z ⊆ X(ℂ)` closed and `W = V ⊓ (X ∖ Z)`. Upstream's `relH ℚ_X n (W ≤ V)`, the
cohomology of the pair `(V, W)`, has upstream's flasque supported-sections model for the singular
cochain sheaves (`relHAddEquivSupportedSectionsHomologyOfFlasque` at `V`). Every class `α` in it is
represented, through that model, by the supported section `Θ₁ x` of a relative cocycle `x` of
`(V, W)`, and the Hom-complex cocycle out of the pair sheaf named by `Θ₁ x` names `α` in the
derived category. This is `exists_supported_rep` with `⊤` replaced by `V`.

## Main definitions

* `HodgeLadder.Cup.flasqueModelOpen`, `HodgeLadder.Cup.supCocycleOpen`

## Main results

* `HodgeLadder.Cup.exists_supported_rep_open`
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

local instance openHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance openSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  openHasDerivedCategory X

/-- Upstream's flasque supported-sections model of `H^n(V, V ⊓ (X ∖ Z); ℚ)` for the singular
cochain sheaves. -/
abbrev flasqueModelOpen (n : ℕ) :=
  relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X) Z.compl V
    (V ⊓ Z.compl) rfl (singularCochainSheafComplexInt_isFlasque X) n

/-- The Hom-complex cocycle out of the pair sheaf `ℤ[V, V ⊓ (X ∖ Z)]` named by a supported
cocycle over `V`. -/
def supCocycleOpen {p : ℕ} (s : (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.X (p : ℤ))
    (hs : (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.d (p : ℤ) ((p : ℤ) + 1) s = 0) :
    Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl) rfl))
      (singularCochainSheafComplexInt X ℚ) p :=
  Cocycle.mk ((homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl V
    (V ⊓ Z.compl) rfl (singularCochainSheafComplexInt X ℚ)).inv.f p s) ((p : ℤ) + 1) rfl (by
      have := map_d_eq_zero (homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X))
        Z.compl V (V ⊓ Z.compl) rfl (singularCochainSheafComplexInt X ℚ)).inv s hs
      exact this)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Every class of the pair `(V, V ⊓ (X ∖ Z))` has a relative-cocycle representative**, and the
Hom-complex cocycle of that representative names the class in the derived category. -/
theorem exists_supported_rep_open {p : ℕ}
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) p (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) :
    ∃ (x : (relSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.X (p : ℤ))
      (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0),
      flasqueModelOpen X Z V p α =
        cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp)
          ((rawMap (TopCat.of (ComplexPoint X)) Z.compl V).τ₁.f p x) (map_d_eq_zero _ x hx) ∧
      α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
        ShiftedHom.map (Cocycle.equivHomShift.symm (supCocycleOpen X Z V
          ((rawMap (TopCat.of (ComplexPoint X)) Z.compl V).τ₁.f p x) (map_d_eq_zero _ x hx)))
          DerivedCategory.Q := by
  obtain ⟨y, hy⟩ := (homologyMap_rawMap_bijective (TopCat.of (ComplexPoint X)) Z.compl V p).2
    (flasqueModelOpen X Z V p α)
  obtain ⟨x, hx, rfl⟩ := exists_cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y
  rw [homologyMap_cls] at hy
  refine ⟨x, hx, hy.symm, ?_⟩
  set s₀ := (rawMap (TopCat.of (ComplexPoint X)) Z.compl V).τ₁.f p x
  set z := supCocycleOpen X Z V s₀ (map_d_eq_zero _ x hx)
  set xz : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) p (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V)) :=
    Abelian.Ext.homAddEquiv.symm
      (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q ≫
        inv ((DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧'))
  have hxz : xz.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
    rw [← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  have hFxz := relHSupportedOfFlasque_mk (TopCat.of (ComplexPoint X)) Z.compl V (V ⊓ Z.compl)
    rfl 𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) p xz z hxz
  set e := homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl V
    (V ⊓ Z.compl) rfl (singularCochainSheafComplexInt X ℚ)
  have hcls : HomologicalComplex.homologyMap e.hom p
      ((homologyAddEquiv _ _ p).symm (CohomologyClass.mk z)) =
      cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
        (map_d_eq_zero _ x hx) := by
    rw [← homologyAddEquiv_cls z, AddEquiv.symm_apply_apply, homologyMap_cls]
    apply cls_eq
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ)) e.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  have hαx : flasqueModelOpen X Z V p α = flasqueModelOpen X Z V p xz := by
    rw [← hy]
    exact (hFxz.trans hcls).symm
  rw [(flasqueModelOpen X Z V p).injective hαx]
  exact hxz

end Variety

end HodgeLadder.Cup
