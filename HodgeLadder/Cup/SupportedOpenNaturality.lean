module

public import HodgeLadder.Cup.SupportedOpenFinal

/-!
# Naturality of the comparison on an open in the open

Rung `supported-open-naturality` (front `cup`, supported comparison on a general open). For opens
`V' ≤ V` of `X(ℂ)` and `Z ⊆ X(ℂ)` closed, restriction of pairs `(V', V' ⊓ (X ∖ Z)) → (V, V ⊓ (X ∖ Z))`
acts on upstream's sheaf-side `relH` by `relH.restrict` (precomposition with `pairSheafMap`) and on
the singular side by `relativeCohomologyMap (openInclusionPairMap …)`.

* `Φ_V` (upstream's flasque model at `V` followed by
  `supportedRationalSingularSectionCohomologyEquivRelative` at `V`) commutes with the two
  restrictions, with no sign: `Φ_{V'} ∘ relH.restrict = relativeCohomologyMap (openInclusionPairMap …) ∘ Φ_V`.
  The proof is upstream's `relHAddEquivSupportedSectionsHomologyOfFlasque_restrict` at
  `U' = U = X ∖ Z`, `supportedSectionsRestriction_refl`, and
  `supportedRationalSingularSectionCohomologyEquivRelative_naturality`.
* Restriction of pairs commutes with the product with an absolute class:
  `relH.restrict (α ∪ β) = (relH.restrict α) ∪ β`, from `comp_supCupY₀`.

With `relCupSing_naturality` and upstream's `cohomologyMap_comp`, these make the identity of
`cup_singular_comparison_open` natural in `V`.

## Main results

* `HodgeLadder.Cup.relH_restrict_supCupY`, `HodgeLadder.Cup.comparisonOpen_restrict`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section General

variable {Y : TopCat.{0}}

/-- **Restriction of pairs commutes with the product** with an absolute class: for a map of pairs
`(V', W') → (V, W)` of opens, `relH.restrict (α ∪ β) = (relH.restrict α) ∪ β`. No sign. -/
theorem relH_restrict_supCupY {W V W' V' : Opens Y} (f : W ⟶ V) (f' : W' ⟶ V') (a : W' ⟶ W)
    (b : V' ⟶ V) (w : f' ≫ b = a ≫ f) {p q : ℕ}
    (α : CategoryTheory.Sheaf.relH (constAb Y (AddCommGrpCat.of ℚ)) p f) (β : HQ Y q) (n : ℕ)
    (h : p + q = n) :
    CategoryTheory.Sheaf.relH.restrict (constAb Y (AddCommGrpCat.of ℚ)) f f' a b w n
        (supCupY α β n h) =
      supCupY (CategoryTheory.Sheaf.relH.restrict (constAb Y (AddCommGrpCat.of ℚ)) f f' a b w p α)
        β n h :=
  comp_supCupY₀ _ α β n h

end General

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))
  {V V' : Opens (ComplexPoint X)}

local instance openNatHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance openNatSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  openNatHasDerivedCategory X

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option backward.isDefEq.respectTransparency false in
/-- **`Φ_V` is natural in `V`.** For `V' ≤ V`, the comparison `Φ` at `V'` after upstream's
restriction `relH.restrict` of pairs is upstream's `relativeCohomologyMap` along the inclusion of
pairs `(V', V' ⊓ (X ∖ Z)) → (V, V ⊓ (X ∖ Z))` after `Φ` at `V`. No sign. -/
theorem comparisonOpen_restrict (hV : V' ≤ V) (n : ℕ)
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) n (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) :
    supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V'
        n (flasqueModelOpen X Z V' n
          (CategoryTheory.Sheaf.relH.restrict _ (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))
            (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V'))
            (homOfLE (inf_le_inf_right Z.compl hV)) (homOfLE hV) (Subsingleton.elim _ _) n α)) =
      relativeCohomologyMap ℚ n
        (openInclusionPairMap (TopCat.of (ComplexPoint X)) (Opens.infLELeft V Z.compl)
          (Opens.infLELeft V' Z.compl) (homOfLE hV) (homOfLE (inf_le_inf_right Z.compl hV)))
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
          Z.compl V n (flasqueModelOpen X Z V n α)) := by
  have h := relHAddEquivSupportedSectionsHomologyOfFlasque_restrict (TopCat.of (ComplexPoint X))
    (U := Z.compl) (V := V) (W := V ⊓ Z.compl) (U' := Z.compl) (V' := V') (W' := V' ⊓ Z.compl)
    (le_refl _) hV rfl rfl (inf_le_inf_right Z.compl hV) 𝓒(↧(ComplexPoint X); ℚ)
    (singularCochainSheafComplexInt X ℚ) (iotaQ X) (singularCochainSheafComplexInt_isFlasque X) n α
  rw [supportedSectionsRestriction_refl] at h
  erw [h]
  exact supportedRationalSingularSectionCohomologyEquivRelative_naturality
    (TopCat.of (ComplexPoint X)) Z.compl (homOfLE hV) n _

end Variety

end HodgeLadder.Cup
