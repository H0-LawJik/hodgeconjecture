module

public import HodgeLadder.Cup.SupportedOpenFinal

/-!
# The comparison on an open, specialized to the whole space

Rung `cup-comparison-supported-open` (front `cup`, supported comparison on a general open).
`cup_singular_comparison_open` spells the second open of the pair as `V ⊓ (X ∖ Z)`; at `V = ⊤`
this is `⊤ ⊓ (X ∖ Z)`, while upstream's `supportH` and `cup_singular_comparison_supported` use
`X ∖ Z`. The two are propositionally equal and definitionally distinct, so the statements have
different types. Upstream's flasque model takes the second open `W` and a proof of `V ⊓ U = W`, and the
`homOfLE` proof in its domain is irrelevant, so the comparison stated for any such `(W, hW)`
reduces to the `rfl` case by `subst`. At `V = ⊤`, upstream's pullback along the inclusion of the
open `⊤` is the top-open transport `singularCochainComplexIsoTopOpen`, with no sign. Together these
recover `cup_singular_comparison_supported` verbatim from `cup_singular_comparison_open`.

## Main results

* `HodgeLadder.Cup.cohomologyMap_inclusion_top`
* `HodgeLadder.Cup.cup_singular_comparison_open_of_eq`
* `HodgeLadder.Cup.cup_singular_comparison_supported_of_open`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

section General

variable {Y : TopCat.{0}}

/-- Upstream's pullback along the inclusion of the open `⊤` is the top-open transport. -/
lemma cohomologyMap_inclusion_top (q : ℕ) (c : Cohomology ℚ Y q) :
    cohomologyMap ℚ q (Opens.inclusion' (X := Y) (⊤ : Opens Y)) c =
      HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).hom q c := by
  have h := isoTopOpen_inv_comp_inclusion (Y := Y) ⊤
  have h1 : (openSingularChainComplexFunctor ℚ Y).map (homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤)) =
      𝟙 _ := by
    rw [show homOfLE (le_top : (⊤ : Opens Y) ≤ ⊤) = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rw [h1, HomologicalComplex.linearDualMap_id] at h
  have h2 : singularCochainComplexMap ℚ (Opens.inclusion' (X := Y) (⊤ : Opens Y)) =
      (singularCochainComplexIsoTopOpen ℚ Y).hom := by
    have h3 := congrArg (fun g => (singularCochainComplexIsoTopOpen ℚ Y).hom ≫ g) h
    simp only [Iso.hom_inv_id_assoc] at h3
    erw [h3]
    exact Category.comp_id _
  unfold cohomologyMap
  rw [h2]
  rfl

end General

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))
  (V : Opens (ComplexPoint X))

local instance openTopHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance openTopSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  openTopHasDerivedCategory X

set_option maxRecDepth 20000 in
set_option backward.isDefEq.respectTransparency false in
/-- `cup_singular_comparison_open` with the second open of the pair given as any `W` with
`V ⊓ (X ∖ Z) = W`, as in upstream's flasque model. -/
theorem cup_singular_comparison_open_of_eq (W : Opens (ComplexPoint X))
    (hW : V ⊓ Z.compl = W) {p q : ℕ}
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) p (homOfLE (hW ▸ (inf_le_left : V ⊓ Z.compl ≤ V) : W ≤ V)))
    (β : H^q(X; ℚ)) :
    supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V
        (p + q) (relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
          𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X) Z.compl V W hW
          (singularCochainSheafComplexInt_isFlasque X) (p + q) (supCupY α β (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl V)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V
          p (relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
            𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X) Z.compl V W hW
            (singularCochainSheafComplexInt_isFlasque X) p α))
        (cohomologyMap ℚ q (Opens.inclusion' (X := TopCat.of (ComplexPoint X)) V)
          (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl := by
  subst hW
  exact cup_singular_comparison_open X Z V α β

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The comparison at `V = ⊤` from the comparison on an open.** `cup_singular_comparison_supported`,
verbatim, derived from `cup_singular_comparison_open` at `V = ⊤` through
`cup_singular_comparison_open_of_eq` (with `W = X ∖ Z`) and `cohomologyMap_inclusion_top`. -/
theorem cup_singular_comparison_supported_of_open {p q : ℕ} (α : H_[Z]^p(X; ℚ))
    (β : H^q(X; ℚ)) :
    supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (p + q) (flasqueModel X Z (p + q) (supCup α β (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
          p (flasqueModel X Z p α))
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
          (TopCat.of (ComplexPoint X))).hom q (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl := by
  have h := cup_singular_comparison_open_of_eq X Z ⊤ Z.compl (top_inf_eq _) α β
  rw [cohomologyMap_inclusion_top] at h
  exact h

end Variety

end HodgeLadder.Cup
