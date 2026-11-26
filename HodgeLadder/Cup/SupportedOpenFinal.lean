module

public import HodgeLadder.Cup.SupportedOpenClass
public import HodgeLadder.Cup.RestrictOpen

/-!
# The product on an open against the relative singular cup product

Rung `cup-comparison-supported-open` (front `cup`, supported comparison on a general open). Let
`V` be an open of `X(ℂ)`, `Z ⊆ X(ℂ)` closed and `W = V ⊓ (X ∖ Z)`. Let `Φ_V` be upstream's flasque
supported-sections model of `relH ℚ_X n (W ≤ V)` for the singular cochain sheaves, followed by
upstream's `supportedRationalSingularSectionCohomologyEquivRelative` at `V`, landing in
`H^n(V, W; ℚ)`. For `α ∈ relH ℚ_X p (W ≤ V)` and `β ∈ H^q(X; ℚ)`, with `α ∪ β = supCupY α β`
(Yoneda composition with the lift of `β`),
`Φ_V (α ∪ β) = (−1)^{pq} · relCupSing (Φ_V α) (β|_V)`, where `β|_V` is `Ψ β` pulled back along the
inclusion `V ⟶ X(ℂ)` by upstream's `cohomologyMap`. The sign is the one of `V = ⊤`
(`cup_singular_comparison_supported`): it comes from `rightMulCochain`, and no sign enters through
the supported models or the restriction to `V`. Conventions: `docs/conventions.md`, rows "Cup
product" and "Supported comparison Φ".

## Main results

* `HodgeLadder.Cup.cup_singular_comparison_open`
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

local instance openFinHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance openFinSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  openFinHasDerivedCategory X

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The product on an open against the relative singular cup product.** Let `Φ_V` be the
composite of upstream's flasque supported-sections model at `V` and
`supportedRationalSingularSectionCohomologyEquivRelative` at `V`, `U = X ∖ Z`. Then
`Φ_V (α ∪ β) = (−1)^{pq} · relCupSing (Φ_V α) (β|_V)`, with `β|_V` upstream's pullback of `Ψ β`
along the inclusion of `V`. -/
theorem cup_singular_comparison_open {p q : ℕ}
    (α : CategoryTheory.Sheaf.relH ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) p (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))) (β : H^q(X; ℚ)) :
    supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V
        (p + q) (flasqueModelOpen X Z V (p + q) (supCupY α β (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl V)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V
          p (flasqueModelOpen X Z V p α))
        (cohomologyMap ℚ q (Opens.inclusion' (X := TopCat.of (ComplexPoint X)) V)
          (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl := by
  obtain ⟨b, hb, hβb⟩ := exists_singClass (rationalCohomologyAddEquivSingularCohomology X q β)
  have hβ := globalSections_of_singClass X β b hb hβb.symm
  obtain ⟨x, hx, hFα, hα⟩ := exists_supported_rep_open X Z V α
  set s₀ := (rawMap (TopCat.of (ComplexPoint X)) Z.compl V).τ₁.f p x
  set z := supCocycleOpen X Z V s₀ (map_d_eq_zero _ x hx)
  have hsup := supCup_flasque_open X Z V α β b hb hβ z hα (p + q) rfl
  set e := homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl V
    (V ⊓ Z.compl) rfl (singularCochainSheafComplexInt X ℚ)
  set w := cocycleComp z (rightMulCocycle b hb)
    (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)
  set s' := e.hom.f ((p + q : ℕ) : ℤ) w.1
  have hs'd : (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.d ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) s' = 0 :=
    map_d_eq_zero e.hom w.1 (Cocycle.δ_eq_zero w _)
  have hcls' : HomologicalComplex.homologyMap e.hom ((p + q : ℕ) : ℤ)
      ((homologyAddEquiv _ _ _).symm (CohomologyClass.mk w)) =
      cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ ((p + q : ℕ) : ℤ)
        (((p + q : ℕ) : ℤ) + 1) (by simp) s' hs'd := by
    rw [← homologyAddEquiv_cls w]
    erw [AddEquiv.symm_apply_apply]
    exact homologyMap_cls e.hom _ _ _ w.1 _
  erw [hsup]
  rw [hcls']
  have hes : e.hom.f (p : ℤ) z.1 = s₀ := by
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ)) e.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  set u : ℤ := (((p : ℤ) * q).negOnePow : ℤ)
  have hu : u * u = 1 := by
    simp only [u, ← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hsec' : (sInt_XIso (X := TopCat.of (ComplexPoint X))
      (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ))).hom.hom.app (op V)
        ((supSeq (TopCat.of (ComplexPoint X)) Z.compl V).f.f _ s') =
      u • (rightMulSheaf b p (p + q) rfl).hom.app (op V)
        ((sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom.hom.app (op V)
          ((supSeq (TopCat.of (ComplexPoint X)) Z.compl V).f.f p s₀)) := by
    have h1 := supportedSection_eq_pairEval' (Y := TopCat.of (ComplexPoint X)) Z.compl V
      (V ⊓ Z.compl) rfl (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ)) w.1
    have h2 := supportedSection_eq_pairEval' (Y := TopCat.of (ComplexPoint X)) Z.compl V
      (V ⊓ Z.compl) rfl (rfl : (p : ℤ) = p) z.1
    have h3 := pairSheafEvaluation_cocycleComp_rightMul' (Y := TopCat.of (ComplexPoint X)) Z.compl
      V (V ⊓ Z.compl) rfl z b hb
    rw [← hes]
    exact h1.trans (h3.trans (by rw [← h2]; rfl))
  obtain ⟨s'', hs''⟩ : ∃ t, t = u • s' := ⟨_, rfl⟩
  have hs''d : (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁.d ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) s'' = 0 := by
    rw [hs'', map_zsmul, hs'd, smul_zero]
  have hsec'' : (sInt_XIso (X := TopCat.of (ComplexPoint X))
      (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ))).hom.hom.app (op V)
        ((supSeq (TopCat.of (ComplexPoint X)) Z.compl V).f.f _ s'') =
      (rightMulSheaf b p (p + q) rfl).hom.app (op V)
        ((sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom.hom.app (op V)
          ((supSeq (TopCat.of (ComplexPoint X)) Z.compl V).f.f p s₀)) := by
    rw [hs'', map_zsmul, map_zsmul]
    erw [hsec']
    rw [smul_smul, hu, one_smul]
  have hbV : (SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl V).fst
      ).linearDualCochainComplex.d q (q + 1) (resQ b (op V)) = 0 := by
    change (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op V)
      (resQ b (op V)) = 0
    rw [resQ_coboundary, hb]
    exact map_zero _
  have hrel := supported_relative_cup (TopCat.of (ComplexPoint X)) Z.compl V x hx b hbV (p + q) rfl
    s'' hs''d hsec''
  have hss : s' = u • s'' := by
    rw [hs'', smul_smul, hu, one_smul]
  have hc : cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) (by simp) s' hs'd =
      u • cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ ((p + q : ℕ) : ℤ)
        (((p + q : ℕ) : ℤ) + 1) (by simp) s'' hs''d :=
    (cls_eq _ (by simp) hs'd (hss ▸ hs'd) hss).trans
      (cls_zsmul (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ (by simp) u s'' hs''d _)
  refine (congrArg (supportedRationalSingularSectionCohomologyEquivRelative
    (TopCat.of (ComplexPoint X)) Z.compl V (p + q)) hc).trans ?_
  refine (map_zsmul (supportedRationalSingularSectionCohomologyEquivRelative
    (TopCat.of (ComplexPoint X)) Z.compl V (p + q)) u _).trans ?_
  have hA : supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
      Z.compl V p (flasqueModelOpen X Z V p α) =
      supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V p
        (cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
          (map_d_eq_zero _ x hx)) := congrArg _ hFα
  have hB : cohomologyMap ℚ q (Opens.inclusion' (X := TopCat.of (ComplexPoint X)) V)
      (rationalCohomologyAddEquivSingularCohomology X q β) =
      (SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl V).fst
        ).linearDualCochainComplex.homologyπ q
        ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl V).fst
          ).linearDualCochainComplex.cyclesMk (resQ b (op V)) (q + 1) (by simp) hbV) := by
    rw [← hβb]
    exact cohomologyMap_inclusion_singClass_pair (Y := TopCat.of (ComplexPoint X)) V Z.compl b hb hbV
  have hR : relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl V)
      (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V p
        (cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl V).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
          (map_d_eq_zero _ x hx)))
      ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl V).fst
        ).linearDualCochainComplex.homologyπ q
        ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl V).fst
          ).linearDualCochainComplex.cyclesMk (resQ b (op V)) (q + 1) (by simp) hbV)) (p + q) rfl =
      relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl V)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl V
          p (flasqueModelOpen X Z V p α))
        (cohomologyMap ℚ q (Opens.inclusion' (X := TopCat.of (ComplexPoint X)) V)
          (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl :=
    congrArg₂ (fun a c => relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl V) a c (p + q) rfl)
      hA.symm hB.symm
  exact congrArg (u • ·) (hrel.trans hR)

end Variety

end HodgeLadder.Cup
