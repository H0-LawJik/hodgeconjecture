module

public import HodgeLadder.Hodge.RationalDeRhamComplex
public import HodgeLadder.Tests.Witness
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare

/-!
# The de Rham unit is nonzero on a point

Rung `de-rham-unit-nonzero` (red team of `rational-de-rham-complex`, change 7, section 7b). The
unit lemma `HodgeLadder.forget_rationalDeRhamUnit` identifies the rational unit
`ℚ_X[0] ⟶ Ω•_ℚ` with upstream's `fieldToHolomorphicDeRhamComplexInt ℚ X` through isomorphisms.
It would hold for a trivial reason if both maps were zero. This file rules that out: on any
`X` with a complex point, upstream's unit `K_X[0] ⟶ Ω•(X)` is nonzero for every field
`K` embedded in `ℂ`, and so is `rationalDeRhamUnit X`. The test case is
`HodgeLadder.Tests.point`, `Spec ℂ` over itself, which carries the instances `IsIntegral` and
`Smooth` that both units need.

The proof works in degree zero. Upstream's unit there is `K_X ⟶ ℂ_X ⟶ Ω⁰`, the sheafification
of the presheaf map `c ↦ [c]`. If it were zero, the presheaf map followed by the sheafification
map of `Ω⁰` would be zero; on the stalk at a point `x` the sheafification map is an isomorphism
(Mathlib's `stalkFunctor_map_unit_toSheafify_isIso`), so the germ at `x` of the constant
zero-form `[1]` would vanish, and `[1]` would be zero on an open neighborhood `W` of `x`. Its
chart evaluation at `x` is `1`.

The same argument with `n • f'` in place of `f'` gives the non-torsion forms `n • ι ≠ 0` for
`n ≠ 0`, and at `n = 2` the sign separations `ι ≠ −ι` and
`rationalDeRhamUnit X ≠ −rationalDeRhamUnit X`: `forget_rationalDeRhamUnit` is false with
`−rationalDeRhamUnit X` in place of the unit (red team of this rung, change 4).

## Main results

* `HodgeLadder.Tests.holomorphicFormOfConstant_ne_zero`: `[c] ≠ 0` on a nonempty open, `c ≠ 0`
* `HodgeLadder.Tests.fieldToHolomorphicFormZeroSheaf_ne_zero`: `K_X ⟶ ℂ_X ⟶ Ω⁰` is nonzero
* `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_ne_zero`: upstream's unit is nonzero on
  any `X` with a complex point
* `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_point_ne_zero`: the rung's statement,
  `fieldToHolomorphicDeRhamComplexInt ℚ point ≠ 0`
* `HodgeLadder.Tests.rationalDeRhamUnit_ne_zero`,
  `HodgeLadder.Tests.rationalDeRhamUnit_point_ne_zero`: the rational unit is nonzero, from
  `forget_rationalDeRhamUnit`
* `HodgeLadder.Tests.nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero`,
  `HodgeLadder.Tests.nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero`: the non-torsion forms
* `HodgeLadder.Tests.fieldToHolomorphicDeRhamComplexInt_ne_neg`,
  `HodgeLadder.Tests.rationalDeRhamUnit_ne_neg`: the sign separations
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint TopologicalSpace

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Tests

/-- On a nonempty open, the class of a nonzero complex constant is a nonzero holomorphic
zero-form: its chart evaluation at any point is the constant. The same argument as upstream's
`holomorphicFormOfConstant_injective`, which is `private`. -/
theorem holomorphicFormOfConstant_ne_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) [Nonempty U.unop] {c : ℂ} (hc : c ≠ 0) :
    holomorphicFormOfConstant X d U c ≠ 0 := by
  intro hzero
  let a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0 :=
    Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) c
  have ha : a ∈ chartEvaluationKernel X d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    rwa [Submodule.Quotient.mk_eq_zero] at hzero
  let x : U.unop := Classical.arbitrary U.unop
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (mem_chartEvaluationKernel_iff X d U 0 a).1 ha x.1 (e x.1) hxe
  rw [chartEvaluation_ofConstant X d U x.1 c hxe] at heval
  have hcoeff := congrArg (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
  exact hc (by simpa using hcoeff)

/-- **Degree zero.** On a scheme with a complex point, upstream's degree-zero unit
`K_X ⟶ ℂ_X ⟶ Ω⁰` (the constant sheaf map along `K → ℂ`, then constants as zero-forms) is not
zero: the germ of `[1]` at the point survives sheafification. -/
theorem fieldToHolomorphicFormZeroSheaf_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [Nonempty (ComplexPoint X)] :
    fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d ≠ 0 := by
  intro hfg
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let Q := holomorphicDeRhamPresheaf X d 0
  let f' : 𝓒ᵖ(↧(ComplexPoint X); K) ⟶ Q :=
    (Functor.const _).map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
      constantsToHolomorphicDeRhamZero X d
  have hf' : sheafifyMap J f' = 0 := by
    have : (presheafToSheaf J AddCommGrpCat).map f' = 0 := by
      rw [Functor.map_comp]
      exact hfg
    change ((presheafToSheaf J AddCommGrpCat).map f').hom = 0
    rw [this]
    rfl
  have hnat := toSheafify_naturality J f'
  rw [hf', comp_zero] at hnat
  let x : ComplexPoint X := Classical.arbitrary _
  have hst := congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map hnat
  rw [Functor.map_comp, Functor.map_zero] at hst
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat Q
  have hst' : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f' = 0 :=
    (cancel_mono _).1 (hst.trans zero_comp.symm)
  have hgerm := congrArg (fun φ => φ (TopCat.Presheaf.germ 𝓒ᵖ(↧(ComplexPoint X); K) ⊤ x (by simp)
    (1 : K))) hst'
  simp only at hgerm
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hgerm
  obtain ⟨W, hxW, iU, iV, hW⟩ := Q.germ_eq (U := ⊤) (V := ⊤) x (by simp) (by simp)
    (f'.app _ (1 : K)) 0 (hgerm.trans (map_zero _).symm)
  rw [map_zero] at hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  apply holomorphicFormOfConstant_ne_zero X d (.op W) (one_ne_zero (α := ℂ))
  refine Eq.trans ?_ hW
  change _ = holomorphicFormRestriction X d iU.op 0
    (holomorphicFormOfConstant X d (.op ⊤) (algebraMap K ℂ 1))
  rw [holomorphicFormRestriction_ofConstant, (algebraMap K ℂ).map_one]

/-- **Upstream's unit is nonzero.** On a smooth integral scheme with a complex point, the map
`K_X[0] ⟶ Ω•(X)` is not zero, for every field `K` embedded in `ℂ`. Its degree-zero component is
`K_X ⟶ ℂ_X ⟶ Ω⁰` up to the isomorphisms of single and extended complexes. -/
theorem fieldToHolomorphicDeRhamComplexInt_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [Nonempty (ComplexPoint X)] :
    fieldToHolomorphicDeRhamComplexInt K X ≠ 0 := by
  intro h
  have hg : constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (holomorphicDeRhamComplex X (dim X.left)).d 0 1 = 0 := by
    rw [holomorphicDeRhamComplex_d]
    exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential X _
  have hR := single_map_comp_extendSingleIso_inv_comp (C := AnalyticAdditiveSheaf X)
    (𝟙 _) (fieldToComplexConstantSheaf K X) (L := holomorphicDeRhamComplex X (dim X.left))
    (constantsToHolomorphicDeRhamZeroSheaf X _) hg
  have hR' := hR.symm.trans (show _ = 0 by
    change _ ≫ _ ≫ fieldToHolomorphicDeRhamComplexInt K X = 0
    rw [h, comp_zero, comp_zero])
  have h0 := congrArg (fun f => f.f 0 ≫ ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
    ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom) hR'
  rw [homFromSingleExtend_f_zero, HomologicalComplex.zero_f, zero_comp, Category.id_comp] at h0
  have hfg : fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X _ = 0 :=
    (cancel_epi _).1 (h0.trans comp_zero.symm)
  exact fieldToHolomorphicFormZeroSheaf_ne_zero K X _ hfg

/-- **The rung's statement.** Upstream's unit `ℚ_X[0] ⟶ Ω•(X)` is nonzero on `point = Spec ℂ`. -/
theorem fieldToHolomorphicDeRhamComplexInt_point_ne_zero :
    fieldToHolomorphicDeRhamComplexInt ℚ point ≠ 0 := by
  have : Nonempty (ComplexPoint point) := ⟨𝟙 _⟩
  exact fieldToHolomorphicDeRhamComplexInt_ne_zero ℚ point

/-- **The rational unit is nonzero.** On a smooth integral scheme with a complex point,
`rationalDeRhamUnit X ≠ 0`: by `forget_rationalDeRhamUnit`, if it were zero, then
`forgetUnitComplexIso X` followed by upstream's unit would be zero, and cancelling the
isomorphism contradicts `fieldToHolomorphicDeRhamComplexInt_ne_zero`. -/
theorem rationalDeRhamUnit_ne_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [Nonempty (ComplexPoint X)] : rationalDeRhamUnit X ≠ 0 := by
  have : (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).Additive :=
    Cup.forgetSheaf_additive _
  have : (forgetComplex X).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (instAdditiveHomologicalComplexMapHomologicalComplex _ _)
  intro hu
  have h := forget_rationalDeRhamUnit X
  rw [hu, Functor.map_zero, zero_comp] at h
  exact fieldToHolomorphicDeRhamComplexInt_ne_zero ℚ X
    ((cancel_epi (forgetUnitComplexIso X).hom).1 (h.symm.trans comp_zero.symm))

/-- **The corollary on a point.** `rationalDeRhamUnit point ≠ 0`. -/
theorem rationalDeRhamUnit_point_ne_zero : rationalDeRhamUnit point ≠ 0 := by
  have : Nonempty (ComplexPoint point) := ⟨𝟙 _⟩
  exact rationalDeRhamUnit_ne_zero point

/-- Non-torsion form of the degree-zero test: `n • (K_X ⟶ ℂ_X ⟶ Ω⁰) ≠ 0` for `n ≠ 0`. -/
theorem nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [Nonempty (ComplexPoint X)] {n : ℕ} (hn : n ≠ 0) :
    n • (fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X d) ≠ 0 := by
  intro hfg
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let Q := holomorphicDeRhamPresheaf X d 0
  let f' : 𝓒ᵖ(↧(ComplexPoint X); K) ⟶ Q :=
    n • ((Functor.const _).map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
      constantsToHolomorphicDeRhamZero X d)
  have hf' : sheafifyMap J f' = 0 := by
    have : (presheafToSheaf J AddCommGrpCat).map f' = 0 := by
      rw [Functor.map_nsmul, Functor.map_comp]
      exact hfg
    change ((presheafToSheaf J AddCommGrpCat).map f').hom = 0
    rw [this]
    rfl
  have hnat := toSheafify_naturality J f'
  rw [hf', comp_zero] at hnat
  let x : ComplexPoint X := Classical.arbitrary _
  have hst := congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map hnat
  rw [Functor.map_comp, Functor.map_zero] at hst
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat Q
  have hst' : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f' = 0 :=
    (cancel_mono _).1 (hst.trans zero_comp.symm)
  have hgerm := congrArg (fun φ => φ (TopCat.Presheaf.germ 𝓒ᵖ(↧(ComplexPoint X); K) ⊤ x (by simp)
    (1 : K))) hst'
  simp only at hgerm
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hgerm
  obtain ⟨W, hxW, iU, iV, hW⟩ := Q.germ_eq (U := ⊤) (V := ⊤) x (by simp) (by simp)
    (f'.app _ (1 : K)) 0 (hgerm.trans (map_zero _).symm)
  rw [map_zero] at hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have key : (holomorphicFormOfConstant X d (.op W) (n : ℂ) : HolomorphicForm X d (.op W) 0) =
      holomorphicFormRestriction X d iU.op 0
        (n • holomorphicFormOfConstant X d (.op ⊤) (algebraMap K ℂ 1)) := by
    rw [map_nsmul, holomorphicFormRestriction_ofConstant, (algebraMap K ℂ).map_one,
      ← map_nsmul, nsmul_eq_mul, mul_one]
  exact holomorphicFormOfConstant_ne_zero X d (.op W) (c := (n : ℂ)) (by exact_mod_cast hn)
    (key.trans hW)

/-- Non-torsion form of upstream's unit. -/
theorem nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [Nonempty (ComplexPoint X)]
    {n : ℕ} (hn : n ≠ 0) :
    n • fieldToHolomorphicDeRhamComplexInt K X ≠ 0 := by
  intro h
  have hg : constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (holomorphicDeRhamComplex X (dim X.left)).d 0 1 = 0 := by
    rw [holomorphicDeRhamComplex_d]
    exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential X _
  have hR := single_map_comp_extendSingleIso_inv_comp (C := AnalyticAdditiveSheaf X)
    (𝟙 _) (fieldToComplexConstantSheaf K X) (L := holomorphicDeRhamComplex X (dim X.left))
    (constantsToHolomorphicDeRhamZeroSheaf X _) hg
  have hR' := (congrArg (fun φ : (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj 𝓒(↧(ComplexPoint X); K) ⟶
        (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat =>
      (n • φ : _ ⟶ _)) hR).symm.trans (show _ = 0 by
    change n • (_ ≫ _ ≫ fieldToHolomorphicDeRhamComplexInt K X) = 0
    rw [← Preadditive.comp_nsmul, ← Preadditive.comp_nsmul, h, comp_zero, comp_zero])
  have h0 := congrArg (fun f : (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj 𝓒(↧(ComplexPoint X); K) ⟶
        (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat =>
      f.f 0 ≫ ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom) hR'
  simp only [HomologicalComplex.nsmul_f_apply, Preadditive.nsmul_comp] at h0
  rw [homFromSingleExtend_f_zero, HomologicalComplex.zero_f, zero_comp, Category.id_comp,
    ← Preadditive.comp_nsmul] at h0
  have hfg :
      n • (fieldToComplexConstantSheaf K X ≫ constantsToHolomorphicDeRhamZeroSheaf X _) = 0 :=
    (cancel_epi _).1 (h0.trans comp_zero.symm)
  exact nsmul_fieldToHolomorphicFormZeroSheaf_ne_zero K X _ hn hfg

/-- **Sign separation.** Upstream's unit is not its own negative. -/
theorem fieldToHolomorphicDeRhamComplexInt_ne_neg (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [Nonempty (ComplexPoint X)] :
    fieldToHolomorphicDeRhamComplexInt ℚ X ≠ -fieldToHolomorphicDeRhamComplexInt ℚ X := by
  intro h
  apply nsmul_fieldToHolomorphicDeRhamComplexInt_ne_zero ℚ X (n := 2) two_ne_zero
  rw [two_nsmul]; nth_rw 2 [h]; exact add_neg_cancel _

/-- **Sign separation for the rational unit**: `forget_rationalDeRhamUnit` is false for
`−rationalDeRhamUnit X`. -/
theorem rationalDeRhamUnit_ne_neg (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [Nonempty (ComplexPoint X)] : rationalDeRhamUnit X ≠ -rationalDeRhamUnit X := by
  have : (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).Additive :=
    Cup.forgetSheaf_additive _
  have : (forgetComplex X).Additive := instAdditiveHomologicalComplexMapHomologicalComplex _ _
  intro hu
  have h := forget_rationalDeRhamUnit X
  have h' : (forgetComplex X).map (-rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ (-fieldToHolomorphicDeRhamComplexInt ℚ X) := by
    rw [Functor.map_neg, Preadditive.neg_comp, h, Preadditive.comp_neg]
  rw [← hu, h] at h'
  exact fieldToHolomorphicDeRhamComplexInt_ne_neg X ((cancel_epi _).1 h')

end HodgeLadder.Tests
