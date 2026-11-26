module

public import HodgeLadder.Cup.RightMultUnit
public import HodgeLadder.Cup.ExtRightMult

/-!
# Right multiplication by `b` composed with the resolution names `b`

Rung `ext-class-right-mult` (front `cup`, sub-rung 4 of `cup-singular-comparison`). Let
`ι_ℤ : ℤ_Y[0] ⟶ S_ℤ` be the chain map whose degree-zero component is `ℤ_Y → ℚ_Y → S⁰`
(upstream's constant-cochain map). For a global `q`-cocycle `b`, the Hom-complex cocycle
`R_b ∘ ι_ℤ` is the degree-`q` cocycle from `ℤ_Y[0]` that sends the section `1` to `b`. In the
derived category, `ι_ℤ` followed by the class of `R_b` is the class of that cocycle.

## Main definitions

* `HodgeLadder.Cup.intToRat`, `HodgeLadder.Cup.iotaZ`, `HodgeLadder.Cup.globalMap`

## Main results

* `HodgeLadder.Cup.evalOne_intToRat`, `HodgeLadder.Cup.fromSingleEquiv_rightMul_precomp`,
  `HodgeLadder.Cup.toSmallShiftedHom_rightMul_precomp`, `HodgeLadder.Cup.globalSections_rightMul_iota`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular CochainComplex
  HomComplex TopCat.Sheaf

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}}

variable (Y) in
/-- The map `ℤ_Y → ℚ_Y` of constant sheaves. -/
def intToRat : 𝓒(Y; ℤ) ⟶ 𝓒(Y; ℚ) :=
  (constantFunctor Y).map (AddCommGrpCat.ofHom (Int.castAddHom ℚ))

/-- Evaluated at `1`, the map `ℤ_Y → ℚ_Y` is the sheafified constant `1`. -/
lemma evalOne_intToRat :
    integerConstantHomAddEquivGlobalSections 𝓒(Y; ℚ) (intToRat Y) =
      (toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ(Y; ℚ)).app (op ⊤) (1 : ℚ) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
    Limits.isTerminalTop
  have h1 : adj.homEquiv _ _ (intToRat Y) =
      AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫ adj.unit.app (AddCommGrpCat.of ℚ) := by
    rw [intToRat, ← Category.comp_id ((constantFunctor Y).map _),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  change ConcreteCategory.hom (adj.homEquiv _ _ (intToRat Y)) (1 : ℤ) = _
  rw [h1, ConcreteCategory.comp_apply]
  simp only [adj, constantSheafAdj, Adjunction.comp_unit_app]
  erw [ConcreteCategory.comp_apply]

variable (Y) in
/-- `ι_ℤ : ℤ_Y[0] ⟶ S_ℤ`, with degree-zero component `ℤ_Y → ℚ_Y → S⁰`. -/
def iotaZ : integerConstantSingleComplex Y ⟶ sInt Y :=
  HomologicalComplex.mkHomFromSingle
    (intToRat Y ≫ constantsToSingularCochainZeroSheaf ℚ Y ≫ (sInt_XIso (k := 0) rfl).inv)
    (fun k hk => by
      obtain rfl : k = 1 := by simpa using hk.symm
      rw [sInt_d (k := 0) (p := 0) (p' := 1) (by norm_num) (by norm_num), Category.assoc, Category.assoc,
        Iso.inv_hom_id_assoc, ← Category.assoc (constantsToSingularCochainZeroSheaf ℚ Y),
        constantsToSingularCochainZeroSheaf_comp_coboundary, Limits.zero_comp,
        Limits.comp_zero])

/-- The map `ℤ_Y ⟶ S^q` sending `1` to the sheafified global cochain `b`. -/
def globalMap {q : ℕ} (b : OpenCochains ℚ Y (op ⊤) q) :
    𝓒(Y; ℤ) ⟶ (sInt Y).X q :=
  (integerConstantHomAddEquivGlobalSections (singularCochainSheaf ℚ Y q)).symm
      ((toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y q)).app (op ⊤) b) ≫
    (sInt_XIso rfl).inv

/-- **`R_b ∘ ι_ℤ` is the cocycle naming `b`**: its component out of `ℤ_Y` is `globalMap b`. -/
theorem fromSingleEquiv_rightMul_precomp {q : ℕ} (b : OpenCochains ℚ Y (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    Cochain.fromSingleEquiv (zero_add (q : ℤ))
        ((rightMulCocycle b hb).precomp (iotaZ Y)).1 = globalMap b := by
  simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cocycle.precomp,
    Cocycle.mk, rightMulCocycle]
  erw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rw [iotaZ, HomologicalComplex.mkHomFromSingle_f,
    rightMulCochain_v b 0 q 0 q rfl rfl (zero_add q) (zero_add _)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, zero_mul, Int.negOnePow_zero, Units.val_one,
    one_smul]
  rw [globalMap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply (integerConstantHomAddEquivGlobalSections (singularCochainSheaf ℚ Y q)).injective
  erw [AddEquiv.apply_symm_apply]
  rw [Category.assoc]
  erw [integerConstantHomAddEquivGlobalSections_naturality]
  rw [evalOne_intToRat, constantsToZeroSheaf_rightMulSheaf]
  exact constTimes_sheafify_one b

section Variety

open AlgebraicGeometry ComplexPoint Localization

variable (X : Over (Spec ↧ℂ))

/-- **In the derived category, `ι_ℤ` followed by the class of `R_b` is the class of the cocycle
naming `b`.** -/
theorem toSmallShiftedHom_rightMul_precomp {q : ℕ}
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0) :
    (CohomologyClass.mk ((rightMulCocycle b hb).precomp
        (iotaZ (TopCat.of (ComplexPoint X))))).toSmallShiftedHom.{1} =
      (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl (iotaZ (TopCat.of (ComplexPoint X)))).comp
        (CohomologyClass.mk (rightMulCocycle b hb)).toSmallShiftedHom.{1} (add_zero _) :=
  toSmallShiftedHom_precomp _ _

set_option maxHeartbeats 800000 in
/-- **`R_b ∘ ι` represents `[b]` under upstream's step 2**, for every K-injective resolution:
step 2 sends the derived-category class of `R_b ∘ ι_ℤ`, pulled back to upstream's integer
constant complex, to the homology class of the global section that `R_b ∘ ι_ℤ` names, which is
`b` by `fromSingleEquiv_rightMul_precomp`. -/
theorem globalSections_rightMul_iota
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    {q : ℕ} (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i q
        ((SmallShiftedHom.mk₀ _ (0 : ℤ) rfl (constantIntegerSheafComplexIntIsoSingle X).hom).comp
          ((SmallShiftedHom.mk₀ _ (0 : ℤ) rfl (iotaZ (TopCat.of (ComplexPoint X)))).comp
            (CohomologyClass.mk (rightMulCocycle b hb)).toSmallShiftedHom (add_zero _))
          (add_zero _)) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          (singularCochainSheafComplexInt X ℚ)).hom q
        ((homologyAddEquiv _ _ q).symm (CohomologyClass.mk
          ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))))) := by
  have h := globalSectionsOfResolution_mk X I i q
    ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X))))
  erw [toSmallShiftedHom_precomp, toSmallShiftedHom_precomp] at h
  exact h

end Variety

end HodgeLadder.Cup
