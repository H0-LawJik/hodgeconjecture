module

public import HodgeLadder.Cup.SupportedForget
public import HodgeLadder.Cup.ConstantGenerator
public import HodgeLadder.Cup.SupportedForgetGen

/-!
# Forgetting the support commutes with the supported comparison

Rung `supported-forget-compat` (front `cup`). Forgetting the support commutes with the supported
comparison `Φ` and upstream's absolute comparison `Ψ`, with no sign:
`forgetRel (Φ α) = Ψ (forgetSupport α)`, with `Ψ` read on the open `⊤`.

## Main results

* `HodgeLadder.Cup.supported_forget_compat`
* `HodgeLadder.Cup.fromSingleEquiv_precomp_single`, `HodgeLadder.Cup.cocycle_precomp_precomp`,
  `HodgeLadder.Cup.homologyMap_cyclesMk`, `HodgeLadder.Cup.forget_named_cocycle`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Localization AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
  AlgebraicTopology.Singular CochainComplex.HomComplex

namespace HodgeLadder.Cup

section General

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/-- Precomposing a cochain out of a single complex with the image of a map. -/
lemma fromSingleEquiv_precomp_single {A A' : C} {L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) L n) (g : A' ⟶ A) :
    Cochain.fromSingleEquiv (zero_add n) (z.precomp ((CochainComplex.singleFunctor C 0).map g)).1 =
      g ≫ Cochain.fromSingleEquiv (zero_add n) z.1 := by
  simp [Cochain.fromSingleEquiv, Cocycle.precomp]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  erw [HomologicalComplex.single_map_f_self]
  simp

/-- Precomposing a cocycle twice is precomposing with the composite. -/
lemma cocycle_precomp_precomp {K K' K'' L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n)
    (g : K' ⟶ K) (f : K'' ⟶ K') : (z.precomp g).precomp f = z.precomp (f ≫ g) := by
  apply Cocycle.ext
  simp [Cocycle.precomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end General

section ModuleCls

/-- A map of complexes on the class of `cyclesMk`. -/
lemma homologyMap_cyclesMk {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (k : ℕ)
    (y : K.X k) (hy : K.d k (k + 1) y = 0) (hy' : L.d k (k + 1) (φ.f k y) = 0) :
    HomologicalComplex.homologyMap φ k (K.homologyπ k (K.cyclesMk y (k + 1) (by simp) hy)) =
      L.homologyπ k (L.cyclesMk (φ.f k y) (k + 1) (by simp) hy') := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles k)).mp inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  have e1 := HomologicalComplex.i_cyclesMk K y (k + 1) (by simp) hy
  have e2 := HomologicalComplex.i_cyclesMk L (φ.f k y) (k + 1) (by simp) hy'
  erw [e1, e2]

/-- The class of `cyclesMk` depends only on the element. -/
lemma homologyπ_cyclesMk_congr {K : CochainComplex (ModuleCat.{0} ℚ) ℕ} {k : ℕ} {y y' : K.X k}
    (hy : K.d k (k + 1) y = 0) (hy' : K.d k (k + 1) y' = 0) (h : y = y') :
    K.homologyπ k (K.cyclesMk y (k + 1) (by simp) hy) =
      K.homologyπ k (K.cyclesMk y' (k + 1) (by simp) hy') := by
  subst h; rfl

end ModuleCls

section Variety

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

attribute [local instance] endHasDerivedCategory endSiteHasDerivedCategory endHasExt

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The cocycle of a supported representative, after forgetting the support, names the relative
cocycle read as a global cochain. -/
lemma forget_named_cocycle {n : ℕ} (x : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.X (n : ℤ))
    (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (n : ℤ) ((n : ℤ) + 1) x = 0)
    (c : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) n)
    (hcx : c = ((relativeDualCochainShortComplexNat ℚ
      (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)).X₂.extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        ((relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f n x)) :
    Cochain.fromSingleEquiv (zero_add (n : ℤ))
        ((supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f n x)
          (map_d_eq_zero _ x hx)).precomp ((CochainComplex.singleFunctor _ 0).map
            ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
              (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv ≫ forgetMap X Z))).1 =
      globalMap c := by
  rw [fromSingleEquiv_precomp_single]
  exact gen_forget_named_cocycle (TopCat.of (ComplexPoint X)) Z.compl x hx c hcx

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Forgetting the support commutes with the supported comparison**, with no sign:
`forgetRel (Φ α) = Ψ (forgetSupport α)`, with `Ψ` read on the open `⊤`. -/
theorem supported_forget_compat (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    forgetRel (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤) n
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
          Z.compl ⊤ n (flasqueModel X Z n α)) =
      HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
          (TopCat.of (ComplexPoint X))).hom n
        (rationalCohomologyAddEquivSingularCohomology X n (forgetSupport ℚ X Z n α)) := by
  obtain ⟨x, hx, hFα, hα⟩ := exists_supported_rep X Z α
  have hf := forgetSupport_named X Z α _ hα
  have h1 := step1_of_hom X (forgetSupport ℚ X Z n α) _ hf
  set K := (relativeDualCochainShortComplexNat ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)).X₂
  set c : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) n :=
    (K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
      ((relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f n x)
  have hc : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) n).app (op ⊤) c = 0 :=
    (extend_d_zero_iff K n _).mp (map_d_eq_zero (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f x hx)
  have hw : (((supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f n x)
      (map_d_eq_zero _ x hx)).precomp ((CochainComplex.singleFunctor _ 0).map (forgetMap X Z))).precomp
        (constantIntegerSheafComplexIntIsoSingleULift X).hom) =
      ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))).precomp
        (constantIntegerSheafComplexIntIsoSingle X).hom := by
    have key : ((supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f n x)
        (map_d_eq_zero _ x hx)).precomp ((CochainComplex.singleFunctor _ 0).map
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
            (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv ≫ forgetMap X Z))) =
        (rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X))) := by
      apply Cocycle.ext
      apply (Cochain.fromSingleEquiv (zero_add (n : ℤ))).injective
      exact (forget_named_cocycle X Z x hx c rfl).trans (fromSingleEquiv_rightMul_precomp c hc).symm
    rw [← key, cocycle_precomp_precomp, cocycle_precomp_precomp]
    congr 1
    have hU : (constantIntegerSheafComplexIntIsoSingleULift X).hom =
        (constantIntegerSheafComplexIntIsoSingle X).hom ≫
          (CochainComplex.singleFunctor (CategoryTheory.Sheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).map
            ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
              (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso.inv) := rfl
    rw [hU, Category.assoc, ← Functor.map_comp]
  have hΨ : rationalCohomologyAddEquivSingularCohomology X n (forgetSupport ℚ X Z n α) =
      singClass c hc := by
    change rationalSingularCochainHypercohomologyAddEquivCohomology X n
      (rationalCohomologySingularCochainAddEquiv X n (forgetSupport ℚ X Z n α)) = _
    rw [h1, hw]
    exact step3_named_class X c hc
  rw [hΨ, topOpen_singClass, hFα, ← homologyMap_cls (rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁
    (n : ℤ) ((n : ℤ) + 1) (by simp) x hx, supported_singular_class]
  have hx₀ := (extend_d_zero_iff (RelativeCochainComplex ℚ (pairVU (TopCat.of (ComplexPoint X))
    Z.compl ⊤)) n x).mp hx
  rw [relDualEquiv_cls (TopCat.of (ComplexPoint X)) Z.compl ⊤ n x hx hx₀]
  have hcf := relSeq_f_apply (TopCat.of (ComplexPoint X)) Z.compl ⊤ n x
  have hc' : (HomologicalComplex.linearDualMap (relativeChainProjection ℚ
      (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤))).f n
      (((RelativeCochainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom x) = c :=
    hcf.symm
  exact (homologyMap_cyclesMk _ n _ hx₀ (hc' ▸ hc)).trans (homologyπ_cyclesMk_congr _ _ hc')

end Variety

end HodgeLadder.Cup
