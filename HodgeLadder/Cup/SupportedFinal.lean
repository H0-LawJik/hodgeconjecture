module

public import HodgeLadder.Cup.SupportedRelCup
public import HodgeLadder.Cup.SupportedNamed
public import HodgeLadder.Cup.SupportedClass
public import HodgeLadder.Cup.CupSingular

/-!
# The supported cup product against the relative singular cup product

Rung `cup-singular-comparison` (front `cup`, supported case). Let `Φ` be the supported
comparison: upstream's flasque supported-sections model of `H_[Z]^n(X; ℚ)` for the singular
cochain sheaves (`relHAddEquivSupportedSectionsHomologyOfFlasque`), followed by upstream's
`supportedRationalSingularSectionCohomologyEquivRelative` at `V = ⊤`, `U = X ∖ Z`, landing in
`H^n(⊤, ⊤ ⊓ (X ∖ Z); ℚ)`. Then `Φ (α ∪ β) = (−1)^{pq} · relCupSing (Φ α) (Ψ β)`, with `Ψ` upstream's
sheaf–singular equivalence and `Ψ β` read on the open `⊤`. The sign is the one of the absolute case
(`cup-singular-comparison-absolute`): it comes from `rightMulCochain`, and no sign enters through the
supported models. Conventions: `docs/conventions.md`, rows "Cup product" and "Supported comparison Φ".

## Main results

* `HodgeLadder.Cup.cup_singular_comparison_supported`
* `HodgeLadder.Cup.supportedSection_eq_pairEval`, `HodgeLadder.Cup.exists_cls`,
  `HodgeLadder.Cup.cls_zsmul`, `HodgeLadder.Cup.exists_supported_rep`,
  `HodgeLadder.Cup.supCup_flasque_chosen`, `HodgeLadder.Cup.globalSections_of_singClass`,
  `HodgeLadder.Cup.topOpen_singClass`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite AlgebraicTopology.Singular
  TopCat.Sheaf CochainComplex.HomComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder.Cup

variable {Y : TopCat.{0}} (U V W : Opens Y) (hW : V ⊓ U = W)

set_option backward.isDefEq.respectTransparency false in
/-- **The supported section named by a cochain, as a section of `S`, is its evaluation at the
generator.** -/
lemma supportedSection_eq_pairEval {k : ℕ} {n : ℤ} (hk : (k : ℤ) = n)
    (c : Cochain ((CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
      (pairSheaf' Y U V W hW)) (sInt Y) n) :
    (sInt_XIso hk).hom.hom.app (op V) ((supSeq Y U V).f.f n
        ((homComplexPairSheafIsoSupportedSections Y U V W hW (sInt Y)).hom.f n c)) =
      pairEval U V W hW hk c := by
  unfold pairEval
  congr 1
  have e := ConcreteCategory.congr_hom
    (pairSheafHomIsoSupportedSections_hom_inclusion Y U V W hW ((sInt Y).X n))
    (Cochain.fromSingleEquiv (zero_add n) c)
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- `supportedSection_eq_pairEval` for a cochain out of the pair sheaf in the site spelling. -/
lemma supportedSection_eq_pairEval' {k : ℕ} {n : ℤ} (hk : (k : ℤ) = n)
    (c : Cochain ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat) 0).obj (pairSheaf' Y U V W hW)) (sInt Y) n) :
    (sInt_XIso hk).hom.hom.app (op V) ((supSeq Y U V).f.f n
        ((homComplexPairSheafIsoSupportedSections Y U V W hW (sInt Y)).hom.f n c)) =
      pairEval U V W hW hk c :=
  supportedSection_eq_pairEval U V W hW hk c

set_option backward.isDefEq.respectTransparency false in
/-- `pairSheafEvaluation_cocycleComp_rightMul` for a cocycle in the site spelling. -/
lemma pairSheafEvaluation_cocycleComp_rightMul' {p q : ℕ}
    (z : Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat) 0).obj (pairSheaf' Y U V W hW)) (sInt Y) p)
    (b : OpenCochains ℚ Y (op ⊤) q) (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    pairEval U V W hW (k := p + q) (by push_cast; rfl)
        (cocycleComp z (rightMulCocycle b hb)
          (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)).1 =
      (((p : ℤ) * q).negOnePow : ℤ) •
        (rightMulSheaf b p (p + q) rfl).hom.app (op V) (pairEval U V W hW rfl z.1) :=
  pairSheafEvaluation_cocycleComp_rightMul U V W hW z b hb

/-- Every class of a complex of abelian groups is the class of a cocycle. -/
lemma exists_cls {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat.{0} c)
    (i j : ι) (hj : c.next i = j) (u : K.homology i) :
    ∃ (x : K.X i) (hx : K.d i j x = 0), u = cls K i j hj x hx := by
  obtain ⟨v, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance u
  refine ⟨K.iCycles i v, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, K.iCycles_d, AddCommGrpCat.zero_apply]
  · unfold cls
    congr 1
    apply cycles_ext
    rw [iCycles_cyc]

/-- The class of a multiple is the multiple of the class. -/
lemma cls_zsmul {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat.{0} c)
    {i j : ι} (hj : c.next i = j) (m : ℤ) (x : K.X i) (hx : K.d i j x = 0)
    (hmx : K.d i j (m • x) = 0) : cls K i j hj (m • x) hmx = m • cls K i j hj x hx := by
  unfold cls
  rw [← map_zsmul]
  congr 1
  apply cycles_ext
  rw [map_zsmul, iCycles_cyc, iCycles_cyc]

section Variety

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (Z : Closeds (ComplexPoint X))

local instance finHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance finSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  finHasDerivedCategory X

/-- Upstream's flasque supported-sections model of `H_[Z]^n(X; ℚ)` for the singular cochain
sheaves. -/
abbrev flasqueModel (n : ℕ) :=
  relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint X))
    𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X) Z.compl ⊤ Z.compl
    (top_inf_eq _) (singularCochainSheafComplexInt_isFlasque X) n

/-- The Hom-complex cocycle out of the pair sheaf named by a supported cocycle. -/
def supCocycle {p : ℕ} (s : (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.X (p : ℤ))
    (hs : (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) s = 0) :
    Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
      (singularCochainSheafComplexInt X ℚ) p :=
  Cocycle.mk ((homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) (singularCochainSheafComplexInt X ℚ)).inv.f p s) ((p : ℤ) + 1) rfl (by
      have := map_d_eq_zero (homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X))
        Z.compl ⊤ Z.compl (top_inf_eq _) (singularCochainSheafComplexInt X ℚ)).inv s hs
      exact this)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Every supported class has a relative-cocycle representative**, and the Hom-complex cocycle
of that representative names the class in the derived category. -/
theorem exists_supported_rep {p : ℕ} (α : H_[Z]^p(X; ℚ)) :
    ∃ (x : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.X (p : ℤ))
      (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0),
      flasqueModel X Z p α =
        cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp)
          ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x) (map_d_eq_zero _ x hx) ∧
      α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
        ShiftedHom.map (Cocycle.equivHomShift.symm (supCocycle X Z
          ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x) (map_d_eq_zero _ x hx)))
          DerivedCategory.Q := by
  obtain ⟨y, hy⟩ := (homologyMap_rawMap_bijective (TopCat.of (ComplexPoint X)) Z.compl ⊤ p).2
    (flasqueModel X Z p α)
  obtain ⟨x, hx, rfl⟩ := exists_cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y
  rw [homologyMap_cls] at hy
  refine ⟨x, hx, hy.symm, ?_⟩
  set s₀ := (rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x
  set z := supCocycle X Z s₀ (map_d_eq_zero _ x hx)
  set xz : H_[Z]^p(X; ℚ) := Abelian.Ext.homAddEquiv.symm
    (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q ≫
      inv ((DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧'))
  have hxz : xz.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
    rw [← Abelian.Ext.homAddEquiv_apply, AddEquiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  have hFxz := relHSupportedOfFlasque_mk (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) 𝓒(↧(ComplexPoint X); ℚ) (singularCochainSheafComplexInt X ℚ) (iotaQ X)
    (singularCochainSheafComplexInt_isFlasque X) p xz z hxz
  set e := homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) (singularCochainSheafComplexInt X ℚ)
  have hcls : HomologicalComplex.homologyMap e.hom p
      ((homologyAddEquiv _ _ p).symm (CohomologyClass.mk z)) =
      cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
        (map_d_eq_zero _ x hx) := by
    rw [← homologyAddEquiv_cls z, AddEquiv.symm_apply_apply, homologyMap_cls]
    apply cls_eq
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ)) e.inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  have hαx : flasqueModel X Z p α = flasqueModel X Z p xz := by
    rw [← hy]
    exact (hFxz.trans hcls).symm
  rw [(flasqueModel X Z p).injective hαx]
  exact hxz

set_option maxHeartbeats 2000000 in
/-- `supported-sections-class` at upstream's chosen resolution. -/
lemma supCup_flasque_chosen {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ))
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0)
    (hβ : rationalSingularCochainHypercohomologyAddEquivGlobalSections X q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      namedClass X ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))))
    (z : Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
      (singularCochainSheafComplexInt X ℚ) p)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q)
    (n : ℕ) (h : p + q = n) :
    flasqueModel X Z n (supCup α β n h) =
      HomologicalComplex.homologyMap (homComplexPairSheafIsoSupportedSections
          (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
          (singularCochainSheafComplexInt X ℚ)).hom n
        ((homologyAddEquiv _ _ n).symm
          (CohomologyClass.mk (cocycleComp z (rightMulCocycle b hb) (by omega)))) := by
  unfold rationalSingularCochainHypercohomologyAddEquivGlobalSections at hβ
  dsimp only at hβ
  refine @supCup_supportedSections X _ _ _ _ _ ?_ _ ?_ ?_ Z p q α β b hb hβ z hα n h
  all_goals
    letI : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
      dsimp [singularCochainSheafComplexInt]
      infer_instance
  · haveI := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose
    haveI := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose_spec
    exact CochainComplex.isKInjective_of_injective _ 0
  · exact (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose
  · haveI := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose
    haveI := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose_spec.choose_spec
    haveI := (CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (singularCochainSheafComplexInt X ℚ) 0).choose_spec.choose_spec.choose
    exact TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      _ 0 0 (fun q => singularCochainSheafComplexInt_isFlasque X q) (fun _ => inferInstance)

/-- Step 1 and step 2 of upstream's `Ψ` on a class whose singular class is that of a global
cocycle. -/
lemma globalSections_of_singClass {q : ℕ} (β : H^q(X; ℚ))
    (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0)
    (h : rationalCohomologyAddEquivSingularCohomology X q β = singClass b hb) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSections X q
        (rationalCohomologySingularCochainAddEquiv X q β) =
      namedClass X ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X)))) := by
  have hΨ : rationalCohomologyAddEquivSingularCohomology X q β =
      rationalSingularCochainHypercohomologyAddEquivCohomology X q
        (rationalCohomologySingularCochainAddEquiv X q β) := rfl
  rw [hΨ, ← step3_named_class X b hb] at h
  rw [(rationalSingularCochainHypercohomologyAddEquivCohomology X q).injective h]
  exact globalSections_mk X q _

/-- The class of `b` on the open `⊤` is the singular class of `b`, read on `⊤`. -/
lemma topOpen_singClass {q : ℕ} (b : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) q)
    (hb : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) q).app (op ⊤) b = 0) :
    HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
        (TopCat.of (ComplexPoint X))).hom q (singClass b hb) =
      (TopOpenSingularChainComplex ℚ (TopCat.of (ComplexPoint X))).linearDualCochainComplex.homologyπ q
        ((TopOpenSingularChainComplex ℚ (TopCat.of (ComplexPoint X))).linearDualCochainComplex.cyclesMk
          b (q + 1) (by simp) hb) := by
  rw [singClass_eq, singClassM, ← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    Iso.inv_hom_id, HomologicalComplex.homologyMap_id]
  rfl

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The supported cup product against the relative singular cup product.** Let `Φ` be the
supported comparison used here, a composite of two upstream equivalences: upstream's flasque supported-sections model followed by
`supportedRationalSingularSectionCohomologyEquivRelative` at `V = ⊤`, `U = X ∖ Z`. Then
`Φ (α ∪ β) = (−1)^{pq} · relCupSing (Φ α) (Ψ β)`, with `Ψ β` read on the open `⊤`. -/
theorem cup_singular_comparison_supported {p q : ℕ} (α : H_[Z]^p(X; ℚ)) (β : H^q(X; ℚ)) :
    supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (p + q) (flasqueModel X Z (p + q) (supCup α β (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
          p (flasqueModel X Z p α))
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
          (TopCat.of (ComplexPoint X))).hom q (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl := by
  obtain ⟨b, hb, hβb⟩ := exists_singClass (rationalCohomologyAddEquivSingularCohomology X q β)
  have hβ := globalSections_of_singClass X β b hb hβb.symm
  obtain ⟨x, hx, hFα, hα⟩ := exists_supported_rep X Z α
  set s₀ := (rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x
  set z := supCocycle X Z s₀ (map_d_eq_zero _ x hx)
  have hsup := supCup_flasque_chosen X Z α β b hb hβ z hα (p + q) rfl
  set e := homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) (singularCochainSheafComplexInt X ℚ)
  set w := cocycleComp z (rightMulCocycle b hb) (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; rfl)
  set s' := e.hom.f ((p + q : ℕ) : ℤ) w.1
  have hs'd : (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) s' = 0 :=
    map_d_eq_zero e.hom w.1 (Cocycle.δ_eq_zero w _)
  have hcls' : HomologicalComplex.homologyMap e.hom ((p + q : ℕ) : ℤ)
      ((homologyAddEquiv _ _ _).symm (CohomologyClass.mk w)) =
      cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ ((p + q : ℕ) : ℤ)
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
      (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ))).hom.hom.app (op ⊤)
        ((supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f _ s') =
      u • (rightMulSheaf b p (p + q) rfl).hom.app (op ⊤)
        ((sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom.hom.app (op ⊤)
          ((supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f p s₀)) := by
    have h1 := supportedSection_eq_pairEval' (Y := TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
      (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ)) w.1
    have h2 := supportedSection_eq_pairEval' (Y := TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) (rfl : (p : ℤ) = p) z.1
    have h3 := pairSheafEvaluation_cocycleComp_rightMul' (Y := TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) z b hb
    rw [← hes]
    exact h1.trans (h3.trans (by rw [← h2]; rfl))
  obtain ⟨s'', hs''⟩ : ∃ t, t = u • s' := ⟨_, rfl⟩
  have hs''d : (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) s'' = 0 := by
    rw [hs'', map_zsmul, hs'd, smul_zero]
  have hsec'' : (sInt_XIso (X := TopCat.of (ComplexPoint X))
      (rfl : ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ))).hom.hom.app (op ⊤)
        ((supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f _ s'') =
      (rightMulSheaf b p (p + q) rfl).hom.app (op ⊤)
        ((sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom.hom.app (op ⊤)
          ((supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f p s₀)) := by
    rw [hs'', map_zsmul, map_zsmul]
    erw [hsec']
    rw [smul_smul, hu, one_smul]
  have hbV : (SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤).fst
      ).linearDualCochainComplex.d q (q + 1) (resQ b (op ⊤)) = 0 := by
    rw [resQ_top]
    exact hb
  have hrel := supported_relative_cup (TopCat.of (ComplexPoint X)) Z.compl ⊤ x hx b hbV (p + q) rfl
    s'' hs''d hsec''
  have hss : s' = u • s'' := by
    rw [hs'', smul_smul, hu, one_smul]
  have hc : cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ ((p + q : ℕ) : ℤ)
      (((p + q : ℕ) : ℤ) + 1) (by simp) s' hs'd =
      u • cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ ((p + q : ℕ) : ℤ)
        (((p + q : ℕ) : ℤ) + 1) (by simp) s'' hs''d :=
    (cls_eq _ (by simp) hs'd (hss ▸ hs'd) hss).trans
      (cls_zsmul (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (by simp) u s'' hs''d _)
  refine (congrArg (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
    Z.compl ⊤ (p + q)) hc).trans ?_
  refine (map_zsmul (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
    Z.compl ⊤ (p + q)) u _).trans ?_
  have hA : supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X))
      Z.compl ⊤ p (flasqueModel X Z p α) =
      supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤ p
        (cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
          (map_d_eq_zero _ x hx)) := congrArg _ hFα
  have hB : HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
      (TopCat.of (ComplexPoint X))).hom q (rationalCohomologyAddEquivSingularCohomology X q β) =
      (SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤).fst
        ).linearDualCochainComplex.homologyπ q
        ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤).fst
          ).linearDualCochainComplex.cyclesMk (resQ b (op ⊤)) (q + 1) (by simp) hbV) := by
    rw [← hβb, topOpen_singClass]
    congr 2
    exact (resQ_top b).symm
  have hR : relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)
      (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤ p
        (cls (supSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ (p : ℤ) ((p : ℤ) + 1) (by simp) s₀
          (map_d_eq_zero _ x hx)))
      ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤).fst
        ).linearDualCochainComplex.homologyπ q
        ((SingularChainComplex ℚ (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤).fst
          ).linearDualCochainComplex.cyclesMk (resQ b (op ⊤)) (q + 1) (by simp) hbV)) (p + q) rfl =
      relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤)
        (supportedRationalSingularSectionCohomologyEquivRelative (TopCat.of (ComplexPoint X)) Z.compl ⊤
          p (flasqueModel X Z p α))
        (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ
          (TopCat.of (ComplexPoint X))).hom q (rationalCohomologyAddEquivSingularCohomology X q β))
        (p + q) rfl :=
    congrArg₂ (fun a c => relCupSing (pairVU (TopCat.of (ComplexPoint X)) Z.compl ⊤) a c (p + q) rfl)
      hA.symm hB.symm
  exact congrArg (u • ·) (hrel.trans hR)

end Variety

end HodgeLadder.Cup
