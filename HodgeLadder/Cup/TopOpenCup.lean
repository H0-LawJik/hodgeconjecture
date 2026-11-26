module

public import HodgeLadder.Cup.Step3
public import HodgeLadder.Cup.SingularCup

/-!
# The cup product on the open `⊤` against the singular cup product

Rung `cup-top-open` (front `cup`, part of `cup-step3`). The singular class of a global cocycle
(`singClass`, through upstream's raw identification) is the Tau Ceti class of the cocycle on the
space `⊤` pulled back along `X ≅ ⊤`; with Tau Ceti's naturality of the cup product this gives
`cupSing (singClass a) (singClass b) = singClass (cupGlobal a b)`.

## Main results

* `HodgeLadder.Cup.homologyπ_mapHomologyIso_hom`, `HodgeLadder.Cup.singClass_eq`,
  `HodgeLadder.Cup.cohIso_singClassM`, `HodgeLadder.Cup.tcTop_cupGlobal`,
  `HodgeLadder.Cup.cupSing_singClass`
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HodgeLadder.Cup

section MapHomology

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [S.HasHomology]
  [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S]

set_option backward.isDefEq.respectTransparency false in
/-- **`mapHomologyIso` on classes**: it sends the class of a cycle of `S.map F` to `F` of the class
of the corresponding cycle of `S`. -/
lemma homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let hl := S.leftHomologyData
  have key : hl.π ≫ hl.homologyIso.inv = hl.cyclesIso.inv ≫ S.homologyπ := by
    rw [← cancel_epi hl.cyclesIso.hom, Iso.hom_inv_id_assoc, ← Category.assoc,
      ← hl.homologyπ_comp_homologyIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 := (hl.map F).homologyπ_comp_homologyIso_hom
  have h1 : (S.mapHomologyIso F).hom =
      (hl.map F).homologyIso.hom ≫ F.map hl.homologyIso.inv :=
    congrArg Iso.hom (hl.mapHomologyIso_eq F)
  have h2 : (S.mapCyclesIso F).hom = (hl.map F).cyclesIso.hom ≫ F.map hl.cyclesIso.inv :=
    congrArg Iso.hom (hl.mapCyclesIso_eq F)
  rw [h1, h2, (hl.map F).homologyπ_comp_homologyIso_hom_assoc, Category.assoc]
  congr 1
  rw [← F.map_comp, ← key, F.map_comp]
  rfl

end MapHomology

section SingClass

open TopologicalSpace Opposite AlgebraicTopology.Singular MonoidalCategory

variable {Y : TopCat.{0}}

/-- The singular class of a global cocycle, from the `ℚ`-module cochain complex of the open `⊤`
transported along upstream's `singularCochainComplexIsoTopOpen`. -/
def singClassM {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) : Cohomology ℚ Y n :=
  HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).inv n
    ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.homologyπ n
      ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (n + 1) (by simp)
        hc))

set_option backward.isDefEq.respectTransparency false in
/-- **The two descriptions of the singular class agree.** -/
lemma singClass_eq {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) :
    singClass c hc = singClassM c hc := by
  rw [singClass, AddEquiv.symm_apply_eq]
  unfold ordinarySingularCohomologyEquivGlobalRaw
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  set Kd := (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
  set w := Kd.cyclesMk c (n + 1) (by simp) hc
  -- undo the transport along `singularCochainComplexIsoTopOpen`
  have h1 : ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapIso (HomologicalComplex.homologyMapIso
      (singularCochainComplexIsoTopOpen ℚ Y) n)).addCommGroupIsoToAddEquiv (singClassM c hc) =
      Kd.homologyπ n w := by
    change HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).hom n
      (HomologicalComplex.homologyMap (singularCochainComplexIsoTopOpen ℚ Y).inv n
        (Kd.homologyπ n w)) = _
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
      HomologicalComplex.homologyMap_id]
    rfl
  erw [h1]
  -- the forgetful functor
  have hcF : (topOpenForgottenSingularCochainComplex ℚ Y).d n (n + 1) c = 0 := hc
  have hq : (topOpenForgottenSingularCochainHomologyIso ℚ Y n).hom
      (cls (topOpenForgottenSingularCochainComplex ℚ Y) n (n + 1) (by simp) c hcF) =
      Kd.homologyπ n w := by
    have key := ConcreteCategory.congr_hom
      (homologyπ_mapHomologyIso_hom (forget₂ (ModuleCat ℚ) AddCommGrpCat) (Kd.sc n))
      (cyc (topOpenForgottenSingularCochainComplex ℚ Y) n (n + 1) (by simp) c hcF)
    refine key.trans ?_
    change (Kd.sc n).homologyπ _ = (Kd.sc n).homologyπ w
    congr 1
    apply (ModuleCat.mono_iff_injective ((Kd.sc n).iCycles)).mp inferInstance
    have e3 := ConcreteCategory.congr_hom
      (ShortComplex.mapCyclesIso_hom_iCycles (Kd.sc n) (forget₂ (ModuleCat ℚ) AddCommGrpCat))
      (cyc (topOpenForgottenSingularCochainComplex ℚ Y) n (n + 1) (by simp) c hcF)
    refine e3.trans ?_
    exact (iCycles_cyc (topOpenForgottenSingularCochainComplex ℚ Y) n (n + 1) (by simp) c
      hcF).trans (Kd.i_cyclesMk c (n + 1) (by simp) hc).symm
  have hq' := congrArg (topOpenForgottenSingularCochainHomologyIso ℚ Y n).inv hq
  rw [Iso.hom_inv_id_apply] at hq'
  erw [← hq']
  exact (homologyMap_cls (globalRawSingularCochainComplexIso ℚ Y).inv n (n + 1) (by simp) c
    hcF).symm

/-- Upstream's transport along `X ≅ ⊤` is Tau Ceti's cochain map of `⊤ ⟶ X`'s inverse, through
`dualIsoYoneda`. -/
lemma isoTopOpen_inv_dualIsoYoneda :
    (singularCochainComplexIsoTopOpen ℚ Y).inv ≫ (dualIsoYoneda (SingularChainComplex ℚ Y)).hom =
      (dualIsoYoneda (TopOpenSingularChainComplex ℚ Y)).hom ≫
        TopCat.singularCochainComplexMap (R := 𝟙_ (ModuleCat.{0} ℚ)) (k := ℚ)
          (M := 𝟙_ (ModuleCat.{0} ℚ)) (Opens.inclusionTopIso Y).inv := by
  ext n φ
  rfl

/-- **The Tau Ceti class of a global cocycle on the space `⊤`.** -/
def tcTop {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) :
    tcCoh ((Opens.toTopCat Y).obj ⊤) n :=
  HomologicalComplex.homologyMap (dualIsoYoneda (TopOpenSingularChainComplex ℚ Y)).hom n
    ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.homologyπ n
      ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (n + 1) (by simp)
        hc))

set_option backward.isDefEq.respectTransparency false in
/-- **The singular class is the Tau Ceti class on `⊤` pulled back to `X`.** -/
lemma cohIso_singClassM {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) :
    (cohIso Y n).hom (singClassM c hc) =
      TopCat.singularCohomologyMap (Opens.inclusionTopIso Y).inv n (tcTop c hc) := by
  unfold cohIso singClassM tcTop
  rw [HomologicalComplex.homologyMapIso_hom]
  generalize (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.homologyπ n
    ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (n + 1) (by simp) hc) = x
  unfold TopCat.singularCohomologyMap
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (isoTopOpen_inv_dualIsoYoneda (Y := Y))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h x).trans rfl

lemma resQ_top {q : ℕ} (b : OpenCochains ℚ Y (op ⊤) q) : resQ b (op ⊤) = b := by
  change (singularCochainPresheaf ℚ Y q).map (𝟙 _) b = b
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma homologyMap_dualIsoYoneda_π {m : ℕ} (c : OpenCochains ℚ Y (op ⊤) m)
    (hc : (singularCochainCoboundary ℚ Y m).app (op ⊤) c = 0) :
    HomologicalComplex.homologyMap (dualIsoYoneda (TopOpenSingularChainComplex ℚ Y)).hom m
      ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.homologyπ m
        ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (m + 1) (by simp)
          hc)) =
      ((TopOpenSingularChainComplex ℚ Y).linearYonedaObj ℚ (ModuleCat.of ℚ ℚ)).homologyπ m
        (HomologicalComplex.cyclesMap (dualIsoYoneda (TopOpenSingularChainComplex ℚ Y)).hom m
          ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (m + 1) (by simp)
            hc)) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **On `⊤`, the Tau Ceti class of `a ∪ b` is the Tau Ceti cup of the classes.** -/
lemma tcTop_cupGlobal {p q : ℕ} (a : OpenCochains ℚ Y (op ⊤) p) (b : OpenCochains ℚ Y (op ⊤) q)
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    tcTop (cupGlobal a b) (cupGlobal_coboundary ha hb) =
      tcCup ((Opens.toTopCat Y).obj ⊤) p q (p + q) rfl (tcTop a ha) (tcTop b hb) := by
  unfold tcTop
  rw [homologyMap_dualIsoYoneda_π, homologyMap_dualIsoYoneda_π, homologyMap_dualIsoYoneda_π]
  unfold tcCup
  erw [TopCat.singularCup_homologyπ]
  congr 1
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles _ _)).mp inferInstance
  erw [TauCeti.ChainComplex.iCycles_cupCycles]
  have hiC : ∀ {m : ℕ} (c : OpenCochains ℚ Y (op ⊤) m)
      (hc : (singularCochainCoboundary ℚ Y m).app (op ⊤) c = 0),
      ((TopOpenSingularChainComplex ℚ Y).linearYonedaObj ℚ (ModuleCat.of ℚ ℚ)).iCycles m
        (HomologicalComplex.cyclesMap (dualIsoYoneda (TopOpenSingularChainComplex ℚ Y)).hom m
          ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.cyclesMk c (m + 1) (by simp)
            hc)) = toHomQ Y c := by
    intro m c hc
    have e := HomologicalComplex.i_cyclesMk
      (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex c (m + 1) (by simp) hc
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
    erw [e]
    rfl
  erw [hiC, hiC, hiC]
  change toHomQ Y (toHomQ Y |>.symm _) = _
  rw [LinearEquiv.apply_symm_apply, resQ_top]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The singular cup product of the singular classes of `a` and `b` is the singular class of
`a ∪ b`.** -/
theorem cupSing_singClass {p q : ℕ} (a : OpenCochains ℚ Y (op ⊤) p)
    (b : OpenCochains ℚ Y (op ⊤) q)
    (ha : (singularCochainCoboundary ℚ Y p).app (op ⊤) a = 0)
    (hb : (singularCochainCoboundary ℚ Y q).app (op ⊤) b = 0) :
    cupSing Y (singClass a ha) (singClass b hb) (p + q) rfl =
      singClass (cupGlobal a b) (cupGlobal_coboundary ha hb) := by
  rw [singClass_eq, singClass_eq, singClass_eq]
  unfold cupSing
  rw [cohIso_singClassM, cohIso_singClassM]
  erw [TopCat.singularCup_naturality]
  rw [← tcTop_cupGlobal, ← cohIso_singClassM, Iso.hom_inv_id_apply]

end SingClass

end HodgeLadder.Cup
