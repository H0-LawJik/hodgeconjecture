module

public import HodgeLadder.Cup.CupGlobal

/-!
# Upstream's step 3 on the class named by a global cocycle

Rung `step3-named-class` (front `cup`, part of `cup-step3`). Upstream's step 3 goes from the
cohomology of the global sections of the singular cochain sheaves to singular cohomology, through
the raw cochains on the open `⊤` and their sheafification. It sends the class named by a global
cocycle `c` to the singular class of `c`, defined through upstream's
`ordinarySingularCohomologyEquivGlobalRaw`.

## Main results

* `HodgeLadder.Cup.cls`, `HodgeLadder.Cup.homologyMap_cls`, `HodgeLadder.Cup.homologyAddEquiv_cls`,
  `HodgeLadder.Cup.extendHomologyIso_cls`, `HodgeLadder.Cup.topOpenToGlobal_f`,
  `HodgeLadder.Cup.globalSectionsIso_named`, `HodgeLadder.Cup.extendXIso_globalSectionsIso`,
  `HodgeLadder.Cup.singClass`, `HodgeLadder.Cup.step3_named_class`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder.Cup

section Cls

variable {ι : Type*} {c : ComplexShape ι} (K L : HomologicalComplex AddCommGrpCat.{0} c)

/-- An element of `K.X i` as a map from `ℤ`. -/
def elemHom {i : ι} (x : K.X i) : AddCommGrpCat.of ℤ ⟶ K.X i :=
  AddCommGrpCat.ofHom (zmultiplesHom _ x)

lemma elemHom_d {i j : ι} (x : K.X i) (hx : K.d i j x = 0) : elemHom K x ≫ K.d i j = 0 := by
  ext
  simp [elemHom, hx]

/-- The cycle defined by a cycle element. -/
def cyc (i j : ι) (hj : c.next i = j) (x : K.X i) (hx : K.d i j x = 0) : K.cycles i :=
  K.liftCycles (elemHom K x) j hj (elemHom_d K x hx) (1 : ℤ)

lemma iCycles_cyc (i j : ι) (hj : c.next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (cyc K i j hj x hx) = x := by
  rw [cyc, ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp [elemHom]

/-- Cycles are determined by their image in the chains. -/
lemma cycles_ext {i : ι} {u v : K.cycles i} (h : K.iCycles i u = K.iCycles i v) : u = v :=
  (AddCommGrpCat.mono_iff_injective (K.iCycles i)).mp inferInstance h

/-- The homology class of a cycle of a complex of abelian groups. -/
def cls (i j : ι) (hj : c.next i = j) (x : K.X i) (hx : K.d i j x = 0) : K.homology i :=
  K.homologyπ i (cyc K i j hj x hx)

variable {K L} in
lemma map_d_eq_zero (φ : K ⟶ L) {i j : ι} (x : K.X i) (hx : K.d i j x = 0) :
    L.d i j (φ.f i x) = 0 := by
  rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply, hx, map_zero]

variable {K L} in
/-- **A map of complexes sends the class of `x` to the class of its image.** -/
lemma homologyMap_cls (φ : K ⟶ L) (i j : ι) (hj : c.next i = j) (x : K.X i)
    (hx : K.d i j x = 0) :
    HomologicalComplex.homologyMap φ i (cls K i j hj x hx) =
      cls L i j hj (φ.f i x) (map_d_eq_zero φ x hx) := by
  unfold cls
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  have hc : HomologicalComplex.cyclesMap φ i (cyc K i j hj x hx) =
      cyc L i j hj (φ.f i x) (map_d_eq_zero φ x hx) := by
    apply cycles_ext
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      iCycles_cyc, iCycles_cyc]
  rw [hc]

lemma cls_congr {i j : ι} (hj : c.next i = j) {x x' : K.X i} (hx : K.d i j x = 0) (h : x = x') :
    cls K i j hj x hx = cls K i j hj x' (h ▸ hx) := by
  subst h; rfl

lemma cls_eq {i j : ι} (hj : c.next i = j) {x x' : K.X i} (hx : K.d i j x = 0)
    (hx' : K.d i j x' = 0) (h : x = x') : cls K i j hj x hx = cls K i j hj x' hx' := by
  subst h; rfl

end Cls

section ExtendCls

variable (K : CochainComplex AddCommGrpCat.{0} ℕ)

/-- **`extendHomologyIso` sends the class of `x` to the class of its component.** -/
lemma extendHomologyIso_cls (n : ℕ) (x : (K.extend ComplexShape.embeddingUpNat).X (n : ℤ))
    (hx : (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n : ℤ) + 1) x = 0)
    (hx' : K.d n (n + 1)
      ((K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom x)
      = 0) :
    (K.extendHomologyIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        (cls (K.extend ComplexShape.embeddingUpNat) (n : ℤ) ((n : ℤ) + 1) (by simp) x hx) =
      cls K n (n + 1) (by simp) ((K.extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = n)).hom x) hx' := by
  unfold cls
  have e : (K.extendHomologyIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
      ((K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ)
        (cyc (K.extend ComplexShape.embeddingUpNat) (n : ℤ) ((n : ℤ) + 1) (by simp) x hx)) =
      K.homologyπ n ((K.extendCyclesIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        (cyc (K.extend ComplexShape.embeddingUpNat) (n : ℤ) ((n : ℤ) + 1) (by simp) x hx)) :=
    ConcreteCategory.congr_hom (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = n)) _
  rw [e]
  congr 1
  apply cycles_ext
  have e2 : K.iCycles n ((K.extendCyclesIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        (cyc (K.extend ComplexShape.embeddingUpNat) (n : ℤ) ((n : ℤ) + 1) (by simp) x hx)) =
      (K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
        ((K.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ)
          (cyc (K.extend ComplexShape.embeddingUpNat) (n : ℤ) ((n : ℤ) + 1) (by simp) x hx)) :=
    ConcreteCategory.congr_hom (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = n)) _
  rw [e2, iCycles_cyc, iCycles_cyc]

lemma extend_d_zero (n : ℕ) (x : (K.extend ComplexShape.embeddingUpNat).X (n : ℤ))
    (hx : (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) ((n : ℤ) + 1) x = 0) :
    K.d n (n + 1)
      ((K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom x)
      = 0 := by
  rw [HomologicalComplex.extend_d_eq K _ (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
    (show ComplexShape.embeddingUpNat.f (n + 1) = (n : ℤ) + 1 by simp)] at hx
  simp only [ConcreteCategory.comp_apply] at hx
  have := congrArg (K.extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f (n + 1) = (n : ℤ) + 1 by simp)).hom hx
  rw [Iso.inv_hom_id_apply, map_zero] at this
  exact this

end ExtendCls

section HomComplexCls

variable {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} {n : ℤ}

lemma cocycle_d (z : CochainComplex.HomComplex.Cocycle K L n) :
    (CochainComplex.HomComplex K L).d n (n + 1) z.1 = 0 :=
  CochainComplex.HomComplex.Cocycle.δ_eq_zero z (n + 1)

/-- **`homologyAddEquiv` sends the class of a cocycle to its cohomology class.** -/
lemma homologyAddEquiv_cls (z : CochainComplex.HomComplex.Cocycle K L n) :
    CochainComplex.HomComplex.homologyAddEquiv K L n
        (cls (CochainComplex.HomComplex K L) n (n + 1) (by simp) z.1
          (by simp [CochainComplex.HomComplex])) =
      CochainComplex.HomComplex.CohomologyClass.mk z := by
  set u := cyc (CochainComplex.HomComplex K L) n (n + 1) (by simp) z.1
    (by simp [CochainComplex.HomComplex]) with hu
  have e : ((CochainComplex.HomComplex K L).sc n).homologyπ ≫
      (CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.hom =
      (CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso.hom ≫
        (CochainComplex.HomComplex.leftHomologyData K L n).π :=
    (CochainComplex.HomComplex.leftHomologyData K L n).homologyπ_comp_homologyIso_hom
  have e' : (CochainComplex.HomComplex.leftHomologyData K L n).homologyIso.hom
      (((CochainComplex.HomComplex K L).sc n).homologyπ u) =
      (CochainComplex.HomComplex.leftHomologyData K L n).π
        ((CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso.hom u) :=
    ConcreteCategory.congr_hom e u
  have hz : (CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso.hom u = z := by
    apply Subtype.ext
    have : (CochainComplex.HomComplex.leftHomologyData K L n).i
        ((CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso.hom u) =
        ((CochainComplex.HomComplex K L).sc n).iCycles u :=
      ConcreteCategory.congr_hom
        (CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso_hom_comp_i u
    exact this.trans (iCycles_cyc _ _ _ _ _ _)
  rw [hz] at e'
  exact e'

end HomComplexCls


variable (Y : TopCat.{0})

/-- **Upstream's raw-to-global comparison is the sheafification unit at `⊤`.** -/
lemma topOpenToGlobal_f (n : ℕ) :
    (topOpenToGlobalSingularCochainSheafComplex ℚ Y).f n =
      (toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℚ Y n)).app (op ⊤) := by
  have h := congrArg (fun f => NatTrans.app f (op ⊤))
    (toSheafify_plusPlusIsoSheafify_hom (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
      (singularCochainPresheaf ℚ Y n))
  have h2 := congrArg (fun f => NatTrans.app f (op ⊤))
    (singularCochainToPlusPlusPresheafComplex_f ℚ Y n)
  simp only [NatTrans.comp_app] at h h2
  rw [← h, ← h2]
  rfl

section Elements

open AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- **(d)** Upstream's extension isomorphism, read in degree `n`, is the identity on sections. -/
lemma extendXIso_globalSectionsIso (n : ℕ)
    (s : (singularCochainSheaf ℚ (TopCat.of (ComplexPoint X)) n).presheaf.obj (op ⊤)) :
    ((globalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)).hom
      ((globalSectionsSingularCochainComplexIntIsoExtend X).hom.f (n : ℤ)
        ((sInt_XIso (X := TopCat.of (ComplexPoint X)) (k := n) rfl).inv.hom.app (op ⊤) s)) = s := by
  simp only [globalSectionsSingularCochainComplexIntIsoExtend]
  erw [Iso.trans_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  erw [HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ _
    (show ComplexShape.embeddingUpNat.f n = n from rfl)]
  erw [HomologicalComplex.extendMap_f _ _ (i := n)
    (show ComplexShape.embeddingUpNat.f n = n from rfl)]
  simp only [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  change (((sInt_XIso (X := TopCat.of (ComplexPoint X)) (k := n) rfl).inv ≫
    (sInt_XIso (X := TopCat.of (ComplexPoint X)) (k := n) rfl).hom).hom.app (op ⊤)) s = s
  rw [Iso.inv_hom_id]
  rfl

/-- **(c)** Upstream's global-sections isomorphism sends the cocycle naming `c` to the
sheafified `c`, read in the integer-indexed complex. -/
lemma globalSectionsIso_named {n : ℕ}
    (c : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) n).app (op ⊤) c = 0) :
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).hom.f (n : ℤ)
      ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))).1 =
      (sInt_XIso (X := TopCat.of (ComplexPoint X)) (k := n) rfl).inv.hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (singularCochainPresheaf ℚ (TopCat.of (ComplexPoint X)) n)).app (op ⊤) c) := by
  change TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (n : ℤ))
      ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))).1) = _
  erw [fromSingleEquiv_rightMul_precomp c hc, globalMap,
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality, AddEquiv.apply_symm_apply]

lemma raw_d_eq_zero {Y : TopCat.{0}} {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) :
    (globalRawSingularCochainComplex ℚ Y).d n (n + 1) c = 0 := by
  change ((singularCochainPresheafComplex ℚ Y).d n (n + 1)).app (op ⊤) c = 0
  rw [singularCochainPresheafComplex_d]
  exact hc

/-- **The singular class of a global cocycle `c`**, through upstream's identification of
singular cohomology with the cohomology of raw cochains on the open `⊤`. -/
def singClass {Y : TopCat.{0}} {n : ℕ} (c : OpenCochains ℚ Y (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ Y n).app (op ⊤) c = 0) : Cohomology ℚ Y n :=
  (ordinarySingularCohomologyEquivGlobalRaw ℚ Y n).symm
    (cls (globalRawSingularCochainComplex ℚ Y) n (n + 1) (by simp) c (raw_d_eq_zero c hc))

/-- Upstream's step 2 for its chosen resolution, on the class of a cocycle. -/
lemma globalSections_mk [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle
      (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
      (singularCochainSheafComplexInt X ℚ) n) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSections X n
        (CochainComplex.HomComplex.CohomologyClass.mk
          (z.precomp (constantIntegerSheafComplexIntIsoSingle X).hom)).toSmallShiftedHom =
      namedClass X z := by
  unfold rationalSingularCochainHypercohomologyAddEquivGlobalSections
  dsimp only
  refine @globalSectionsOfResolution_mk X _ ?_ _ ?_ ?_ n z

set_option maxHeartbeats 1000000 in
/-- **Upstream's comparison sends the class named by a global cocycle `c` to the singular class
of `c`.** -/
theorem step3_named_class [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] {n : ℕ}
    (c : OpenCochains ℚ (TopCat.of (ComplexPoint X)) (op ⊤) n)
    (hc : (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) n).app (op ⊤) c = 0) :
    rationalSingularCochainHypercohomologyAddEquivCohomology X n
        (CochainComplex.HomComplex.CohomologyClass.mk
          (((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))).precomp
            (constantIntegerSheafComplexIntIsoSingle X).hom)).toSmallShiftedHom =
      singClass c hc := by
  unfold rationalSingularCochainHypercohomologyAddEquivCohomology
  erw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply]
  erw [globalSections_mk]
  have : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  rw [AddEquiv.symm_apply_eq]
  -- the singular side
  have hR : HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
      (TopCat.of (ComplexPoint X)) n (singClass c hc) =
      cls (globalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))) n (n + 1) (by simp)
        ((topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).f n c)
        (map_d_eq_zero (topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
          c (raw_d_eq_zero c hc)) := by
    unfold HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
    erw [AddEquiv.trans_apply]
    rw [singClass, AddEquiv.apply_symm_apply]
    exact homologyMap_cls _ _ _ _ _ _
  rw [hR]
  -- the global-sections side
  have hL1 : (CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm
      (CochainComplex.HomComplex.CohomologyClass.mk
        ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X))))) =
      cls (CochainComplex.HomComplex
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
          (singularCochainSheafComplexInt X ℚ)) (n : ℤ) ((n : ℤ) + 1) (by simp)
        ((rightMulCocycle c hc).precomp (iotaZ (TopCat.of (ComplexPoint X)))).1
        (cocycle_d _) :=
    (AddEquiv.symm_apply_eq _).mpr (homologyAddEquiv_cls _).symm
  unfold namedClass
  erw [hL1, homologyMap_cls]
  erw [homologyMap_cls]
  erw [extendHomologyIso_cls _ n _ _ (extend_d_zero _ n _ (map_d_eq_zero _ _ (map_d_eq_zero _ _
    (cocycle_d _))))]
  apply cls_eq
  erw [globalSectionsIso_named, extendXIso_globalSectionsIso, topOpenToGlobal_f]
  rfl

end Elements

end HodgeLadder.Cup
