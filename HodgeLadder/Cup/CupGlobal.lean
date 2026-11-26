module

public import HodgeLadder.Cup.EndClass
public import HodgeLadder.Cup.NamedCocycle
public import HodgeLadder.Cup.Product

/-!
# The cup product against upstream's comparison with global sections

Rung `cup-global-comparison` (front `cup`, first half of `cup-singular-comparison`). Upstream's
steps 1 and 2 send `H^n(X; ℚ)` to the cohomology of the global sections of the singular cochain
sheaves. If they send `x ∈ H^p` and `y ∈ H^q` to the classes named by global cocycles `a` and `b`,
they send `x ∪ y` to `(−1)^{pq}` times the class named by `a ∪ b`.

## Main results

* `HodgeLadder.Cup.shiftedHom_cup_core`, `HodgeLadder.Cup.cup_global_comparison`
-/

@[expose] public noncomputable section

open CategoryTheory Localization AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder.Cup

section Core

variable {D : Type*} [Category D] [HasShift D ℤ]

/-- **The shifted-hom algebra of the comparison**, in any category with a shift by `ℤ`. -/
lemma shiftedHom_cup_core {Tz T Ae Fe S : D} (eA : Ae ≅ Tz) (eF : Fe ≅ T) (ι : Fe ⟶ S)
    {p q n : ℤ} (h : q + p = n)
    (Ex : ShiftedHom T T q) (Xh : ShiftedHom Tz T p) (Ch : ShiftedHom Tz T n)
    (ax : ShiftedHom Ae Fe p) (ac : ShiftedHom Ae Fe n) (R : ShiftedHom S S q)
    (hx : Xh = (ShiftedHom.mk₀ (0 : ℤ) rfl eA.inv).comp
      (ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p)) (add_zero p))
    (hc : Ch = (ShiftedHom.mk₀ (0 : ℤ) rfl eA.inv).comp
      (ac.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add n)) (add_zero n))
    (hcup : Ch = Xh.comp Ex h) (φ : T ⟶ S) (hφ : eF.inv ≫ ι = φ)
    (hend : Ex ≫ φ⟦q⟧' = φ ≫ R) :
    ac.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add n) =
      (ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add p)).comp R h := by
  replace hend : Ex.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) (zero_add q) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)).comp R (add_zero q) := by
    rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, hφ]
    exact hend
  -- cancel `eA` on the left
  have cancelA : ∀ {a : ℤ} (f : ShiftedHom Ae T a),
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp
        ((ShiftedHom.mk₀ (0 : ℤ) rfl eA.inv).comp f (add_zero a)) (add_zero a) = f := by
    intro a f
    rw [← ShiftedHom.comp_assoc _ _ _ (add_zero 0) (add_zero a) (by simp),
      ShiftedHom.mk₀_comp_mk₀, Iso.hom_inv_id, ShiftedHom.mk₀_id_comp]
  have hac : ac.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add n) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp Ch (add_zero n) := by
    rw [hc, cancelA]
  have hax : ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom).comp Xh (add_zero p) := by
    rw [hx, cancelA]
  -- postcompose `ac ≫ eF` with `eF⁻¹ ≫ ι`
  have e1 : ac.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add n) =
      (ac.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add n)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) (zero_add n) := by
    rw [ShiftedHom.comp_assoc _ _ _ (zero_add n) (add_zero 0) (by simp), ShiftedHom.mk₀_comp_mk₀,
      Iso.hom_inv_id_assoc]
  have e2 : ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ι) (zero_add p) =
      (ax.comp (ShiftedHom.mk₀ (0 : ℤ) rfl eF.hom) (zero_add p)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) (zero_add p) := by
    rw [ShiftedHom.comp_assoc _ _ _ (zero_add p) (add_zero 0) (by simp), ShiftedHom.mk₀_comp_mk₀,
      Iso.hom_inv_id_assoc]
  rw [e1, hac, hcup, e2, hax,
    ← ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0 : ℤ) rfl eA.hom) Xh Ex (add_zero p) h (by omega),
    ShiftedHom.comp_assoc _ Ex (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) h (zero_add q)
      (by omega), hend,
    ← ShiftedHom.comp_assoc _ (ShiftedHom.mk₀ (0 : ℤ) rfl (eF.inv ≫ ι)) R (zero_add p)
      (add_zero q) (by omega)]

end Core

section CocycleComp

variable {C : Type*} [Category C] [Abelian C]

/-- Precomposition with a chain map commutes with composing cocycles. -/
lemma cocycleComp_precomp {K K' L M : CochainComplex C ℤ} {p q n : ℤ}
    (z : CochainComplex.HomComplex.Cocycle K L p) (w : CochainComplex.HomComplex.Cocycle L M q)
    (h : p + q = n) (f : K' ⟶ K) :
    cocycleComp (z.precomp f) w h = (cocycleComp z w h).precomp f := by
  ext a c hac
  simp [cocycleComp, CochainComplex.HomComplex.Cocycle.precomp,
    CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]

end CocycleComp

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

attribute [local instance] endHasDerivedCategory endSiteHasDerivedCategory endHasExt

variable (X : Over (Spec ↧ℂ))

/-- The global-section class named by a Hom-complex cocycle `ℤ_X[0] → S` (upstream's step 2 on
its class, `globalSectionsOfResolution_mk`). -/
abbrev namedClass {n : ℤ} (z : CochainComplex.HomComplex.Cocycle
    (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
    (singularCochainSheafComplexInt X ℚ) n) :=
  HomologicalComplex.homologyMap
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
      (singularCochainSheafComplexInt X ℚ)).hom n
    ((CochainComplex.HomComplex.homologyAddEquiv _ _ n).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z))

set_option maxHeartbeats 1000000 in
/-- **The cup product against upstream's comparison with global sections.** -/
theorem cup_global_comparison [IsIntegral X.left] [Smooth X.hom]
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map i)]
    {p q : ℕ} (x : H^p(X; ℚ)) (y : H^q(X; ℚ))
    (a : AlgebraicTopology.Singular.OpenCochains ℚ (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) p)
    (b : AlgebraicTopology.Singular.OpenCochains ℚ (TopCat.of (ComplexPoint X)) (Opposite.op ⊤) q)
    (ha : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) p).app (Opposite.op ⊤) a = 0)
    (hb : (AlgebraicTopology.Singular.singularCochainCoboundary ℚ
      (TopCat.of (ComplexPoint X)) q).app (Opposite.op ⊤) b = 0)
    (hx : rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i p
        (rationalCohomologySingularCochainAddEquiv X p x) =
      namedClass X ((rightMulCocycle a ha).precomp (iotaZ (TopCat.of (ComplexPoint X)))))
    (hy : rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i q
        (rationalCohomologySingularCochainAddEquiv X q y) =
      namedClass X ((rightMulCocycle b hb).precomp (iotaZ (TopCat.of (ComplexPoint X))))) :
    rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i (p + q : ℕ)
        (rationalCohomologySingularCochainAddEquiv X (p + q) (cup x y (p + q) rfl)) =
      (((p : ℤ) * q).negOnePow : ℤ) • namedClass X ((rightMulCocycle (cupGlobal a b)
        (cupGlobal_coboundary ha hb)).precomp (iotaZ (TopCat.of (ComplexPoint X)))) := by
  have : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  -- step 1 of `x`
  have hstepx := (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution
    X I i p).injective (hx.trans (globalSectionsOfResolution_mk X I i p
      ((rightMulCocycle a ha).precomp (iotaZ (TopCat.of (ComplexPoint X))))).symm)
  -- the endomorphism class of `y`
  have hend := end_class_right_mult X I i y b hb hy
  -- the cup product in abelian groups
  have hcup : (cup x y (p + q) rfl).hom =
      x.hom.comp (forgetEnd (TopCat.of (ComplexPoint X))
        (rationalExtEquiv (TopCat.of (ComplexPoint X)) q y)).hom (by push_cast; ring) := by
    rw [cup, cupY_eq_comp_forgetEnd, Abelian.Ext.comp_hom]
  -- the bridges for `x` and for the cup product
  have hbx := hyperEquiv_hom_comp X p ((hypercohomologyAddEquivConstantCohomology ℚ X p).symm x)
  rw [AddEquiv.apply_symm_apply, SmallShiftedHom.equiv_mk₀Inv, SmallShiftedHom.equiv_mk₀] at hbx
  have hbc := hyperEquiv_hom_comp X (p + q)
    ((hypercohomologyAddEquivConstantCohomology ℚ X (p + q)).symm (cup x y (p + q) rfl))
  rw [AddEquiv.apply_symm_apply, SmallShiftedHom.equiv_mk₀Inv, SmallShiftedHom.equiv_mk₀] at hbc
  have hcore := shiftedHom_cup_core
    (Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance))
    (DerivedCategory.Q.mapIso (constantFieldSheafComplexIntIsoSingle ℚ X))
    (DerivedCategory.Q.map (rationalToSingularCochainComplexInt X))
    (show (q : ℤ) + p = ((p + q : ℕ) : ℤ) by push_cast; ring)
    _ _ _ _ _ (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (rightMulClass X b hb)) hbx hbc hcup (DerivedCategory.Q.map (iotaQ X))
    (by rw [iotaQ, CategoryTheory.Functor.map_comp]; rfl) hend
  have hs1 : rationalCohomologySingularCochainAddEquiv X (p + q) (cup x y (p + q) rfl) =
      (rationalCohomologySingularCochainAddEquiv X p x).comp (rightMulClass X b hb)
        (show (q : ℤ) + p = ((p + q : ℕ) : ℤ) by push_cast; ring) := by
    apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [SmallShiftedHom.equiv_comp, rationalCohomologySingularCochainAddEquiv_apply,
      rationalCohomologySingularCochainAddEquiv_apply]
    change SmallShiftedHom.equiv _ _ (((hypercohomologyAddEquivConstantCohomology ℚ X (p + q)).symm
        (cup x y (p + q) rfl)).comp (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (rationalToSingularCochainComplexInt X)) (zero_add _)) =
      (SmallShiftedHom.equiv _ _ (((hypercohomologyAddEquivConstantCohomology ℚ X p).symm x).comp
        (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (rationalToSingularCochainComplexInt X)) (zero_add _))).comp _ _
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀]
    exact hcore
  rw [hs1, hstepx]
  have hcz := namedCocycle_comp_rightMul a b ha hb
  have hc2 := toSmallShiftedHom_cocycleComp.{1}
    (((rightMulCocycle a ha).precomp (iotaZ (TopCat.of (ComplexPoint X)))).precomp
      (constantIntegerSheafComplexIntIsoSingle X).hom) (rightMulCocycle b hb)
    (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; ring)
  rw [cocycleComp_precomp] at hc2
  erw [← hc2, globalSectionsOfResolution_mk]
  have hcz' : cocycleComp ((rightMulCocycle a ha).precomp (iotaZ (TopCat.of (ComplexPoint X))))
      (rightMulCocycle b hb) (show (p : ℤ) + q = ((p + q : ℕ) : ℤ) by push_cast; ring) =
      (((p : ℤ) * q).negOnePow : ℤ) • (rightMulCocycle (cupGlobal a b)
        (cupGlobal_coboundary ha hb)).precomp (iotaZ (TopCat.of (ComplexPoint X))) := hcz
  erw [hcz']
  have hmk : ∀ (k : ℤ) (z : CochainComplex.HomComplex.Cocycle
      (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
      (singularCochainSheafComplexInt X ℚ) ((p + q : ℕ) : ℤ)),
      CochainComplex.HomComplex.CohomologyClass.mk (k • z) =
        k • CochainComplex.HomComplex.CohomologyClass.mk z := fun k z =>
    map_zsmul (CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom _ _ _) k z
  erw [hmk, map_zsmul, map_zsmul]

end HodgeLadder.Cup
