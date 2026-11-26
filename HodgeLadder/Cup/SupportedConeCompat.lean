module

public import HodgeLadder.Cup.SupportedRawMap
public import HodgeLadder.Cup.ConeMaps

/-!
# Upstream's cone identifications against the raw map

Rungs `supported-cone-compat` and `supported-singular-class` (front `cup`, supported comparison). Upstream's equivalence
`supportedRationalSingularSectionCohomologyEquivRelative` passes from the cone of the supported
sequence to the cone of raw restriction through three cone isomorphisms. On the cone of `Θ`
(`supported-raw-map`), the sheaf-side isomorphisms composed with the cone map of `Θ` equal the
inverse of the raw-to-dual isomorphism followed by the raw-to-sheaf cone map. With upstream's
naturality of `shortExactHomologyIsoCone` and its compatibility with forgetting the `ℚ`-module
structure (`cone-map-lemmas`), upstream's supported singular equivalence sends the class of `Θ₁ c`
to the relative class of `c`, with no sign. So `Θ₁` is an isomorphism on cohomology.

## Main results

* `HodgeLadder.Cup.rawCone_compat`, `HodgeLadder.Cup.relSeq_shortExact`,
  `HodgeLadder.Cup.supported_singular_class_hom`, `HodgeLadder.Cup.supported_singular_class`,
  `HodgeLadder.Cup.homologyMap_rawMap_bijective`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular TopCat.Sheaf CochainComplex

namespace HodgeLadder.Cup

variable (X : TopCat.{0}) [T2Space X] [∀ W : Opens X, ParacompactSpace W] (U V : Opens X)

set_option backward.isDefEq.respectTransparency false in
/-- **The chain-level identity of cone maps.** -/
theorem rawCone_compat :
    mappingCone.map (relSeq X U V).g (supSeq X U V).g (rawMap X U V).τ₂ (rawMap X U V).τ₃
        (rawMap X U V).comm₂₃.symm ≫
      (supportRestrictionSectionsConeIso X U V (rationalSingularCochainComplex X)).hom ≫
      (sectionComplexRestrictionExtendConeIso X (singularCochainSheafComplex ℚ X)
        (Opens.infLELeft V U)).hom =
    (openRawSingularRestrictionConeIsoRelative ℚ X (Opens.infLELeft V U)).inv ≫
      openRawToSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U) := by
  have h1 : (supportRestrictionSectionsConeIso X U V (rationalSingularCochainComplex X)).hom =
      mappingCone.map _ _ (𝟙 _) (supportRestrictionSectionsIntersectionIso X U V
        (rationalSingularCochainComplex X)).hom (by
          simpa using (supportRestrictionSectionsIntersectionIso_restriction X U V
            (rationalSingularCochainComplex X))) :=
    mapArrowHom_eq_map _ _ _ _
  have h2 : (sectionComplexRestrictionExtendConeIso X (singularCochainSheafComplex ℚ X)
      (Opens.infLELeft V U)).hom =
      mappingCone.map (sectionComplexRestriction X (ComplexShape.up ℤ)
          (rationalSingularCochainComplex X) (V.infLELeft U)) _
        (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V)
          (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).hom
        (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X (V ⊓ U))
          (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).hom
        (sectionComplexRestriction_extend X _ _) :=
    mapArrowHom_eq_map _ _ _ _
  have h3 : (openRawSingularRestrictionConeIsoRelative ℚ X (Opens.infLELeft V U)).inv =
      mappingCone.map _ _ (openRawSingularCochainComplexIntIsoDual ℚ X V).inv
        (openRawSingularCochainComplexIntIsoDual ℚ X (V ⊓ U)).inv (by
          rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
          exact (openRawSingularRestrictionInt_transport ℚ X (Opens.infLELeft V U)).symm) :=
    mapArrowHom_eq_map _ _ _ _
  rw [h1, h2, h3, ← mappingCone.map_comp, ← mappingCone.map_comp]
  unfold openRawToSingularSheafRestrictionCone
  rw [← mappingCone.map_comp]
  congr 1
  · simp [rawMap, rawMapMid]
  · simp [rawMap, rawMapEnd]

/-- The relative dual-cochain sequence of `(V, V ⊓ U)` in abelian groups is short exact. -/
lemma relSeq_shortExact : (relSeq X U V).ShortExact :=
  (relativeDualCochainShortComplexInt_shortExact ℚ
    (openInclusionPair X (Opens.infLELeft V U))).map_of_exact _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The comparison as one identity of maps.** -/
theorem supported_singular_class_hom (n : ℕ) :
    haveI := openRawToSingularSheafRestrictionCone_quasiIso X (Opens.infLELeft V U)
    HomologicalComplex.homologyMap (rawMap X U V).τ₁ n ≫
      (mappingCocone.shortExactHomologyIsoCone (supSeq X U V) (supSeq_shortExact X U V)
        ((n : ℤ) - 1) n (by omega)).hom ≫
      HomologicalComplex.homologyMap
        (supportRestrictionSectionsConeIso X U V (rationalSingularCochainComplex X)).hom ((n : ℤ) - 1) ≫
      HomologicalComplex.homologyMap (sectionComplexRestrictionExtendConeIso X
        (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U)).hom ((n : ℤ) - 1) ≫
      inv (HomologicalComplex.homologyMap
        (openRawToSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U)) ((n : ℤ) - 1)) ≫
      HomologicalComplex.homologyMap
        (openRawSingularRestrictionConeIsoRelative ℚ X (Opens.infLELeft V U)).hom ((n : ℤ) - 1) ≫
      HomologicalComplex.homologyMap (mappingCone.mapHomologicalComplexIso
        (relativeCochainRestrictionInt ℚ (openInclusionPair X (Opens.infLELeft V U)))
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv ((n : ℤ) - 1) ≫
      (ShortComplex.mapHomologyIso ((mappingCone (relativeCochainRestrictionInt ℚ
        (openInclusionPair X (Opens.infLELeft V U)))).sc ((n : ℤ) - 1))
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom =
    (ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
        (openInclusionPair X (Opens.infLELeft V U))).X₁.sc n)
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom ≫
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (relativeDualCochainHomologyIsoCone ℚ (openInclusionPair X (Opens.infLELeft V U)) n).hom := by
  rw [← Category.assoc (HomologicalComplex.homologyMap (rawMap X U V).τ₁ n),
    mappingCocone.shortExactHomologyIsoCone_naturality (rawMap X U V) (relSeq_shortExact X U V)
      (supSeq_shortExact X U V)]
  have hc := congrArg (fun g => HomologicalComplex.homologyMap g ((n : ℤ) - 1)) (rawCone_compat X U V)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  simp only [Category.assoc]
  rw [reassoc_of% hc, IsIso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp_assoc,
    Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp]
  exact map_shortExactHomologyIsoCone (forget₂ (ModuleCat ℚ) AddCommGrpCat)
    (relativeDualCochainShortComplexInt ℚ (openInclusionPair X (Opens.infLELeft V U)))
    (relativeDualCochainShortComplexInt_shortExact ℚ _) (relSeq_shortExact X U V) _ _ _

set_option maxHeartbeats 1000000 in
/-- **Upstream's supported singular equivalence on the image of `Θ₁`.** -/
theorem supported_singular_class (n : ℕ) (x : ((relSeq X U V).X₁).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivRelative X U V n
        (HomologicalComplex.homologyMap (rawMap X U V).τ₁ n x) =
      relativeDualCochainCohomologyEquiv ℚ (openInclusionPair X (Opens.infLELeft V U)) n
        ((ShortComplex.mapHomologyIso
          ((relativeDualCochainShortComplexInt ℚ (openInclusionPair X (Opens.infLELeft V U))).X₁.sc n)
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom x) := by
  simp only [supportedRationalSingularSectionCohomologyEquivRelative,
    supportedSectionHomologyIsoRestrictionCone, openSingularSheafRestrictionConeCohomologyEquivRelative,
    openRawSingularRestrictionConeCohomologyEquivRelative, relativeCochainConeCohomologyEquivCanonical]
  have hM := ConcreteCategory.congr_hom (supported_singular_class_hom X U V n) x
  simp only [ConcreteCategory.comp_apply] at hM
  calc _ = relativeDualCochainCohomologyEquiv ℚ (openInclusionPair X (Opens.infLELeft V U)) n
        ((relativeDualCochainHomologyIsoCone ℚ (openInclusionPair X (Opens.infLELeft V U)) n).symm.toLinearEquiv
          ((ConcreteCategory.hom ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
              (openInclusionPair X (Opens.infLELeft V U))).X₁.sc n)
              (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom ≫
            (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
              (relativeDualCochainHomologyIsoCone ℚ (openInclusionPair X (Opens.infLELeft V U)) n).hom)) x)) := by
        exact congrArg (fun y => relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair X (Opens.infLELeft V U)) n
          ((relativeDualCochainHomologyIsoCone ℚ (openInclusionPair X (Opens.infLELeft V U)) n).symm.toLinearEquiv
            y)) hM
    _ = _ := by
        refine congrArg (relativeDualCochainCohomologyEquiv ℚ
          (openInclusionPair X (Opens.infLELeft V U)) n) ?_
        exact Iso.hom_inv_id_apply
          (relativeDualCochainHomologyIsoCone ℚ (openInclusionPair X (Opens.infLELeft V U)) n) _

/-- **`Θ₁` is an isomorphism on cohomology**: every supported class is the class of the image of
a relative cocycle. -/
theorem homologyMap_rawMap_bijective (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (rawMap X U V).τ₁ (n : ℤ)) := by
  set Φ := supportedRationalSingularSectionCohomologyEquivRelative X U V n
  set M := (ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
    (openInclusionPair X (Opens.infLELeft V U))).X₁.sc n) (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
  have hM : Function.Bijective M := (ConcreteCategory.isIso_iff_bijective M).mp inferInstance
  constructor
  · intro x y hxy
    have h := congrArg Φ hxy
    simp only [Φ] at h
    rw [supported_singular_class, supported_singular_class] at h
    exact hM.1 ((LinearEquiv.injective _) h)
  · intro z
    obtain ⟨x, hx⟩ := hM.2 ((relativeDualCochainCohomologyEquiv ℚ
      (openInclusionPair X (Opens.infLELeft V U)) n).symm (Φ z))
    refine ⟨x, Φ.injective ?_⟩
    refine (supported_singular_class X U V n x).trans ?_
    erw [hx]
    exact LinearEquiv.apply_symm_apply _ _

end HodgeLadder.Cup
