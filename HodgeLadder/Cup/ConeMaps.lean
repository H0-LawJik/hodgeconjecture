module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import HodgeConjecture.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-!
# Maps of mapping cones from maps of arrows

Rung `cone-map-lemmas`, part of `supported-cone-compat` (front `cup`). For cochain complexes indexed by `ℤ`, the map
of homotopy cofibers induced by a map of arrows (`homotopyCofiber.mapArrowHom`, used by upstream
for its cone isomorphisms) is the mapping-cone map `mappingCone.map` of its two components. An exact functor commutes with
upstream's cone comparison `shortExactHomologyIsoCone` (used to move upstream's relative-cochain
comparison from `ℚ`-modules to abelian groups).

## Main results

* `HodgeLadder.Cup.mapArrowHom_eq_map`
* `HodgeLadder.Cup.map_shiftedLiftShortComplex`, `HodgeLadder.Cup.mapHomologyIso_shiftIso`,
  `HodgeLadder.Cup.map_shortExactHomologyIsoCone`: an exact functor commutes with upstream's
  cone comparison
-/

@[expose] public noncomputable section

open CategoryTheory Limits CochainComplex

namespace HodgeLadder.Cup

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {F G F' G' : CochainComplex C ℤ} (φ : F ⟶ G) (φ' : F' ⟶ G')

set_option backward.isDefEq.respectTransparency false in
/-- **`mapArrowHom` is `mappingCone.map`.** -/
lemma mapArrowHom_eq_map (H : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j)
    (α : Arrow.mk φ ⟶ Arrow.mk φ') :
    HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H α =
      mappingCone.map φ φ' α.left α.right α.w.symm := by
  ext n
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  constructor
  · rw [mappingCone.map, mappingCone.inl_v_desc_f]
    simp [HomologicalComplex.homotopyCofiber.mapArrowHom, mappingCone.inl,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom φ' H (n + 1) n rfl]
  · rw [mappingCone.map, mappingCone.inr_f_desc_f]
    simp [HomologicalComplex.homotopyCofiber.mapArrowHom, mappingCone.inr]

section Functor

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (S : ShortComplex (CochainComplex C ℤ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **An additive functor commutes with the shifted lift into the cone.** -/
lemma map_shiftedLiftShortComplex :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (mappingCocone.shiftedLiftShortComplex S) ≫
      (mappingCone.mapHomologicalComplexIso S.g F).hom =
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫
      mappingCocone.shiftedLiftShortComplex (S.map (F.mapHomologicalComplex _)) := by
  ext n
  dsimp [mappingCone.mapHomologicalComplexIso]
  rw [mappingCone.mapHomologicalComplexXIso_eq S.g F n (n + 1) rfl,
    mappingCone.ext_to_iff _ _ (n + 1) rfl]
  constructor
  · simp [mappingCocone.shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
      mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
      HomComplex.Cochain.leftShift, shiftFunctorObjXIso]
    rw [← F.map_comp, ← F.map_comp, mappingCone.inl_v_fst_v, Category.comp_id]
  · simp [mappingCocone.shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
      mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
      HomComplex.Cochain.leftShift, shiftFunctorObjXIso]
    rw [← F.map_comp, mappingCone.inl_v_snd_v, F.map_zero, Limits.comp_zero]
    simp [mappingCone.descShortComplex]

variable [F.PreservesHomology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **An exact functor commutes with the shift isomorphism of homology.** -/
lemma mapHomologyIso_shiftIso (K : CochainComplex C ℤ) (n n' : ℤ) (h : 1 + n = n') :
    (ShortComplex.mapHomologyIso (K.sc n') F).hom ≫
        F.map (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
          (1 : ℤ) n n' h).inv.app K) =
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftIso (1 : ℤ) n n' h).inv.app
          ((F.mapHomologicalComplex _).obj K) ≫
        HomologicalComplex.homologyMap
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app K) n ≫
        (ShortComplex.mapHomologyIso ((K⟦(1 : ℤ)⟧).sc n) F).hom := by
  simp only [Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    CochainComplex.ShiftSequence.shiftIso_inv_app]
  rw [← ShortComplex.mapHomologyIso_hom_naturality]
  change _ = ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ ≫ _
  rw [← Category.assoc, ← ShortComplex.homologyMap_comp]
  congr 2
  ext <;> simp [shiftShortComplexFunctorIso, HomologicalComplex.XIsoOfEq, eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **An exact functor commutes with upstream's cone comparison `H^{n+1}(A) ≅ H^n(Cone(B → C))`.** -/
theorem map_shortExactHomologyIsoCone (hS : S.ShortExact)
    (hFS : (S.map (F.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact) (n n' : ℤ)
    (h : 1 + n = n') :
    (mappingCocone.shortExactHomologyIsoCone _ hFS n n' h).hom ≫
        HomologicalComplex.homologyMap (mappingCone.mapHomologicalComplexIso S.g F).inv n ≫
        (ShortComplex.mapHomologyIso ((mappingCone S.g).sc n) F).hom =
      (ShortComplex.mapHomologyIso (S.X₁.sc n') F).hom ≫
        F.map (mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom := by
  have hL := map_shiftedLiftShortComplex F S
  have hL' : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app S.X₁ ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCocone.shiftedLiftShortComplex S) =
      mappingCocone.shiftedLiftShortComplex (S.map (F.mapHomologicalComplex _)) ≫
        (mappingCone.mapHomologicalComplexIso S.g F).inv := by
    have := congrArg (fun g => ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
      (1 : ℤ)).inv.app S.X₁ ≫ g ≫ (mappingCone.mapHomologicalComplexIso S.g F).inv) hL
    simpa using this
  simp only [mappingCocone.shortExactHomologyIsoCone, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    asIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (ShortComplex.mapHomologyIso (S.X₁.sc n') F).hom,
    mapHomologyIso_shiftIso F S.X₁ n n' h]
  simp only [Category.assoc]
  congr 1
  erw [← ShortComplex.mapHomologyIso_hom_naturality]
  change _ = HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (mappingCocone.shiftedLiftShortComplex S)) n ≫ _
  have e := congrArg (fun g => HomologicalComplex.homologyMap g n) hL'
  simp only [HomologicalComplex.homologyMap_comp] at e
  rw [reassoc_of% e]

end Functor

end HodgeLadder.Cup
