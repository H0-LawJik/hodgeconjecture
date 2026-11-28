module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Exact functors carry cocycle-named derived maps to cocycle-named maps

A Hom-complex cocycle `z : Cocycle K L n` between cochain complexes names the map
`Cocycle.equivHomShift.symm z : K ⟶ L⟦n⟧`, and through `DerivedCategory.Q` a shifted hom
`Q.obj K ⟶ (Q.obj L)⟦n⟧` in the derived category. This file shows that an exact functor
`F : C ⥤ D` between abelian categories carries the class named by `z` to the class named by
`z` mapped degreewise, `cocycleMap F z`, read through the comparison iso
`F.mapDerivedCategoryFactors : Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex _ ⋙ Q`.

The identity is exact, with no sign. Mathlib's shift isos for `F.mapHomologicalComplex`
(`Functor.mapCochainComplexShiftIso`) are the identity in every degree
(`Functor.mapHomologicalComplex_commShiftIso_hom_app_f`), so the shift convention of
`Cocycle.equivHomShift` passes through `F` unchanged; the step in the derived category is the
compatibility of `F.mapDerivedCategoryFactors` with shifts (Mathlib's `NatTrans.CommShift`
instance), used through `ShiftedHom.map_naturality_2`.

Everything is stated for a general exact functor; nothing concrete is instantiated here.

## Main definitions

* `HodgeLadder.ExtMapCocycle.cocycleMap`: a cocycle mapped degreewise by an additive functor

## Main results

* `HodgeLadder.ExtMapCocycle.equivHomShift_symm_cocycleMap`: on cochain complexes, the map named
  by `cocycleMap F z` is `ShiftedHom.map` of the map named by `z` along
  `F.mapHomologicalComplex _`
* `HodgeLadder.ExtMapCocycle.mapDerivedCategory_shiftedHom_cocycle`: the derived form,
  `F.mapDerivedCategory` sends the class named by `z` to the class named by `cocycleMap F z`,
  conjugated by `F.mapDerivedCategoryFactors`
* `HodgeLadder.ExtMapCocycle.cocycleMap_precomp`, `HodgeLadder.ExtMapCocycle.cocycleMap_postcomp`:
  `cocycleMap` commutes with pre- and postcomposition by chain maps
* `HodgeLadder.ExtMapCocycle.mapExactFunctor_hom_named`: the `Ext` form, `Ext.mapExactFunctor F`
  carries an `Ext` class named by `z` to the class named by `cocycleMap F z`, read through the
  comparison of single complexes, no sign
* `HodgeLadder.ExtMapCocycle.mk₀_comp_named`, `HodgeLadder.ExtMapCocycle.comp_mk₀_named`:
  pre- and postcomposition of a named `Ext` class by degree-zero classes;
  `HodgeLadder.ExtMapCocycle.precomp_postcomp_precomp`
* `HodgeLadder.ExtMapCocycle.cocycleMap_id`, `HodgeLadder.ExtMapCocycle.cocycleMap_injective`:
  sanity checks, `cocycleMap (𝟭 C)` is the identity and `cocycleMap F` is injective for faithful
  `F`
-/

@[expose] public section

open CategoryTheory Category Limits CochainComplex HomComplex Abelian

namespace HodgeLadder.ExtMapCocycle

universe w₁ w₂ t t'

section Map

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {n : ℤ}

/-- **The image of a Hom-complex cocycle under an additive functor**, degreewise: the component
of `cocycleMap F z` from degree `p` to degree `q` is `F.map (z.v p q _)`. It is a cocycle
because `δ` commutes with `Cochain.map` (`δ_map`). -/
def cocycleMap (z : Cocycle K L n) :
    Cocycle ((F.mapHomologicalComplex _).obj K) ((F.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map F) (n + 1) rfl
    (by rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])

/-- The components of `cocycleMap F z` are the images of the components of `z`. -/
@[simp]
theorem cocycleMap_v (z : Cocycle K L n) (p q : ℤ) (hpq : p + n = q) :
    (cocycleMap F z).1.v p q hpq = F.map (z.1.v p q hpq) :=
  rfl

/-- Sanity check: for the identity functor, `cocycleMap` is the identity on cocycles. -/
theorem cocycleMap_id (z : Cocycle K L n) : cocycleMap (𝟭 C) z = z :=
  rfl

/-- For a faithful additive functor, `cocycleMap` is injective: a nonzero cocycle maps to a
nonzero cocycle. -/
theorem cocycleMap_injective [F.Faithful] :
    Function.Injective (cocycleMap F (K := K) (L := L) (n := n)) := by
  intro z w h
  ext p q hpq
  have := congrArg (fun c : Cocycle _ _ n => c.1.v p q hpq) h
  simpa using F.map_injective this

/-- **`cocycleMap` commutes with precomposition by a chain map**: mapping `z ∘ g` is
precomposing the mapped cocycle with the mapped chain map. -/
theorem cocycleMap_precomp (z : Cocycle K L n) {K' : CochainComplex C ℤ} (g : K' ⟶ K) :
    cocycleMap F (z.precomp g) =
      (cocycleMap F z).precomp ((F.mapHomologicalComplex _).map g) := by
  ext : 1
  simp [cocycleMap, Cocycle.precomp]

/-- **`cocycleMap` commutes with postcomposition by a chain map**: mapping `g ∘ z` is
postcomposing the mapped cocycle with the mapped chain map. -/
theorem cocycleMap_postcomp (z : Cocycle K L n) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    cocycleMap F (z.postcomp g) =
      (cocycleMap F z).postcomp ((F.mapHomologicalComplex _).map g) := by
  ext : 1
  simp [cocycleMap, Cocycle.postcomp]

/-- **The map named by `cocycleMap F z` is the image of the map named by `z`**: on cochain
complexes, `Cocycle.equivHomShift.symm (cocycleMap F z)` is `ShiftedHom.map` of
`Cocycle.equivHomShift.symm z` along `F.mapHomologicalComplex _`, whose shift isos are the
identity in every degree. Exact, no sign. -/
theorem equivHomShift_symm_cocycleMap (z : Cocycle K L n) :
    Cocycle.equivHomShift.symm (cocycleMap F z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z)
        (F.mapHomologicalComplex (ComplexShape.up ℤ)) := by
  apply Cocycle.equivHomShift.injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨f, rfl⟩ := Cocycle.equivHomShift.surjective z
  rw [AddEquiv.symm_apply_apply]
  ext p q hpq
  simp [cocycleMap, ShiftedHom.map, Cocycle.equivHomShift_apply, Cochain.map_v,
    Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p), HomologicalComplex.XIsoOfEq, eqToHom_map]

end Map

section Derived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K L : CochainComplex C ℤ} {n : ℤ}

/-- **An exact functor carries the class named by a cocycle to the class named by its image.**
For `z : Cocycle K L n`, the shifted hom `Q.obj K ⟶ (Q.obj L)⟦n⟧` named by `z`, mapped by
`F.mapDerivedCategory`, equals the shifted hom named by `cocycleMap F z`, conjugated by the
comparison iso `F.mapDerivedCategoryFactors` at `K` and (shifted by `n`) at `L`. Exact, no
sign: both shift conventions are those of `Cocycle.equivHomShift` and `ShiftedHom.map`. -/
theorem mapDerivedCategory_shiftedHom_cocycle (z : Cocycle K L n) :
    ShiftedHom.map (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q)
        F.mapDerivedCategory =
      F.mapDerivedCategoryFactors.hom.app K ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm (cocycleMap F z)) DerivedCategory.Q ≫
          (F.mapDerivedCategoryFactors.inv.app L)⟦n⟧' := by
  rw [← ShiftedHom.comp_map, ← ShiftedHom.map_naturality_2 _ F.mapDerivedCategoryFactors,
    ShiftedHom.comp_map, ← equivHomShift_symm_cocycleMap, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀]

/-- **The `Ext` form: an exact functor carries a cocycle-named `Ext` class to the class named by
the mapped cocycle.** Let `e : Ext X Y n` be named by `z : Cocycle (X[0]) L n` through a map
`ι : Y[0] ⟶ L`, in the sense `e.hom ≫ (Q.map ι)⟦n⟧' = class of z`. Then `e.mapExactFunctor F`
is named, through `F.mapCochainComplexSingleFunctor 0` and `F.mapHomologicalComplex _ ι`, by
`cocycleMap F z` precomposed with the comparison of single complexes at `X`. Exact, no sign. -/
theorem mapExactFunctor_hom_named [HasExt.{t} C] [HasExt.{t'} D] {X Y : C} {n : ℕ}
    (e : Ext.{t} X Y n) {L : CochainComplex C ℤ}
    (ι : (CochainComplex.singleFunctor C 0).obj Y ⟶ L)
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj X) L n)
    (h : e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    (e.mapExactFunctor F).hom ≫
        (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex _).map ι))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm ((cocycleMap F z).precomp
        ((F.mapCochainComplexSingleFunctor 0).inv.app X))) DerivedCategory.Q := by
  have h2 := congrArg (fun φ => ShiftedHom.map φ F.mapDerivedCategory) h
  simp only at h2
  rw [mapDerivedCategory_shiftedHom_cocycle] at h2
  have hmap : ShiftedHom.map (e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧')
      F.mapDerivedCategory = e.hom.map F.mapDerivedCategory ≫
        (F.mapDerivedCategory.map (DerivedCategory.Q.map ι))⟦(n : ℤ)⟧' := by
    simp only [ShiftedHom.map, Functor.map_comp, assoc, Functor.commShiftIso_hom_naturality]
  rw [hmap] at h2
  have hY : (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y) =
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj Y) := by
    rw [← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app Y), Iso.inv_hom_id_app_assoc]
    exact (F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app Y).symm
  rw [Cocycle.equivHomShift_symm_precomp, Ext.mapExactFunctor_hom]
  rw [DerivedCategory.Q.map_comp, Functor.map_comp, assoc, assoc, ← Functor.map_comp_assoc,
    hY, ← Functor.map_comp, ← F.mapDerivedCategoryFactors_hom_naturality, Functor.map_comp,
    reassoc_of% h2]
  have hX := F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [reassoc_of% hX, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp [ShiftedHom.map]

end Derived

section Named

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt.{t} C]

/-- **Precomposition by a degree-zero class keeps a class named.** If `e : Ext Y A n` is named by
`w` through `ι : A[0] ⟶ L`, then `mk₀ s ∘ e` is named by `w` precomposed with `s[0]`. Exact, no
sign. -/
theorem mk₀_comp_named {X Y A : C} {L : CochainComplex C ℤ} {n : ℕ} (e : Ext.{t} Y A n)
    (ι : (CochainComplex.singleFunctor C 0).obj A ⟶ L)
    (w : Cocycle ((CochainComplex.singleFunctor C 0).obj Y) L n)
    (h : e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm w) DerivedCategory.Q) (s : X ⟶ Y) :
    ((Ext.mk₀ s).comp e (zero_add n)).hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (w.precomp ((CochainComplex.singleFunctor C 0).map s))) DerivedCategory.Q := by
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, assoc, h,
    Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, Functor.map_comp, assoc]
  rfl

/-- **Postcomposition by a degree-zero class along a commuting square keeps a class named.** If
`e : Ext X A n` is named by `w` through `ι : A[0] ⟶ L`, and `c[0] ≫ ι' = ι ≫ φ` for a chain map
`φ : L ⟶ L'`, then `e ∘ mk₀ c` is named by `w` postcomposed with `φ`, through `ι'`. Exact, no
sign. -/
theorem comp_mk₀_named {X A A' : C} {L L' : CochainComplex C ℤ} {n : ℕ} (e : Ext.{t} X A n)
    (ι : (CochainComplex.singleFunctor C 0).obj A ⟶ L)
    (w : Cocycle ((CochainComplex.singleFunctor C 0).obj X) L n)
    (h : e.hom ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm w) DerivedCategory.Q) (c : A ⟶ A')
    (ι' : (CochainComplex.singleFunctor C 0).obj A' ⟶ L') (φ : L ⟶ L')
    (hsq : (CochainComplex.singleFunctor C 0).map c ≫ ι' = ι ≫ φ) :
    (e.comp (Ext.mk₀ c) (add_zero n)).hom ≫ (DerivedCategory.Q.map ι')⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm (w.postcomp φ)) DerivedCategory.Q := by
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, assoc, ← Functor.map_comp,
    ← DerivedCategory.Q_map_single_map, ← Functor.map_comp]
  rw [hsq]
  rw [Functor.map_comp, Functor.map_comp, ← assoc, h, Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, Functor.map_comp, assoc, Functor.commShiftIso_hom_naturality]

omit [HasDerivedCategory C] [HasExt.{t} C] in
/-- Reassociation of pre- and postcomposition of Hom-complex cocycles by chain maps. -/
theorem precomp_postcomp_precomp {K K' K'' L L' : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) (a : K'' ⟶ K') (b : K' ⟶ K) (φ : L ⟶ L') :
    ((z.precomp b).postcomp φ).precomp a = (z.precomp (a ≫ b)).postcomp φ := by
  apply Cocycle.equivHomShift.symm.injective
  simp only [Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp, assoc]

end Named

end HodgeLadder.ExtMapCocycle
