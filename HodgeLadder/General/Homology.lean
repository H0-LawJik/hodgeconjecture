module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Additive

/-!
# Homology functors on classes of cycles

General compatibilities of the homology API of Mathlib, used on the front `cup` to move
comparisons along the forgetful functor from `ℚ`-modules to abelian groups:

* the isomorphism `ShortComplex.mapHomologyIso` on the class of a cycle;
* a map of complexes in a concrete abelian category on `cyclesMk` and on its homology class,
  for any complex shape;
* `ShortComplex.mapHomologyIso` against the shift isomorphisms of the homology functor of
  cochain complexes indexed by `ℤ`, for any shift.

## Main results

* `HodgeLadder.Homology.homologyπ_comp_mapHomologyIso_hom`
* `HodgeLadder.Homology.cyclesMap_cyclesMk`, `HodgeLadder.Homology.homologyMap_homologyπ_cyclesMk`
* `HodgeLadder.Homology.mapHomologyIso_hom_comp_map_shiftIso_inv_app`
-/

@[expose] public section

open CategoryTheory Limits

namespace HodgeLadder.Homology

section MapHomology

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

set_option backward.isDefEq.respectTransparency false in
/-- **`mapHomologyIso` on classes of cycles**: it sends the class of a cycle of `S.map F` to `F`
of the class of the corresponding cycle of `S`. -/
@[reassoc]
lemma homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let hl := S.leftHomologyData
  have key : hl.π ≫ hl.homologyIso.inv = hl.cyclesIso.inv ≫ S.homologyπ := by
    rw [← cancel_epi hl.cyclesIso.hom, Iso.hom_inv_id_assoc, ← Category.assoc,
      ← hl.homologyπ_comp_homologyIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
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

section Concrete

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

/-- **A map of complexes on `cyclesMk`**: the image of `K.cyclesMk x` by `cyclesMap φ i` is
`L.cyclesMk` of the image of `x`. -/
lemma cyclesMap_cyclesMk {K L : HomologicalComplex C c} (φ : K ⟶ L) {i : ι}
    (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).map (HomologicalComplex.cyclesMap φ i) (K.cyclesMk x j hj hx) =
      L.cyclesMk ((forget₂ C Ab).map (φ.f i) x) j hj (by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, φ.comm, Functor.map_comp,
          ConcreteCategory.comp_apply, hx, map_zero]) := by
  apply (AddCommGrpCat.mono_iff_injective ((forget₂ C Ab).map (L.iCycles i))).1 inferInstance
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, HomologicalComplex.cyclesMap_i,
    Functor.map_comp, ConcreteCategory.comp_apply, HomologicalComplex.i_cyclesMk,
    HomologicalComplex.i_cyclesMk]

/-- **A map of complexes on the class of `cyclesMk`**: the image by `homologyMap φ i` of the
class of `K.cyclesMk x` is the class of `L.cyclesMk` of the image of `x`. -/
lemma homologyMap_homologyπ_cyclesMk {K L : HomologicalComplex C c} (φ : K ⟶ L) {i : ι}
    (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).map (HomologicalComplex.homologyMap φ i)
        ((forget₂ C Ab).map (K.homologyπ i) (K.cyclesMk x j hj hx)) =
      (forget₂ C Ab).map (L.homologyπ i) (L.cyclesMk ((forget₂ C Ab).map (φ.f i) x) j hj (by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, φ.comm, Functor.map_comp,
          ConcreteCategory.comp_apply, hx, map_zero])) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, HomologicalComplex.homologyπ_naturality,
    Functor.map_comp, ConcreteCategory.comp_apply, cyclesMap_cyclesMk]

end Concrete

section Shift

open CochainComplex ComplexShape

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [F.PreservesHomology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **`mapHomologyIso` against the shift isomorphisms of homology**, for any shift `n`: on a
cochain complex `K` indexed by `ℤ`, with `n + a = a'`, the isomorphisms
`F (H^{a'} K) ≅ H^{a'} (F K)` and `F (H^a (K⟦n⟧)) ≅ H^a ((F K)⟦n⟧)` are compatible with the shift
isomorphisms `H^{a'} ≅ H^a ∘ ⟦n⟧` and with the commutation of `F` with the shift. -/
lemma mapHomologyIso_hom_comp_map_shiftIso_inv_app (K : CochainComplex C ℤ) (n a a' : ℤ)
    (h : n + a = a') :
    (ShortComplex.mapHomologyIso (K.sc a') F).hom ≫
        F.map (((HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftIso n a a' h).inv.app K) =
      ((HomologicalComplex.homologyFunctor D (up ℤ) 0).shiftIso n a a' h).inv.app
          ((F.mapHomologicalComplex _).obj K) ≫
        HomologicalComplex.homologyMap
          (((F.mapHomologicalComplex (up ℤ)).commShiftIso n).inv.app K) a ≫
        (ShortComplex.mapHomologyIso ((K⟦n⟧).sc a) F).hom := by
  simp only [Functor.shiftIso, Functor.ShiftSequence.shiftIso, ShiftSequence.shiftIso_inv_app]
  rw [← ShortComplex.mapHomologyIso_hom_naturality]
  change _ = ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ ≫ _
  rw [← Category.assoc, ← ShortComplex.homologyMap_comp]
  congr 2
  ext <;> simp [shiftShortComplexFunctorIso, HomologicalComplex.XIsoOfEq, eqToHom_map]

end Shift

end HodgeLadder.Homology
