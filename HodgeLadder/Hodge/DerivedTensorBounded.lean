module

public import HodgeLadder.Hodge.TensorBoundedQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# The derived functor of tensoring with a bounded complex

Rung `derived-tensor-bounded` (front `cup`, step 3 of `docs/sketches/cup-hodge-filtration.md`).
For a strictly bounded complex `B` of sheaves of `ℚ`-vector spaces on `Y`, the functor `− ⊗ B` on
cochain complexes inverts quasi-isomorphisms (`tensorBoundedQuasiIso_holds`), so it descends along
the localization `Q : CochainComplex (ShQ Y) ℤ ⥤ DerivedCategory (ShQ Y)`:
`T_B := Localization.lift (− ⊗ B ⋙ Q) _ Q`, with `Q ⋙ T_B ≅ (− ⊗ B) ⋙ Q`.

The construction is stated for any bifunctor `F : C₁ ⥤ C₂ ⥤ D` between abelian categories,
additive in each variable (`derivedMapBifunctorRight`), with the inversion of quasi-isomorphisms as
a hypothesis; the sheaf case specializes `F` to `curriedTensor (ShQ Y)`, Mathlib's tensor product of
complexes (`HomologicalComplex.tensorObj`, Koszul signs `ε₁ = 1`, `ε₂(p, q) = (−1)^p`).

* Additivity: `Localization.functor_additive_iff` along `Qh : HomotopyCategory ⥤ DerivedCategory`
  (left calculus of fractions, `DerivedCategory/Fractions.lean`), and
  `Functor.additive_of_full_essSurj_comp` along the quotient `CochainComplex ⥤ HomotopyCategory`.
  The descent of `− ⊗ B` to the homotopy category (`mapBifunctorMapHomotopy₁`) is not needed.
* Naturality in `B`: `Localization.liftNatTrans` of `Q.map (𝟙_K ⊗ φ)`, compatible with the
  factorization isos (`derivedMapBifunctorRightMap_fac`), unique with that property
  (`derivedMapBifunctorRightMap_unique`), functorial in `φ`.

No shift enters: `T_B` carries no `CommShift` structure (red team finding 6 of
`docs/sketches/cup-hodge-filtration.redteam.md`), and no sign appears in any statement.

## Main definitions

* `HodgeLadder.mapBifunctorRight F B`: `K ↦ mapBifunctor K B F` as a functor on complexes;
  `HodgeLadder.mapBifunctorRightMap F φ` for `φ : B ⟶ B'`
* `HodgeLadder.derivedMapBifunctorRight`, `HodgeLadder.derivedMapBifunctorRightFacIso`,
  `HodgeLadder.derivedMapBifunctorRightMap`, `HodgeLadder.derivedMapBifunctorRightIsoId`
* `HodgeLadder.tensorRightComplex Y B`, `HodgeLadder.tensorRightComplexMap Y φ`
* `HodgeLadder.derivedTensorRight Y B a b` (the functor `T_B`),
  `HodgeLadder.derivedTensorRightFacIso Y B a b : Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q`,
  `HodgeLadder.derivedTensorRightMap Y a b a' b' φ : T_B ⟶ T_{B'}`

## Main results

* `HodgeLadder.derivedMapBifunctorRight_additive`, `HodgeLadder.derivedTensorRight_additive`
* `HodgeLadder.mapBifunctorRight_eq_map₂CochainComplex`: the functor is Mathlib's
  `Functor.map₂CochainComplex` with `B` fixed (`rfl`)
* `HodgeLadder.derivedMapBifunctorRightIsoId_hom_app`: a unit iso `mapBifunctorRight F B ≅ 𝟭`
  descends, with an explicit component
* `HodgeLadder.tensorRightComplex_isInvertedBy`
* `HodgeLadder.derivedTensorRightMap_fac`, `HodgeLadder.derivedTensorRightMap_app`,
  `HodgeLadder.derivedTensorRightMap_unique`, `HodgeLadder.derivedTensorRightMap_id`,
  `HodgeLadder.derivedTensorRightMap_comp`
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace HodgeLadder

section Generic

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- If the target has coproducts indexed by small types, any two complexes have a
`mapBifunctor`. -/
theorem hasMapBifunctor_of_hasCoproducts [HasCoproducts.{0} D] (K : CochainComplex C₁ ℤ)
    (B : CochainComplex C₂ ℤ) : HasMapBifunctor K B F (.up ℤ) :=
  fun _ => HasColimitsOfShape.has_colimit _

/-- Every complex `K` has a `mapBifunctor K B F`. Stated in the context of abelian categories,
so that a specialization carries the same instance terms as the definitions below (the sheaf
instance `hasB_shQ` then type-checks without a kernel unfolding of the sheaf instances). -/
abbrev HasMapBifunctorRight (B : CochainComplex C₂ ℤ) : Prop :=
  ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)

/-- `HasMapBifunctorRight` from coproducts in the target. -/
theorem hasMapBifunctorRight_of_hasCoproducts [HasCoproducts.{0} D] (B : CochainComplex C₂ ℤ) :
    HasMapBifunctorRight (C₁ := C₁) F B :=
  fun K => hasMapBifunctor_of_hasCoproducts F K B

/-- `K ↦ mapBifunctor K B F` as a functor on cochain complexes. -/
@[simps]
def mapBifunctorRight (B : CochainComplex C₂ ℤ) [hasB : ∀ K : CochainComplex C₁ ℤ,
    HasMapBifunctor K B F (.up ℤ)] : CochainComplex C₁ ℤ ⥤ CochainComplex D ℤ where
  obj K := mapBifunctor K B F (.up ℤ)
  map f := mapBifunctorMap f (𝟙 B) F (.up ℤ)
  map_id K := mapBifunctorMap_id' F K B
  map_comp f g := by rw [mapBifunctorMap_comp', Category.comp_id]

/-- A chain map `φ : B ⟶ B'` gives the natural transformation with components
`mapBifunctorMap (𝟙 K) φ F`, that is `𝟙_K ⊗ φ` for the tensor product. -/
@[simps]
def mapBifunctorRightMap {B B' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)] (φ : B ⟶ B') :
    mapBifunctorRight F B ⟶ mapBifunctorRight F B' where
  app K := mapBifunctorMap (𝟙 K) φ F (.up ℤ)
  naturality K L f := by
    change mapBifunctorMap f (𝟙 B) F (.up ℤ) ≫ mapBifunctorMap (𝟙 L) φ F (.up ℤ) =
      mapBifunctorMap (𝟙 K) φ F (.up ℤ) ≫ mapBifunctorMap f (𝟙 B') F (.up ℤ)
    rw [mapBifunctorMap_comp', mapBifunctorMap_comp']
    simp

/-- `mapBifunctorRightMap` preserves identities. -/
theorem mapBifunctorRightMap_id (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)] :
    mapBifunctorRightMap F (𝟙 B) = 𝟙 (mapBifunctorRight F B) := by
  ext K : 2
  exact mapBifunctorMap_id' F K B

/-- `mapBifunctorRightMap` preserves composition. -/
theorem mapBifunctorRightMap_comp {B B' B'' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    [hasB'' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B'' F (.up ℤ)]
    (φ : B ⟶ B') (ψ : B' ⟶ B'') :
    mapBifunctorRightMap F (φ ≫ ψ) = mapBifunctorRightMap F φ ≫ mapBifunctorRightMap F ψ := by
  ext K : 2
  exact ((mapBifunctorMap_comp' F (𝟙 K) (𝟙 K) φ ψ).trans (by rw [Category.comp_id]; rfl)).symm

/-- `mapBifunctorRight F B` is Mathlib's bifunctor on cochain complexes with `B` fixed. -/
theorem mapBifunctorRight_eq_map₂CochainComplex
    [h : ∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HasMapBifunctor K₁ K₂ F (.up ℤ)] (B : CochainComplex C₂ ℤ) :
    mapBifunctorRight F B = F.map₂CochainComplex.flip.obj B := rfl

/-- `mapBifunctorRightMap F φ` is Mathlib's bifunctor on cochain complexes applied to `φ`. -/
theorem mapBifunctorRightMap_eq_map₂CochainComplex
    [h : ∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HasMapBifunctor K₁ K₂ F (.up ℤ)] {B B' : CochainComplex C₂ ℤ} (φ : B ⟶ B') :
    mapBifunctorRightMap F φ = F.map₂CochainComplex.flip.map φ := rfl

/-- `K ↦ mapBifunctor K B F` is additive, since `F` is additive in its first variable. -/
instance mapBifunctorRight_additive (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)] :
    (mapBifunctorRight F B).Additive where
  map_add {K L f g} := by
    change mapBifunctorMap (f + g) (𝟙 B) F (.up ℤ) =
      mapBifunctorMap f (𝟙 B) F (.up ℤ) + mapBifunctorMap g (𝟙 B) F (.up ℤ)
    ext n : 1
    rw [HomologicalComplex.add_f_apply]
    refine mapBifunctor.hom_ext (fun i j h => ?_)
    simp [Preadditive.comp_add]

variable [HasDerivedCategory C₁] [HasDerivedCategory D]

/-- The derived functor of `mapBifunctorRight F B`, given that `mapBifunctorRight F B ⋙ Q`
inverts quasi-isomorphisms: `Localization.lift` along `Q`. -/
def derivedMapBifunctorRight (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q)) :
    DerivedCategory C₁ ⥤ DerivedCategory D :=
  Localization.lift (mapBifunctorRight F B ⋙ DerivedCategory.Q) hB DerivedCategory.Q

/-- The factorization `Q ⋙ T ≅ mapBifunctorRight F B ⋙ Q` (`Localization.fac`). -/
def derivedMapBifunctorRightFacIso (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q)) :
    DerivedCategory.Q ⋙ derivedMapBifunctorRight F B hB ≅
      mapBifunctorRight F B ⋙ DerivedCategory.Q :=
  Localization.fac _ hB DerivedCategory.Q

/-- The derived functor is a lifting, with `Localization.Lifting.iso` the factorization iso. -/
instance derivedMapBifunctorRight_lifting (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q)) :
    Localization.Lifting DerivedCategory.Q (quasiIso C₁ (.up ℤ))
      (mapBifunctorRight F B ⋙ DerivedCategory.Q) (derivedMapBifunctorRight F B hB) :=
  Localization.liftingLift _ hB _

/-- **Additivity.** The derived functor is additive: `Localization.functor_additive_iff` along
`Qh`, which has a left calculus of fractions, reduces it to `Qh ⋙ T`; composed with the quotient
to the homotopy category it is isomorphic to `mapBifunctorRight F B ⋙ Q`, which is additive, and
the quotient is full and essentially surjective. -/
instance derivedMapBifunctorRight_additive (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q)) :
    (derivedMapBifunctorRight F B hB).Additive := by
  rw [Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (.up ℤ))]
  have : (HomotopyCategory.quotient C₁ (.up ℤ) ⋙
      (DerivedCategory.Qh ⋙ derivedMapBifunctorRight F B hB)).Additive :=
    Functor.additive_of_iso ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C₁) _ ≪≫
      derivedMapBifunctorRightFacIso F B hB).symm
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient C₁ (.up ℤ)) _

/-- **Naturality in `B`.** A chain map `φ : B ⟶ B'` gives `T_B ⟶ T_{B'}`, the lift of
`Q.map (mapBifunctorMap (𝟙 K) φ F)` (`Localization.liftNatTrans`). -/
def derivedMapBifunctorRightMap {B B' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (φ : B ⟶ B') :
    derivedMapBifunctorRight F B hB ⟶ derivedMapBifunctorRight F B' hB' :=
  Localization.liftNatTrans DerivedCategory.Q (quasiIso C₁ (.up ℤ))
    (mapBifunctorRight F B ⋙ DerivedCategory.Q) (mapBifunctorRight F B' ⋙ DerivedCategory.Q) _ _
    (Functor.whiskerRight (mapBifunctorRightMap F φ) DerivedCategory.Q)

/-- Compatibility of `derivedMapBifunctorRightMap` with the factorization isos. -/
theorem derivedMapBifunctorRightMap_fac {B B' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (φ : B ⟶ B') :
    Functor.whiskerLeft DerivedCategory.Q (derivedMapBifunctorRightMap F hB hB' φ) ≫
        (derivedMapBifunctorRightFacIso F B' hB').hom =
      (derivedMapBifunctorRightFacIso F B hB).hom ≫
        Functor.whiskerRight (mapBifunctorRightMap F φ) DerivedCategory.Q := by
  ext K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, derivedMapBifunctorRightMap,
    Localization.liftNatTrans_app]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- The components of `derivedMapBifunctorRightMap` at `Q.obj K`. -/
theorem derivedMapBifunctorRightMap_app {B B' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (φ : B ⟶ B') (K : CochainComplex C₁ ℤ) :
    (derivedMapBifunctorRightMap F hB hB' φ).app (DerivedCategory.Q.obj K) =
      (derivedMapBifunctorRightFacIso F B hB).hom.app K ≫
        DerivedCategory.Q.map ((mapBifunctorRightMap F φ).app K) ≫
          (derivedMapBifunctorRightFacIso F B' hB').inv.app K := by
  have := congrArg (fun τ => τ.app K ≫ (derivedMapBifunctorRightFacIso F B' hB').inv.app K)
    (derivedMapBifunctorRightMap_fac F hB hB' φ)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id, Functor.whiskerRight_app] at this
  exact this

/-- **Uniqueness.** `derivedMapBifunctorRightMap` is the only natural transformation compatible
with the factorization isos and `𝟙_K ⊗ φ`. -/
theorem derivedMapBifunctorRightMap_unique {B B' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (φ : B ⟶ B') (τ : derivedMapBifunctorRight F B hB ⟶ derivedMapBifunctorRight F B' hB')
    (hτ : Functor.whiskerLeft DerivedCategory.Q τ ≫ (derivedMapBifunctorRightFacIso F B' hB').hom =
      (derivedMapBifunctorRightFacIso F B hB).hom ≫
        Functor.whiskerRight (mapBifunctorRightMap F φ) DerivedCategory.Q) :
    τ = derivedMapBifunctorRightMap F hB hB' φ := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C₁ (.up ℤ)) (fun K => ?_)
  rw [← cancel_mono ((derivedMapBifunctorRightFacIso F B' hB').hom.app K)]
  have h₁ := congrArg (fun σ => σ.app K) hτ
  have h₂ := congrArg (fun σ => σ.app K) (derivedMapBifunctorRightMap_fac F hB hB' φ)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  exact h₁.trans h₂.symm

/-- `derivedMapBifunctorRightMap` preserves identities. -/
theorem derivedMapBifunctorRightMap_id (B : CochainComplex C₂ ℤ)
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q)) :
    derivedMapBifunctorRightMap F hB hB (𝟙 B) = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C₁ (.up ℤ)) (fun K => ?_)
  rw [derivedMapBifunctorRightMap_app, mapBifunctorRightMap_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- `derivedMapBifunctorRightMap` preserves composition. -/
theorem derivedMapBifunctorRightMap_comp {B B' B'' : CochainComplex C₂ ℤ}
    [hasB : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B' F (.up ℤ)]
    [hasB'' : ∀ K : CochainComplex C₁ ℤ, HasMapBifunctor K B'' F (.up ℤ)]
    (hB : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (hB'' : (quasiIso C₁ (.up ℤ)).IsInvertedBy (mapBifunctorRight F B'' ⋙ DerivedCategory.Q))
    (φ : B ⟶ B') (ψ : B' ⟶ B'') :
    derivedMapBifunctorRightMap F hB hB'' (φ ≫ ψ) =
      derivedMapBifunctorRightMap F hB hB' φ ≫ derivedMapBifunctorRightMap F hB' hB'' ψ := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C₁ (.up ℤ)) (fun K => ?_)
  rw [NatTrans.comp_app, derivedMapBifunctorRightMap_app, derivedMapBifunctorRightMap_app,
    derivedMapBifunctorRightMap_app]
  rw [mapBifunctorRightMap_comp, NatTrans.comp_app, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

end Generic

section Unit

variable {C : Type*} [Category* C] [Abelian C] (F : C ⥤ C ⥤ C) [F.Additive]
  [∀ X, (F.obj X).Additive] [HasDerivedCategory C]

/-- A natural iso `mapBifunctorRight F B ≅ 𝟭` descends to `derivedMapBifunctorRight F B hB ≅ 𝟭`
(`Localization.liftNatIso`). The sheaf instance, for the tensor unit and the right unitor, is left
to rung `pairing-product`. -/
def derivedMapBifunctorRightIsoId (B : CochainComplex C ℤ)
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (ρ : mapBifunctorRight F B ≅ 𝟭 _) :
    derivedMapBifunctorRight F B hB ≅ 𝟭 _ :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (mapBifunctorRight F B ⋙ DerivedCategory.Q) DerivedCategory.Q _ _
    (Functor.isoWhiskerRight ρ DerivedCategory.Q ≪≫ DerivedCategory.Q.leftUnitor)

/-- The component of `derivedMapBifunctorRightIsoId` at `Q.obj K`: the factorization iso
followed by `Q.map (ρ.hom.app K)`, no scalar. -/
theorem derivedMapBifunctorRightIsoId_hom_app (B : CochainComplex C ℤ)
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (ρ : mapBifunctorRight F B ≅ 𝟭 _) (K : CochainComplex C ℤ) :
    (derivedMapBifunctorRightIsoId F B hB ρ).hom.app (DerivedCategory.Q.obj K) =
      (derivedMapBifunctorRightFacIso F B hB).hom.app K ≫
        DerivedCategory.Q.map (ρ.hom.app K) := by
  simp [derivedMapBifunctorRightIsoId, Localization.liftNatIso, Localization.liftNatTrans_app]
  rfl

end Unit

section Sheaves

open MonoidalCategory Cup

attribute [local instance] sheafMonoidal

variable (Y : TopCat.{0})

/-- `ShQ Y` has coproducts indexed by small types. -/
theorem shQ_hasCoproducts : HasCoproducts.{0} (ShQ Y) := fun K =>
  @Sheaf.instHasColimitsOfShape _ _ (J Y) _ _ (Discrete K) _ inferInstance inferInstance

/-- Any two complexes of sheaves of `ℚ`-vector spaces have a tensor product. -/
theorem hasTensor_shQ (K M : CochainComplex (ShQ Y) ℤ) : HomologicalComplex.HasTensor K M :=
  fun _ => HasColimitsOfShape.has_colimit (self := shQ_hasCoproducts Y _) _

/-- Every complex of sheaves of `ℚ`-vector spaces has a tensor product with `B`, as a term to
pass explicitly (instance search for these coproducts on `CochainComplex (ShQ Y) ℤ` runs for
minutes). -/
theorem hasB_shQ (B : CochainComplex (ShQ Y) ℤ) :
    HasMapBifunctorRight (C₁ := ShQ Y) (curriedTensor (ShQ Y)) B :=
  haveI := shQ_hasCoproducts Y
  hasMapBifunctorRight_of_hasCoproducts (curriedTensor (ShQ Y)) B

/-- `− ⊗ B` on cochain complexes of sheaves of `ℚ`-vector spaces: on objects
`HomologicalComplex.tensorObj K B`, on morphisms `HomologicalComplex.tensorHom f (𝟙 B)`
(`tensorRightComplex_obj`, `tensorRightComplex_map`). It plays the role of `tensorRight B`; it is
defined directly, since the monoidal structure on complexes asks for more instances than are
available here. -/
abbrev tensorRightComplex (B : CochainComplex (ShQ Y) ℤ) :
    CochainComplex (ShQ Y) ℤ ⥤ CochainComplex (ShQ Y) ℤ :=
  mapBifunctorRight (hasB := hasB_shQ Y B) (curriedTensor (ShQ Y)) B

/-- A chain map `φ : B ⟶ B'` gives `tensorRightComplex Y B ⟶ tensorRightComplex Y B'`, with
components `𝟙_K ⊗ φ` (`tensorRightComplexMap_app`). -/
abbrev tensorRightComplexMap {B B' : CochainComplex (ShQ Y) ℤ} (φ : B ⟶ B') :
    tensorRightComplex Y B ⟶ tensorRightComplex Y B' :=
  mapBifunctorRightMap (hasB := hasB_shQ Y B)
    (hasB' := hasB_shQ Y B') (curriedTensor (ShQ Y)) φ

/-- On objects, `tensorRightComplex Y B` is Mathlib's tensor product of complexes. -/
theorem tensorRightComplex_obj (B K : CochainComplex (ShQ Y) ℤ) :
    (tensorRightComplex Y B).obj K =
      haveI := hasTensor_shQ Y K B
      HomologicalComplex.tensorObj K B := rfl

/-- On morphisms, `tensorRightComplex Y B` is `f ⊗ 𝟙_B`. -/
theorem tensorRightComplex_map (B : CochainComplex (ShQ Y) ℤ) {K L : CochainComplex (ShQ Y) ℤ}
    (f : K ⟶ L) :
    (tensorRightComplex Y B).map f =
      haveI := hasTensor_shQ Y K B
      haveI := hasTensor_shQ Y L B
      HomologicalComplex.tensorHom f (𝟙 B) := rfl

/-- The components of `tensorRightComplexMap Y φ` are `𝟙_K ⊗ φ`. -/
theorem tensorRightComplexMap_app {B B' : CochainComplex (ShQ Y) ℤ} (φ : B ⟶ B')
    (K : CochainComplex (ShQ Y) ℤ) :
    (tensorRightComplexMap Y φ).app K =
      haveI := hasTensor_shQ Y K B
      haveI := hasTensor_shQ Y K B'
      HomologicalComplex.tensorHom (𝟙 K) φ := rfl

variable [HasDerivedCategory (ShQ Y)]

/-- For `B` strictly bounded, `tensorRightComplex Y B ⋙ Q` inverts quasi-isomorphisms (from
`tensorBoundedQuasiIso_holds`). -/
theorem tensorRightComplex_isInvertedBy (B : CochainComplex (ShQ Y) ℤ) (a b : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] :
    (quasiIso (ShQ Y) (.up ℤ)).IsInvertedBy (tensorRightComplex Y B ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have h := tensorBoundedQuasiIso_holds
  unfold TensorBoundedQuasiIso at h
  have : QuasiIso f := hf
  have hq := @h Y K L f this B a b _ _ (hasTensor_shQ Y K B) (hasTensor_shQ Y L B)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq

/-- **The derived functor `T_B`** of `− ⊗ B` on `D(ShQ Y)`, for `B` strictly bounded, in degrees
`[a, b]`. The bounds enter only through a proof, so `T_B` does not depend on them
(`derivedTensorRight_bounds`). -/
abbrev derivedTensorRight (B : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [B.IsStrictlyGE a]
    [B.IsStrictlyLE b] : DerivedCategory (ShQ Y) ⥤ DerivedCategory (ShQ Y) :=
  derivedMapBifunctorRight (hasB := hasB_shQ Y B) (curriedTensor (ShQ Y)) B
    (tensorRightComplex_isInvertedBy Y B a b)

/-- `T_B` does not depend on the chosen bounds. -/
theorem derivedTensorRight_bounds (B : CochainComplex (ShQ Y) ℤ) (a b a' b' : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] [B.IsStrictlyGE a'] [B.IsStrictlyLE b'] :
    derivedTensorRight Y B a b = derivedTensorRight Y B a' b' := rfl

/-- **Factorization** `Q ⋙ T_B ≅ tensorRightComplex Y B ⋙ Q`. -/
abbrev derivedTensorRightFacIso (B : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [B.IsStrictlyGE a]
    [B.IsStrictlyLE b] :
    DerivedCategory.Q ⋙ derivedTensorRight Y B a b ≅ tensorRightComplex Y B ⋙ DerivedCategory.Q :=
  derivedMapBifunctorRightFacIso (hasB := hasB_shQ Y B) (curriedTensor (ShQ Y)) B
    (tensorRightComplex_isInvertedBy Y B a b)

/-- **Additivity** of `T_B`. -/
instance derivedTensorRight_additive (B : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [B.IsStrictlyGE a]
    [B.IsStrictlyLE b] : (derivedTensorRight Y B a b).Additive :=
  derivedMapBifunctorRight_additive (hasB := hasB_shQ Y B) _ _ _

/-- **Naturality in `B`**: a chain map `φ : B ⟶ B'` gives `T_B ⟶ T_{B'}`. -/
abbrev derivedTensorRightMap {B B' : CochainComplex (ShQ Y) ℤ} (a b a' b' : ℤ) [B.IsStrictlyGE a]
    [B.IsStrictlyLE b] [B'.IsStrictlyGE a'] [B'.IsStrictlyLE b'] (φ : B ⟶ B') :
    derivedTensorRight Y B a b ⟶ derivedTensorRight Y B' a' b' :=
  derivedMapBifunctorRightMap (hasB := hasB_shQ Y B)
    (hasB' := hasB_shQ Y B') (curriedTensor (ShQ Y))
    (tensorRightComplex_isInvertedBy Y B a b) (tensorRightComplex_isInvertedBy Y B' a' b') φ

/-- `T_φ` is compatible with the factorization isos and `𝟙_K ⊗ φ`, with no sign. -/
theorem derivedTensorRightMap_fac {B B' : CochainComplex (ShQ Y) ℤ} (a b a' b' : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] [B'.IsStrictlyGE a'] [B'.IsStrictlyLE b']
    (φ : B ⟶ B') :
    Functor.whiskerLeft DerivedCategory.Q (derivedTensorRightMap Y a b a' b' φ) ≫
        (derivedTensorRightFacIso Y B' a' b').hom =
      (derivedTensorRightFacIso Y B a b).hom ≫
        Functor.whiskerRight (tensorRightComplexMap Y φ) DerivedCategory.Q :=
  derivedMapBifunctorRightMap_fac (hasB := hasB_shQ Y B)
    (hasB' := hasB_shQ Y B') _ _ _ φ

/-- The components of `T_φ` at `Q.obj K`: `Q.map (𝟙_K ⊗ φ)` conjugated by the factorization
isos. -/
theorem derivedTensorRightMap_app {B B' : CochainComplex (ShQ Y) ℤ} (a b a' b' : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] [B'.IsStrictlyGE a'] [B'.IsStrictlyLE b']
    (φ : B ⟶ B') (K : CochainComplex (ShQ Y) ℤ) :
    (derivedTensorRightMap Y a b a' b' φ).app (DerivedCategory.Q.obj K) =
      (derivedTensorRightFacIso Y B a b).hom.app K ≫
        DerivedCategory.Q.map ((tensorRightComplexMap Y φ).app K) ≫
          (derivedTensorRightFacIso Y B' a' b').inv.app K :=
  derivedMapBifunctorRightMap_app (hasB := hasB_shQ Y B)
    (hasB' := hasB_shQ Y B') _ _ _ φ K

/-- `T_φ` is the only natural transformation `T_B ⟶ T_{B'}` compatible with the factorization
isos and `𝟙_K ⊗ φ`. -/
theorem derivedTensorRightMap_unique {B B' : CochainComplex (ShQ Y) ℤ} (a b a' b' : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] [B'.IsStrictlyGE a'] [B'.IsStrictlyLE b']
    (φ : B ⟶ B') (τ : derivedTensorRight Y B a b ⟶ derivedTensorRight Y B' a' b')
    (hτ : Functor.whiskerLeft DerivedCategory.Q τ ≫ (derivedTensorRightFacIso Y B' a' b').hom =
      (derivedTensorRightFacIso Y B a b).hom ≫
        Functor.whiskerRight (tensorRightComplexMap Y φ) DerivedCategory.Q) :
    τ = derivedTensorRightMap Y a b a' b' φ :=
  derivedMapBifunctorRightMap_unique (hasB := hasB_shQ Y B) (hasB' := hasB_shQ Y B') _ _ _ φ τ hτ

/-- `T_{𝟙} = 𝟙`. -/
theorem derivedTensorRightMap_id (B : CochainComplex (ShQ Y) ℤ) (a b : ℤ) [B.IsStrictlyGE a]
    [B.IsStrictlyLE b] :
    derivedTensorRightMap Y a b a b (𝟙 B) = 𝟙 _ :=
  derivedMapBifunctorRightMap_id (hasB := hasB_shQ Y B) _ _ _

/-- `T_{φ ≫ ψ} = T_φ ≫ T_ψ`. -/
theorem derivedTensorRightMap_comp {B B' B'' : CochainComplex (ShQ Y) ℤ} (a b a' b' a'' b'' : ℤ)
    [B.IsStrictlyGE a] [B.IsStrictlyLE b] [B'.IsStrictlyGE a'] [B'.IsStrictlyLE b']
    [B''.IsStrictlyGE a''] [B''.IsStrictlyLE b''] (φ : B ⟶ B') (ψ : B' ⟶ B'') :
    derivedTensorRightMap Y a b a'' b'' (φ ≫ ψ) =
      derivedTensorRightMap Y a b a' b' φ ≫ derivedTensorRightMap Y a' b' a'' b'' ψ :=
  derivedMapBifunctorRightMap_comp (hasB := hasB_shQ Y B)
    (hasB' := hasB_shQ Y B') (hasB'' := hasB_shQ Y B'') _ _ _ _
    φ ψ

end Sheaves

end HodgeLadder
