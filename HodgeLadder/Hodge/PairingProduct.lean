module

public import HodgeLadder.Hodge.DerivedTensorBounded
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# The pairing product

Rung `pairing-product` (front `cup`, step 4 of `docs/sketches/cup-hodge-filtration.md`). For
complexes `A, B, D` over an abelian category, a bifunctor `F` (written `K ⊗ B` for
`mapBifunctor K B F`), a unit complex `E` with `lam : E ⊗ B ≅ B`, a chain map
`m : A ⊗ B ⟶ D`, `x : Q E ⟶ (Q A)⟦a⟧` and `y : Q E ⟶ (Q B)⟦b⟧` in the derived category,

`pairProduct m x y := y ≫ (pairAction m x)⟦b⟧ ≫ (shiftFunctorAdd' a b n h).inv : Q E ⟶ (Q D)⟦n⟧`,

where `pairAction m x : Q B ⟶ (Q D)⟦a⟧` is `x ⊗ B` followed by `m⟦a⟧`, so that informally
`pairProduct m x y = y ≫ (x ⊗ B)⟦b⟧ ≫ m`. Here `x ⊗ B` is computed with the derived functor
`T_B = derivedMapBifunctorRight F B hB` of rung `derived-tensor-bounded` (read only through its
factorization iso) and the shift in the first variable is Mathlib's `mapBifunctorShift₁Iso`, which
has no sign. `T_B` needs no `CommShift`.

The statements are generic (any abelian `C`, `F : C ⥤ C ⥤ C` additive in each variable, the
inversion of quasi-isomorphisms by `− ⊗ B` as a hypothesis `hB`), then specialized to the tensor
product of complexes (`tensorPairProduct`, `E = 𝟙`, `lam` the left unitor) and instantiated once
at sheaves of `ℚ`-vector spaces (`pairProductShQ`, `E = ℚ_Y[0]`). Signs: none; every identity
below is exact.

## Main definitions

* `HodgeLadder.pairAction`, `HodgeLadder.pairProduct` (generic)
* `HodgeLadder.tensorRightUnitorNat`, `HodgeLadder.derivedTensorUnitIso`,
  `HodgeLadder.tensorPairProduct` (tensor product of complexes, any abelian monoidal `C`)
* `HodgeLadder.unitComplex Y` (`ℚ_Y[0]`), `HodgeLadder.unitComplexMul Y` (its multiplication,
  the left unitor), `HodgeLadder.pairProductShQ` (sheaves of `ℚ`-vector spaces); the unit iso
  `T_𝟙 ≅ 𝟭` is `HodgeLadder.derivedTensorUnitIso`, stated for any abelian monoidal `C`

## Main results

* Biadditivity: `pairProduct_add_left`, `pairProduct_add_right`, and their sheaf forms
* Naturality along chain maps of `A`, `B`, `D` compatible with `m` and the unitors:
  `pairProduct_naturality` (from `_comp_target`, `_naturality_left`, `_naturality_right`),
  `tensorPairProduct_naturality`, `pairProductShQ_naturality`
* Unit clause: `pairProduct_unit` (for `lam = m = ρ_E`, with `ρ : − ⊗ E ≅ 𝟭` compatible with the
  shift), `tensorPairProduct_unit`, `pairProductShQ_unit`:
  `pairProduct λ x y = y.comp x` on `ℚ_Y[0]`, exact, no sign
* Unitors of complexes without the monoidal structure on complexes:
  `complexRightUnitor_hom_naturality`, `complexLeftUnitor_hom_naturality`,
  `complexRightUnitor_hom_shift` (no sign), `complexLeftUnitor_tensorUnit_inv` (`λ_𝟙 = ρ_𝟙`)
* `unitComplex_eq_single_QX`: `ℚ_Y[0]` is the constant sheaf `ℚ_Y` in degree `0` (`rfl`)
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace HodgeLadder

section Generic

variable {C : Type*} [Category* C] [Abelian C] (F : C ⥤ C ⥤ C) [F.Additive]
  [∀ X, (F.obj X).Additive]

open DerivedCategory

/-- `mapBifunctorShift₁Iso` with its type written through `mapBifunctorRight`: the iso
`(A⟦a⟧) ⊗ B ≅ (A ⊗ B)⟦a⟧`, with no sign (shift in the first variable). -/
def mapBifunctorRightShiftIso (B : CochainComplex C ℤ)
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)] (A : CochainComplex C ℤ)
    (a : ℤ) : (mapBifunctorRight F B).obj (A⟦a⟧) ≅ ((mapBifunctorRight F B).obj A)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso A B F a

/-- Naturality of `mapBifunctorRightShiftIso` in the first variable (Mathlib's
`mapBifunctorShift₁Iso_hom_naturality₁`). -/
@[reassoc]
theorem mapBifunctorRightShiftIso_hom_naturality_left (B : CochainComplex C ℤ)
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)] {A A' : CochainComplex C ℤ}
    (f : A ⟶ A') (a : ℤ) :
    (mapBifunctorRight F B).map (f⟦a⟧') ≫ (mapBifunctorRightShiftIso F B A' a).hom =
      (mapBifunctorRightShiftIso F B A a).hom ≫ ((mapBifunctorRight F B).map f)⟦a⟧' :=
  CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁ f B F a

/-- Naturality of `mapBifunctorShift₁Iso` in the second variable, along a chain map
`g : B ⟶ B'`; no sign, since `g` has degree zero. Mathlib states it only under a global
`HasMapBifunctor` instance (`NatTrans.CommShift (F.map₂CochainComplex.flip.map g)`). -/
@[reassoc]
theorem mapBifunctorShift₁Iso_hom_naturality₂ (A : CochainComplex C ℤ)
    {B B' : CochainComplex C ℤ} (g : B ⟶ B') (a : ℤ) [HasMapBifunctor A B F (.up ℤ)]
    [HasMapBifunctor A B' F (.up ℤ)] :
    mapBifunctorMap (𝟙 (A⟦a⟧)) g F (.up ℤ) ≫ (CochainComplex.mapBifunctorShift₁Iso A B' F a).hom =
      (CochainComplex.mapBifunctorShift₁Iso A B F a).hom ≫
        (mapBifunctorMap (𝟙 A) g F (.up ℤ))⟦a⟧' := by
  ext d p q h
  simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + a) (d + a) rfl rfl,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + a) (d + a) rfl rfl]

/-- Naturality of `mapBifunctorRightShiftIso` in the second variable. -/
@[reassoc]
theorem mapBifunctorRightShiftIso_hom_naturality_right {B B' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' F (.up ℤ)] (g : B ⟶ B')
    (A : CochainComplex C ℤ) (a : ℤ) :
    (mapBifunctorRightMap F g).app (A⟦a⟧) ≫ (mapBifunctorRightShiftIso F B' A a).hom =
      (mapBifunctorRightShiftIso F B A a).hom ≫ ((mapBifunctorRightMap F g).app A)⟦a⟧' :=
  mapBifunctorShift₁Iso_hom_naturality₂ F A g a

variable [HasDerivedCategory C]

/-- Naturality of the factorization iso, written out. -/
@[reassoc]
theorem derivedMapBifunctorRightFacIso_hom_naturality (B : CochainComplex C ℤ)
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (derivedMapBifunctorRight F B hB).map (DerivedCategory.Q.map g) ≫
        (derivedMapBifunctorRightFacIso F B hB).hom.app L =
      (derivedMapBifunctorRightFacIso F B hB).hom.app K ≫
        DerivedCategory.Q.map ((mapBifunctorRight F B).map g) :=
  (derivedMapBifunctorRightFacIso F B hB).hom.naturality g

/-- `T_φ` against the factorization isos, on the `hom` side. -/
@[reassoc]
theorem derivedMapBifunctorRightMap_app_facIso_hom {B B' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (g : B ⟶ B') (K : CochainComplex C ℤ) :
    (derivedMapBifunctorRightMap F hB hB' g).app (DerivedCategory.Q.obj K) ≫
        (derivedMapBifunctorRightFacIso F B' hB').hom.app K =
      (derivedMapBifunctorRightFacIso F B hB).hom.app K ≫
        DerivedCategory.Q.map ((mapBifunctorRightMap F g).app K) := by
  rw [derivedMapBifunctorRightMap_app, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg _ (Category.comp_id _)

/-- `T_φ` against the factorization isos, on the `inv` side. -/
@[reassoc]
theorem derivedMapBifunctorRightMap_app_facIso_inv {B B' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (g : B ⟶ B') (K : CochainComplex C ℤ) :
    DerivedCategory.Q.map ((mapBifunctorRightMap F g).app K) ≫
        (derivedMapBifunctorRightFacIso F B' hB').inv.app K =
      (derivedMapBifunctorRightFacIso F B hB).inv.app K ≫
        (derivedMapBifunctorRightMap F hB hB' g).app (DerivedCategory.Q.obj K) := by
  rw [derivedMapBifunctorRightMap_app, Iso.inv_hom_id_app_assoc]

/-- **The action of `x` on `B`.** For `x : Q E ⟶ (Q A)⟦a⟧`, a unitor `lam : E ⊗ B ≅ B` and a
chain map `m : A ⊗ B ⟶ D` (here `K ⊗ B` is `mapBifunctor K B F`), the morphism
`Q B ⟶ (Q D)⟦a⟧` given by

`Q B ≅ Q (E ⊗ B) ≅ T_B (Q E) ⟶ T_B ((Q A)⟦a⟧) ≅ T_B (Q (A⟦a⟧)) ≅ Q (A⟦a⟧ ⊗ B)`
`≅ Q ((A ⊗ B)⟦a⟧) ⟶ Q (D⟦a⟧) ≅ (Q D)⟦a⟧`,

that is `Q lam⁻¹`, the factorization iso of `T_B = derivedMapBifunctorRight F B hB`, `T_B` applied
to `x` followed by `Q`'s shift iso, the factorization iso, `Q` of `mapBifunctorShift₁Iso` (shift
in the first variable, no sign) and of `m⟦a⟧`, and `Q`'s shift iso. No sign enters. -/
def pairAction (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a : ℤ} (x : ShiftedHom (Q.obj E) (Q.obj A) a) : ShiftedHom (Q.obj B) (Q.obj D) a :=
  Q.map lam.inv ≫ (derivedMapBifunctorRightFacIso F B hB).inv.app E ≫
    (derivedMapBifunctorRight F B hB).map (x ≫ (Q.commShiftIso a).inv.app A) ≫
    (derivedMapBifunctorRightFacIso F B hB).hom.app (A⟦a⟧) ≫
    Q.map ((mapBifunctorRightShiftIso F B A a).hom ≫ m⟦a⟧') ≫
    (Q.commShiftIso a).hom.app D

/-- **The pairing product** `pairProduct F E hB lam m h x y : Q E ⟶ (Q D)⟦n⟧` of
`x : Q E ⟶ (Q A)⟦a⟧` and `y : Q E ⟶ (Q B)⟦b⟧`, for `a + b = n`: Mathlib's composition of shifted
morphisms `y.comp (pairAction x) h`, that is
`y ≫ (pairAction x)⟦b⟧ ≫ (shiftFunctorAdd' a b n h).inv` (`pairProduct_eq`). In words,
`y ≫ (x ⊗ B)⟦b⟧ ≫ m`: the factor `x` acts on `B` from the left, `y`
is applied first. No sign enters (conventions row "Derived tensor with a bounded complex"). -/
def pairProduct (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj E) (Q.obj A) a)
    (y : ShiftedHom (Q.obj E) (Q.obj B) b) : ShiftedHom (Q.obj E) (Q.obj D) n :=
  y.comp (pairAction F E hB lam m x) h

/-- `pairProduct` unfolded: `y ≫ (pairAction x)⟦b⟧ ≫ (shiftFunctorAdd' a b n h).inv`. -/
theorem pairProduct_eq (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj E) (Q.obj A) a)
    (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB lam m h x y =
      y ≫ (pairAction F E hB lam m x)⟦b⟧' ≫
        (shiftFunctorAdd' (DerivedCategory C) a b n h).inv.app (Q.obj D) := rfl

/-- `pairAction` is additive in `x`. -/
theorem pairAction_add (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a : ℤ} (x x' : ShiftedHom (Q.obj E) (Q.obj A) a) :
    pairAction F E hB lam m (x + x') = pairAction F E hB lam m x + pairAction F E hB lam m x' := by
  simp only [pairAction, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]

/-- **Additivity in the first factor.** -/
theorem pairProduct_add_left (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x x' : ShiftedHom (Q.obj E) (Q.obj A) a)
    (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB lam m h (x + x') y =
      pairProduct F E hB lam m h x y + pairProduct F E hB lam m h x' y := by
  rw [pairProduct, pairAction_add, ShiftedHom.comp_add]
  rfl

/-- **Additivity in the second factor.** -/
theorem pairProduct_add_right (E : CochainComplex C ℤ) {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj E) (Q.obj A) a)
    (y y' : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB lam m h x (y + y') =
      pairProduct F E hB lam m h x y + pairProduct F E hB lam m h x y' :=
  ShiftedHom.add_comp _ _ _ _

/-- **Naturality in the target.** -/
theorem pairProduct_comp_target (E : CochainComplex C ℤ) {A B D D' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (m : (mapBifunctorRight F B).obj A ⟶ D)
    (k : D ⟶ D') {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj E) (Q.obj A) a)
    (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB lam (m ≫ k) h x y = pairProduct F E hB lam m h x y ≫ (Q.map k)⟦n⟧' := by
  have he : pairAction F E hB lam (m ≫ k) x = pairAction F E hB lam m x ≫ (Q.map k)⟦a⟧' := by
    have hk : (m ≫ k)⟦a⟧' = m⟦a⟧' ≫ k⟦a⟧' := Functor.map_comp _ _ _
    simp only [pairAction, Category.assoc, hk]
    rw [← Category.assoc _ (m⟦a⟧'), Q.map_comp, Category.assoc,
      Q.commShiftIso_hom_naturality k a]
  rw [pairProduct_eq, pairProduct_eq, he, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc]
  congr 2
  exact (shiftFunctorAdd' (DerivedCategory C) a b n h).inv.naturality (Q.map k)

/-- **Naturality in the first factor.** -/
theorem pairProduct_naturality_left (E : CochainComplex C ℤ) {A A' B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (f : A ⟶ A')
    (m' : (mapBifunctorRight F B).obj A' ⟶ D) {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj E) (Q.obj A) a) (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB lam m' h (x ≫ (Q.map f)⟦a⟧') y =
      pairProduct F E hB lam ((mapBifunctorRight F B).map f ≫ m') h x y := by
  have he : pairAction F E hB lam m' (x ≫ (Q.map f)⟦a⟧') =
      pairAction F E hB lam ((mapBifunctorRight F B).map f ≫ m') x := by
    have h1 : (x ≫ (Q.map f)⟦a⟧') ≫ (Q.commShiftIso a).inv.app A' =
        (x ≫ (Q.commShiftIso a).inv.app A) ≫ Q.map (f⟦a⟧') := by
      rw [Category.assoc, Q.commShiftIso_inv_naturality, Category.assoc]
    have hk : ((mapBifunctorRight F B).map f ≫ m')⟦a⟧' =
        ((mapBifunctorRight F B).map f)⟦a⟧' ≫ m'⟦a⟧' := Functor.map_comp _ _ _
    simp only [pairAction, h1, Functor.map_comp, Category.assoc, hk,
      derivedMapBifunctorRightFacIso_hom_naturality_assoc]
    rw [← Q.map_comp_assoc, mapBifunctorRightShiftIso_hom_naturality_left, Q.map_comp_assoc]
  rw [pairProduct, he]
  rfl

/-- **Naturality in the second factor**, along a chain map `g : B ⟶ B'` compatible with the
unitors `lam`, `lam'`. -/
theorem pairProduct_naturality_right (E : CochainComplex C ℤ) {A B B' D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (lam' : (mapBifunctorRight F B').obj E ≅ B')
    (g : B ⟶ B') (hlam : lam.hom ≫ g = (mapBifunctorRightMap F g).app E ≫ lam'.hom)
    (m' : (mapBifunctorRight F B').obj A ⟶ D) {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj E) (Q.obj A) a) (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB' lam' m' h x (y ≫ (Q.map g)⟦b⟧') =
      pairProduct F E hB lam ((mapBifunctorRightMap F g).app A ≫ m') h x y := by
  have he : Q.map g ≫ pairAction F E hB' lam' m' x =
      pairAction F E hB lam ((mapBifunctorRightMap F g).app A ≫ m') x := by
    have hl : g ≫ lam'.inv = lam.inv ≫ (mapBifunctorRightMap F g).app E := by
      rw [Iso.comp_inv_eq, Category.assoc, ← hlam, Iso.inv_hom_id_assoc]
    have hk : ((mapBifunctorRightMap F g).app A ≫ m')⟦a⟧' =
        ((mapBifunctorRightMap F g).app A)⟦a⟧' ≫ m'⟦a⟧' := Functor.map_comp _ _ _
    simp only [pairAction, ← Q.map_comp_assoc, hl, hk]
    rw [Q.map_comp_assoc, derivedMapBifunctorRightMap_app_facIso_inv_assoc F hB hB',
      ← (derivedMapBifunctorRightMap F hB hB' g).naturality_assoc]
    dsimp only [Functor.comp_obj]
    rw [derivedMapBifunctorRightMap_app_facIso_hom_assoc,
      ← Q.map_comp_assoc, mapBifunctorRightShiftIso_hom_naturality_right_assoc]
  rw [pairProduct, pairProduct, ← he]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]

/-- **Naturality**, along chain maps `f : A ⟶ A'`, `g : B ⟶ B'`, `k : D ⟶ D'` compatible with
`m`, `m'` (`m ≫ k = (f ⊗ g) ≫ m'`) and with the unitors. -/
theorem pairProduct_naturality (E : CochainComplex C ℤ) {A A' B B' D D' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B F (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' F (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B ⋙ DerivedCategory.Q))
    (hB' : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F B' ⋙ DerivedCategory.Q))
    (lam : (mapBifunctorRight F B).obj E ≅ B) (lam' : (mapBifunctorRight F B').obj E ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (k : D ⟶ D')
    (hlam : lam.hom ≫ g = (mapBifunctorRightMap F g).app E ≫ lam'.hom)
    (m : (mapBifunctorRight F B).obj A ⟶ D) (m' : (mapBifunctorRight F B').obj A' ⟶ D')
    (hm : m ≫ k = mapBifunctorMap f g F (.up ℤ) ≫ m') {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj E) (Q.obj A) a) (y : ShiftedHom (Q.obj E) (Q.obj B) b) :
    pairProduct F E hB' lam' m' h (x ≫ (Q.map f)⟦a⟧') (y ≫ (Q.map g)⟦b⟧') =
      pairProduct F E hB lam m h x y ≫ (Q.map k)⟦n⟧' := by
  have e : (mapBifunctorRight F B).map f ≫ (mapBifunctorRightMap F g).app A' =
      mapBifunctorMap f g F (.up ℤ) := by
    exact (mapBifunctorMap_comp' F f (𝟙 A') (𝟙 B) g).trans
      (by rw [Category.comp_id, Category.id_comp])
  rw [pairProduct_naturality_right F E hB hB' lam lam' g hlam, pairProduct_naturality_left,
    ← pairProduct_comp_target, ← Category.assoc, e, hm]
  rfl

/-- **Unit clause.** If `ρ : (− ⊗ E) ≅ 𝟭` commutes with the shift in the first variable (no
sign), then `pairAction` with `lam = ρ_E` and `m = ρ_E` is the identity on `x`. -/
theorem pairAction_unit (E : CochainComplex C ℤ)
    [hasE : ∀ K : CochainComplex C ℤ, HasMapBifunctor K E F (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F E ⋙ DerivedCategory.Q))
    (ρ : mapBifunctorRight F E ≅ 𝟭 _)
    (hρ : ∀ a : ℤ, ρ.hom.app (E⟦a⟧) = (mapBifunctorRightShiftIso F E E a).hom ≫ (ρ.hom.app E)⟦a⟧')
    {a : ℤ} (x : ShiftedHom (Q.obj E) (Q.obj E) a) :
    pairAction F E hE (ρ.app E) (ρ.hom.app E) x = x := by
  have hu : ∀ (K : CochainComplex C ℤ) {Z : DerivedCategory C} (w : Q.obj K ⟶ Z),
      (derivedMapBifunctorRightFacIso F E hE).hom.app K ≫ Q.map (ρ.hom.app K) ≫ w =
        (derivedMapBifunctorRightIsoId F E hE ρ).hom.app (Q.obj K) ≫ w := fun K _ w => by
    rw [derivedMapBifunctorRightIsoId_hom_app, Category.assoc]
  have hn := (derivedMapBifunctorRightIsoId F E hE ρ).hom.naturality
    (x ≫ (Q.commShiftIso a).inv.app E)
  simp only [Functor.id_map] at hn
  rw [pairAction, ← hρ, hu, reassoc_of% hn, ← hu E, Iso.inv_hom_id_app_assoc, ← Q.map_comp_assoc,
    Iso.app_inv, Iso.inv_hom_id_app]
  erw [Q.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id x

/-- **Unit clause.** On `E` with `lam = m = ρ_E`, the pairing product is Yoneda composition:
`pairProduct ρ_E x y = y.comp x`, exact, no sign. -/
theorem pairProduct_unit (E : CochainComplex C ℤ)
    [hasE : ∀ K : CochainComplex C ℤ, HasMapBifunctor K E F (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight F E ⋙ DerivedCategory.Q))
    (ρ : mapBifunctorRight F E ≅ 𝟭 _)
    (hρ : ∀ a : ℤ, ρ.hom.app (E⟦a⟧) = (mapBifunctorRightShiftIso F E E a).hom ≫ (ρ.hom.app E)⟦a⟧')
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj E) (Q.obj E) a)
    (y : ShiftedHom (Q.obj E) (Q.obj E) b) :
    pairProduct F E hE (ρ.app E) (ρ.hom.app E) h x y = y.comp x h := by
  rw [pairProduct, pairAction_unit F E hE ρ hρ x]

end Generic

section Unitors

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]

section Right

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

/-- Naturality of Mathlib's right unitor of complexes (`HomologicalComplex.rightUnitor`), stated
without the monoidal structure on complexes. -/
theorem complexRightUnitor_inv_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    f ≫ (HomologicalComplex.rightUnitor L).inv =
      (HomologicalComplex.rightUnitor K).inv ≫
        HomologicalComplex.tensorHom f (𝟙 (HomologicalComplex.tensorUnit C (.up ℤ))) := by
  ext i
  simp only [HomologicalComplex.rightUnitor, Iso.symm_inv, HomologicalComplex.comp_f,
    Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom, GradedObject.eval_map,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, HomologicalComplex.id_f,
    MonoidalCategory.whiskerLeft_id, ← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.rightUnitor_inv_naturality_assoc]
  erw [Category.id_comp]

/-- Naturality of the right unitor, `hom` form. -/
theorem complexRightUnitor_hom_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    HomologicalComplex.tensorHom f (𝟙 (HomologicalComplex.tensorUnit C (.up ℤ))) ≫
        (HomologicalComplex.rightUnitor L).hom =
      (HomologicalComplex.rightUnitor K).hom ≫ f := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← complexRightUnitor_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The right unitor of complexes commutes with the shift in the first variable, with no sign:
`ρ_{K⟦a⟧} = (mapBifunctorShift₁Iso K 𝟙 a) ≫ ρ_K⟦a⟧` (inverse form). -/
theorem complexRightUnitor_inv_shift (K : CochainComplex C ℤ) (a : ℤ) :
    (HomologicalComplex.rightUnitor (K⟦a⟧)).inv ≫
        (CochainComplex.mapBifunctorShift₁Iso K (HomologicalComplex.tensorUnit C (.up ℤ))
          (curriedTensor C) a).hom =
      ((HomologicalComplex.rightUnitor K).inv)⟦a⟧' := by
  ext d
  simp only [HomologicalComplex.rightUnitor, Iso.symm_inv, HomologicalComplex.comp_f,
    Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom, GradedObject.eval_map,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, CochainComplex.shiftFunctor_map_f']
  have e := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f K
    (HomologicalComplex.tensorUnit C (.up ℤ)) (curriedTensor C) a d 0 d (add_zero d) (d + a)
    (d + a) (by lia) rfl
  erw [e]
  simp [CochainComplex.shiftFunctorObjXIso]

/-- The right unitor of complexes commutes with the shift in the first variable, with no sign
(`hom` form): `ρ_{K⟦a⟧} = mapBifunctorShift₁Iso K 𝟙 a ≫ ρ_K⟦a⟧`. -/
theorem complexRightUnitor_hom_shift (K : CochainComplex C ℤ) (a : ℤ) :
    (HomologicalComplex.rightUnitor (K⟦a⟧)).hom =
      (CochainComplex.mapBifunctorShift₁Iso K (HomologicalComplex.tensorUnit C (.up ℤ))
          (curriedTensor C) a).hom ≫ ((HomologicalComplex.rightUnitor K).hom)⟦a⟧' := by
  rw [← cancel_epi (HomologicalComplex.rightUnitor (K⟦a⟧)).inv, Iso.inv_hom_id,
    reassoc_of% complexRightUnitor_inv_shift, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]

end Right

section Left

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- Naturality of Mathlib's left unitor of complexes (`HomologicalComplex.leftUnitor`), stated
without the monoidal structure on complexes. -/
theorem complexLeftUnitor_inv_naturality {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    g ≫ (HomologicalComplex.leftUnitor L).inv =
      (HomologicalComplex.leftUnitor K).inv ≫
        HomologicalComplex.tensorHom (𝟙 (HomologicalComplex.tensorUnit C (.up ℤ))) g := by
  ext i
  simp only [HomologicalComplex.leftUnitor, Iso.symm_inv, HomologicalComplex.comp_f,
    Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom, GradedObject.eval_map,
    HomologicalComplex.leftUnitor'_inv, Category.assoc, ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, HomologicalComplex.id_f,
    MonoidalCategory.id_whiskerRight, MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.leftUnitor_inv_naturality_assoc]
  erw [Category.id_comp]

/-- Naturality of the left unitor, `hom` form. -/
theorem complexLeftUnitor_hom_naturality {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.tensorHom (𝟙 (HomologicalComplex.tensorUnit C (.up ℤ))) g ≫
        (HomologicalComplex.leftUnitor L).hom =
      (HomologicalComplex.leftUnitor K).hom ≫ g := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← complexLeftUnitor_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Left

section Both

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- On the unit complex, the left and right unitors of complexes agree (Mathlib's
`unitors_equal` in degree `0`; the other degrees are zero). -/
theorem complexLeftUnitor_tensorUnit_inv :
    (HomologicalComplex.leftUnitor (HomologicalComplex.tensorUnit C (.up ℤ))).inv =
      (HomologicalComplex.rightUnitor (HomologicalComplex.tensorUnit C (.up ℤ))).inv := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  by_cases hi : i = 0
  · subst hi
    simp only [HomologicalComplex.leftUnitor, HomologicalComplex.rightUnitor, Iso.symm_inv,
      Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom, GradedObject.eval_map,
      HomologicalComplex.leftUnitor'_inv, HomologicalComplex.rightUnitor'_inv]
    have key : ∀ {X₀ : C} (e : X₀ ≅ 𝟙_ C), (λ_ X₀).inv ≫ e.inv ▷ X₀ = (ρ_ X₀).inv ≫ X₀ ◁ e.inv :=
      fun e => by
        rw [← cancel_epi e.inv, MonoidalCategory.leftUnitor_inv_naturality_assoc,
          MonoidalCategory.rightUnitor_inv_naturality_assoc, MonoidalCategory.whisker_exchange,
          MonoidalCategory.unitors_inv_equal]
    rw [reassoc_of% key]
  · exact (isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) i hi).eq_of_src _ _

end Both

end Unitors

section TensorUnit

open MonoidalCategory DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- The right unitor `K ⊗ 𝟙 ≅ K` of complexes (`HomologicalComplex.rightUnitor`) as a natural
iso `mapBifunctorRight (curriedTensor C) 𝟙 ≅ 𝟭`. -/
def tensorRightUnitorNat
    [hasE : ∀ K : CochainComplex C ℤ,
      HasMapBifunctor K (HomologicalComplex.tensorUnit C (.up ℤ)) (curriedTensor C) (.up ℤ)] :
    mapBifunctorRight (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => HomologicalComplex.rightUnitor K)
    (fun f => complexRightUnitor_hom_naturality f)


variable [HasDerivedCategory C]

/-- **The unit iso** `T_𝟙 ≅ 𝟭` of the derived functor of `− ⊗ 𝟙`, descended from the right
unitor of complexes (`derivedMapBifunctorRightIsoId`). -/
def derivedTensorUnitIso
    [hasE : ∀ K : CochainComplex C ℤ,
      HasMapBifunctor K (HomologicalComplex.tensorUnit C (.up ℤ)) (curriedTensor C) (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy
      (mapBifunctorRight (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) ⋙ Q)) :
    derivedMapBifunctorRight (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) hE ≅
      𝟭 _ :=
  derivedMapBifunctorRightIsoId _ _ hE tensorRightUnitorNat

omit [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)] in
/-- The component of `derivedTensorUnitIso` at `Q.obj K`: the factorization iso followed by
`Q.map ρ_K`, no scalar. -/
theorem derivedTensorUnitIso_hom_app
    [hasE : ∀ K : CochainComplex C ℤ,
      HasMapBifunctor K (HomologicalComplex.tensorUnit C (.up ℤ)) (curriedTensor C) (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy
      (mapBifunctorRight (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) ⋙ Q))
    (K : CochainComplex C ℤ) :
    (derivedTensorUnitIso hE).hom.app (Q.obj K) =
      (derivedMapBifunctorRightFacIso _ _ hE).hom.app K ≫
        Q.map (HomologicalComplex.rightUnitor K).hom :=
  derivedMapBifunctorRightIsoId_hom_app _ _ hE tensorRightUnitorNat K

/-- The pairing product for the tensor product of complexes, with `E = 𝟙` (the tensor unit
complex) and `lam` the left unitor `𝟙 ⊗ B ≅ B` of complexes. -/
def tensorPairProduct {A B D : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B (curriedTensor C) (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight (curriedTensor C) B ⋙ Q))
    (m : (mapBifunctorRight (curriedTensor C) B).obj A ⟶ D) {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) (Q.obj A) a)
    (y : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) (Q.obj B) b) :
    ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) (Q.obj D) n :=
  pairProduct (curriedTensor C) _ hB (HomologicalComplex.leftUnitor B) m h x y

omit [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)] in
/-- Naturality of `tensorPairProduct` along chain maps, with `m ≫ k = (f ⊗ g) ≫ m'`; the unitor
compatibility is `complexLeftUnitor_hom_naturality`. -/
theorem tensorPairProduct_naturality {A A' B B' D D' : CochainComplex C ℤ}
    [hasB : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B (curriedTensor C) (.up ℤ)]
    [hasB' : ∀ K : CochainComplex C ℤ, HasMapBifunctor K B' (curriedTensor C) (.up ℤ)]
    (hB : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight (curriedTensor C) B ⋙ Q))
    (hB' : (quasiIso C (.up ℤ)).IsInvertedBy (mapBifunctorRight (curriedTensor C) B' ⋙ Q))
    (f : A ⟶ A') (g : B ⟶ B') (k : D ⟶ D')
    (m : (mapBifunctorRight (curriedTensor C) B).obj A ⟶ D)
    (m' : (mapBifunctorRight (curriedTensor C) B').obj A' ⟶ D')
    (hm : m ≫ k = mapBifunctorMap f g (curriedTensor C) (.up ℤ) ≫ m') {a b n : ℤ}
    (h : a + b = n)
    (x : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) (Q.obj A) a)
    (y : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) (Q.obj B) b) :
    tensorPairProduct hB' m' h (x ≫ (Q.map f)⟦a⟧') (y ≫ (Q.map g)⟦b⟧') =
      tensorPairProduct hB m h x y ≫ (Q.map k)⟦n⟧' :=
  pairProduct_naturality _ _ hB hB' _ _ f g k (complexLeftUnitor_hom_naturality g).symm m m' hm
    h x y

/-- **Unit clause** for the tensor product: on `𝟙[0]` with `m` the left unitor, the pairing
product is Yoneda composition, `tensorPairProduct λ x y = y.comp x`, exact, no sign. -/
theorem tensorPairProduct_unit
    [hasE : ∀ K : CochainComplex C ℤ,
      HasMapBifunctor K (HomologicalComplex.tensorUnit C (.up ℤ)) (curriedTensor C) (.up ℤ)]
    (hE : (quasiIso C (.up ℤ)).IsInvertedBy
      (mapBifunctorRight (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) ⋙ Q))
    {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ)))
      (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) a)
    (y : ShiftedHom (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ)))
      (Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) b) :
    tensorPairProduct hE (HomologicalComplex.leftUnitor _).hom h x y = y.comp x h := by
  have hl : HomologicalComplex.leftUnitor (HomologicalComplex.tensorUnit C (.up ℤ)) =
      HomologicalComplex.rightUnitor _ :=
    Iso.ext ((Iso.inv_eq_inv _ _).1 complexLeftUnitor_tensorUnit_inv)
  have := pairProduct_unit (curriedTensor C) _ hE tensorRightUnitorNat
    (fun a => complexRightUnitor_hom_shift _ a) h x y
  dsimp only [tensorPairProduct]
  rw [hl]
  exact this

end TensorUnit


section Sheaves

open MonoidalCategory Cup DerivedCategory

attribute [local instance] sheafMonoidal

variable (Y : TopCat.{0})

/-- The unit complex `ℚ_Y[0]`: Mathlib's tensor unit of complexes of sheaves of `ℚ`-vector
spaces, the single complex on `𝟙_ (ShQ Y)` in degree `0`. -/
abbrev unitComplex : CochainComplex (ShQ Y) ℤ := HomologicalComplex.tensorUnit (ShQ Y) (.up ℤ)

/-- **Bridge to the constant sheaf.** The unit complex is the constant sheaf `ℚ_Y` in degree `0`,
by definition (`HodgeLadder.Cup.unitIsoQX : 𝟙_ (ShQ Y) ≅ QX Y` is `Iso.refl`). -/
theorem unitComplex_eq_single_QX :
    unitComplex Y = (HomologicalComplex.single (ShQ Y) (.up ℤ) 0).obj (QX Y) := rfl

/-- `ℚ_Y[0]` is strictly concentrated in degrees `≥ 0`. -/
instance unitComplex_isStrictlyGE : (unitComplex Y).IsStrictlyGE 0 :=
  inferInstanceAs (((CochainComplex.singleFunctor (ShQ Y) 0).obj (𝟙_ (ShQ Y))).IsStrictlyGE 0)

/-- `ℚ_Y[0]` is strictly concentrated in degrees `≤ 0`. -/
instance unitComplex_isStrictlyLE : (unitComplex Y).IsStrictlyLE 0 :=
  inferInstanceAs (((CochainComplex.singleFunctor (ShQ Y) 0).obj (𝟙_ (ShQ Y))).IsStrictlyLE 0)

/-- The unit multiplication `ℚ_Y[0] ⊗ ℚ_Y[0] ⟶ ℚ_Y[0]`: Mathlib's left unitor of complexes,
typed as the `m` of `pairProductShQ`. Name it in statements; writing the unitor as `m` costs
about 8 s of kernel time per declaration (instance diamond, `docs/gaps.md`). -/
def unitComplexMul : (tensorRightComplex Y (unitComplex Y)).obj (unitComplex Y) ⟶ unitComplex Y :=
  (HomologicalComplex.leftUnitor (unitComplex Y)).hom

/-- `unitComplexMul` is the left unitor, by definition. -/
theorem unitComplexMul_eq :
    unitComplexMul Y = (HomologicalComplex.leftUnitor (unitComplex Y)).hom := rfl

variable [HasDerivedCategory (ShQ Y)]

/-- **The pairing product on `D(ShQ Y)`.** For `B` strictly bounded in `[lo, hi]`, a chain map
`m : A ⊗ B ⟶ D`, `x : ℚ_Y[0] ⟶ A[a]` and `y : ℚ_Y[0] ⟶ B[b]`: `y ≫ (x ⊗ B)⟦b⟧ ≫ m`, with
`x ⊗ B` through the derived tensor `derivedTensorRight Y B lo hi` and the left unitor
`ℚ_Y[0] ⊗ B ≅ B`. No sign. -/
abbrev pairProductShQ {A B D : CochainComplex (ShQ Y) ℤ} (lo hi : ℤ) [B.IsStrictlyGE lo]
    [B.IsStrictlyLE hi] (m : (tensorRightComplex Y B).obj A ⟶ D) {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj A) a)
    (y : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj B) b) :
    ShiftedHom (Q.obj (unitComplex Y)) (Q.obj D) n :=
  tensorPairProduct (hasB := hasB_shQ Y B) (tensorRightComplex_isInvertedBy Y B lo hi) m h x y

/-- **Additivity in `x`** on `D(ShQ Y)`. -/
theorem pairProductShQ_add_left {A B D : CochainComplex (ShQ Y) ℤ} (lo hi : ℤ)
    [B.IsStrictlyGE lo] [B.IsStrictlyLE hi] (m : (tensorRightComplex Y B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x x' : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj A) a)
    (y : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj B) b) :
    pairProductShQ Y lo hi m h (x + x') y =
      pairProductShQ Y lo hi m h x y + pairProductShQ Y lo hi m h x' y :=
  pairProduct_add_left (hasB := hasB_shQ Y B) _ _ _ _ _ h x x' y

/-- **Additivity in `y`** on `D(ShQ Y)`. -/
theorem pairProductShQ_add_right {A B D : CochainComplex (ShQ Y) ℤ} (lo hi : ℤ)
    [B.IsStrictlyGE lo] [B.IsStrictlyLE hi] (m : (tensorRightComplex Y B).obj A ⟶ D)
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj A) a)
    (y y' : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj B) b) :
    pairProductShQ Y lo hi m h x (y + y') =
      pairProductShQ Y lo hi m h x y + pairProductShQ Y lo hi m h x y' :=
  pairProduct_add_right (hasB := hasB_shQ Y B) _ _ _ _ _ h x y y'

/-- **Naturality** on `D(ShQ Y)`, along chain maps `f : A ⟶ A'`, `g : B ⟶ B'`, `k : D ⟶ D'`
with `m ≫ k = (f ⊗ g) ≫ m'`: `pairProduct m' (x ≫ f) (y ≫ g) = pairProduct m x y ≫ k`. -/
theorem pairProductShQ_naturality {A A' B B' D D' : CochainComplex (ShQ Y) ℤ} (lo hi lo' hi' : ℤ)
    [B.IsStrictlyGE lo] [B.IsStrictlyLE hi] [B'.IsStrictlyGE lo'] [B'.IsStrictlyLE hi']
    (f : A ⟶ A') (g : B ⟶ B') (k : D ⟶ D') (m : (tensorRightComplex Y B).obj A ⟶ D)
    (m' : (tensorRightComplex Y B').obj A' ⟶ D')
    (hm : m ≫ k = (haveI := hasTensor_shQ Y A B; haveI := hasTensor_shQ Y A' B';
      HomologicalComplex.tensorHom f g) ≫ m')
    {a b n : ℤ} (h : a + b = n) (x : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj A) a)
    (y : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj B) b) :
    pairProductShQ Y lo' hi' m' h (x ≫ (Q.map f)⟦a⟧') (y ≫ (Q.map g)⟦b⟧') =
      pairProductShQ Y lo hi m h x y ≫ (Q.map k)⟦n⟧' :=
  tensorPairProduct_naturality (hasB := hasB_shQ Y B) (hasB' := hasB_shQ Y B') _ _ f g k m m' hm
    h x y

/-- **Unit clause** on `D(ShQ Y)`: on `ℚ_Y[0]` with `m = λ` the left unitor
`ℚ_Y[0] ⊗ ℚ_Y[0] ≅ ℚ_Y[0]` (`unitComplexMul`, `unitComplexMul_eq`), the pairing product is
Yoneda composition, `pairProductShQ λ x y = y.comp x`, exact, no sign. With the cup product in the diagrammatic order
(`α ∪ β = α.comp β`), this reads `pairProduct λ β α = α ∪ β`. -/
theorem pairProductShQ_unit {a b n : ℤ} (h : a + b = n)
    (x : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj (unitComplex Y)) a)
    (y : ShiftedHom (Q.obj (unitComplex Y)) (Q.obj (unitComplex Y)) b) :
    pairProductShQ Y 0 0 (unitComplexMul Y) h x y = y.comp x h :=
  tensorPairProduct_unit (hasE := hasB_shQ Y _) _ h x y

end Sheaves

end HodgeLadder
