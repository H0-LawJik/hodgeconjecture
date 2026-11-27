module

public import HodgeLadder.Cup.SheafTensor
public import HodgeLadder.Hodge.RationalHypercohomology
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

/-!
# The holomorphic de Rham complex in sheaves of `ℚ`-vector spaces

Rung `rational-de-rham-complex` (front `cup`, step 1 of the construction in
`docs/sketches/cup-hodge-filtration.md`). Upstream's holomorphic de Rham complex `Ω•(X)` lives in
complexes of sheaves of abelian groups on `X(ℂ)`. The cup product of the front is built in
sheaves of `ℚ`-vector spaces (`HodgeLadder.Cup.ShQ`), where the tensor product is exact. This
file builds the same complex there and identifies its underlying complex with upstream's.

The presheaf `U ↦ HolomorphicForm X d U p` is a presheaf of `ℂ`-modules upstream; with the
`ℚ`-module structure obtained by restricting scalars along `ℚ → ℂ` (the instance
`holomorphicFormRatModule`, unique by `subsingleton_rat_module`) it is a presheaf of `ℚ`-vector
spaces whose underlying presheaf of abelian groups is upstream's `holomorphicDeRhamPresheaf`, by
`rfl`. Sheafifying as `ℚ`-vector spaces and forgetting is sheafifying as abelian groups
(`sheafComposeNatIso`, using `HodgeLadder.Cup.preservesSheafification_U`), which gives the
comparison `forgetRationalDeRhamIso`. The differentials, the truncations and the unit are
sheafifications of the same presheaf maps as upstream's, so every comparison below is a
naturality square of that one isomorphism; no scalar enters.

## Spelling

The comparisons of complexes are typed with `HodgeLadder.forgetComplex` (target
`CochainComplex (AnalyticAdditiveSheaf X) ℤ`, the spelling of upstream's `Ω•(X)`, `F^p Ω•(X)` and
of `ℍ^n(X; ·)`). The degreewise lemmas use the site spelling
`Sheaf (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat` of the target of `Cup.forgetSheaf`.
The two are definitionally equal; `rw` and `simp` do not cross them, so proofs combine generic
lemmas with `Eq.trans` and `exact`. The unit is compared through `forgetUnitComplexIso` of rung
`rational-hypercohomology-equiv` (`forget_rationalDeRhamUnit`, that rung's red team, change 8).

## Why the comparison is pinned

Every compatibility above survives replacing `(rationalDeRhamUnit X, forgetRationalDeRhamIso X)`
by `(u ≫ σ, forget(σ)⁻¹ ≫ e)` for a chain automorphism `σ` of `Ω•_ℚ`, for example `σ = −1`; such
a twist would break the unit law of the wedge downstream (`de-rham-cup`). The lemma
`toSheafify_comp_forgetRationalHolomorphicFormSheafIso` rules this out: the comparison
`forget(Ω^p_ℚ) ≅ Ω^p` carries the rational sheafification map to upstream's, which determines it
by the universal property of sheafification, and the unit is then determined because forgetting
is faithful.

## Main definitions

* `HodgeLadder.holomorphicFormRatModule`: `Module ℚ (HolomorphicForm X d U p)`
* `HodgeLadder.rationalHolomorphicFormPresheaf`, `HodgeLadder.rationalHolomorphicFormSheaf`:
  `Ω^p` as a presheaf and as a sheaf of `ℚ`-vector spaces
* `HodgeLadder.rationalDeRhamComplex X`: `Ω•_ℚ`, integer-indexed, zero in negative degrees
* `HodgeLadder.forgetRationalDeRhamIso X`: `forget(Ω•_ℚ) ≅ Ω•(X)`
* `HodgeLadder.rationalHodgeFilteredComplex X p`, `HodgeLadder.rationalHodgeFilteredInclusion`:
  the stupid truncation `F^p Ω•_ℚ` and its inclusion
* `HodgeLadder.forgetRationalHodgeFilteredIso X p`: `forget(F^p Ω•_ℚ) ≅ F^p Ω•(X)`
* `HodgeLadder.rationalDeRhamUnit X`: `ℚ_X[0] ⟶ Ω•_ℚ`
* generic: `HodgeLadder.homFromSingleExtend`, `HodgeLadder.mapStupidTruncIso`

## Main results

* `HodgeLadder.holomorphicFormRatModule_unique`: every `ℚ`-module structure is this one
* `HodgeLadder.rationalHolomorphicFormPresheaf_comp_forget`: the underlying presheaf is
  upstream's `holomorphicDeRhamPresheaf` (`rfl`)
* `HodgeLadder.forget_rationalHolomorphicFormSheafDifferential`: the comparison commutes with `d`
* `HodgeLadder.forget_rationalHodgeFilteredInclusion`: the comparisons commute with the
  inclusions `F^p ⟶ Ω•` and `hodgeFilteredDeRhamInclusion X p`
* `HodgeLadder.forget_rationalConstantsToFormsSheaf`: in degree zero, the forgotten unit is
  `forgetQX ≫ fieldToComplexConstantSheaf ℚ X ≫ constantsToHolomorphicDeRhamZeroSheaf`
* `HodgeLadder.toSheafify_comp_forgetRationalHolomorphicFormSheafIso`: the comparison carries
  the rational sheafification map to upstream's (it pins the comparison)
* `HodgeLadder.forget_rationalDeRhamUnit`: the forgotten unit followed by
  `forgetRationalDeRhamIso` is `forgetUnitComplexIso` followed by upstream's
  `fieldToHolomorphicDeRhamComplexInt ℚ X`; `forget_rationalDeRhamUnit_unfolded` is the same with
  `forgetUnitComplexIso` written out
* `HodgeLadder.hodgeFiltration_eq_range_rational`: upstream's `F^p H_dR^n(X)` is the range of the
  hypercohomology of the forgotten rational truncation
* `HodgeLadder.rationalDeRhamUnit_eq_extendSingleIso`: the unit in the shape of upstream's
  `fieldToHolomorphicDeRhamComplexInt`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry ComplexPoint TopologicalSpace

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder

section Generic

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]

/-- `embeddingUpNat` sends `0` to `0`. -/
lemma embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl

/-- `embeddingUpNat` sends `1` to `1`. -/
lemma embeddingUpNat_f_one : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl

/-- For an `ℕ`-indexed cochain complex `K` and `u : A ⟶ K⁰` with `u ≫ d = 0`, the morphism
`A[0] ⟶ K.extend embeddingUpNat` of integer-indexed complexes with degree-zero component `u`. -/
def homFromSingleExtend (K : CochainComplex C ℕ) {A : C} (u : A ⟶ K.X 0)
    (hu : u ≫ K.d 0 1 = 0) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶
      K.extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.mkHomFromSingle
    (u ≫ (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).inv) (by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat embeddingUpNat_f_zero
        embeddingUpNat_f_one]
      rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hu, zero_comp])

/-- Morphisms `A[0] ⟶ K.extend embeddingUpNat` agree if their degree-zero components agree. -/
lemma homFromSingleExtend_ext {K : CochainComplex C ℕ} {A : C}
    {f g : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶
      K.extend ComplexShape.embeddingUpNat}
    (h : f.f 0 ≫ (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom =
      g.f 0 ≫ (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom) : f = g := by
  apply HomologicalComplex.from_single_hom_ext
  exact (cancel_mono (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom).1 h

/-- The degree-zero component of `homFromSingleExtend K u hu` is `u`. -/
@[simp]
lemma homFromSingleExtend_f_zero (K : CochainComplex C ℕ) {A : C} (u : A ⟶ K.X 0)
    (hu : u ≫ K.d 0 1 = 0) :
    (homFromSingleExtend K u hu).f 0 ≫
        (K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ u := by
  rw [homFromSingleExtend, HomologicalComplex.mkHomFromSingle_f]
  simp

/-- Precomposing `homFromSingleExtend` with `a[0]` precomposes the degree-zero map with `a`. -/
lemma single_map_comp_homFromSingleExtend (K : CochainComplex C ℕ) {A B : C} (a : A ⟶ B)
    (u : B ⟶ K.X 0) (hu : u ≫ K.d 0 1 = 0) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a ≫ homFromSingleExtend K u hu =
      homFromSingleExtend K (a ≫ u) (by rw [Category.assoc, hu, comp_zero]) := by
  apply homFromSingleExtend_ext
  rw [HomologicalComplex.comp_f, Category.assoc, homFromSingleExtend_f_zero,
    homFromSingleExtend_f_zero, HomologicalComplex.single_map_f_self]
  simp

/-- Mathlib's `extendSingleIso` followed by the extension of a map out of `A[0]` (indexed by
`ℕ`) is `homFromSingleExtend` of its degree-zero component. -/
lemma extendSingleIso_inv_comp_extendMap {K : CochainComplex C ℕ} {A : C}
    (φ : (HomologicalComplex.single C (ComplexShape.up ℕ) 0).obj A ⟶ K) :
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0
        embeddingUpNat_f_zero).inv ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
      homFromSingleExtend K
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ φ.f 0) (by
          rw [Category.assoc, φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp,
            comp_zero]) := by
  apply homFromSingleExtend_ext
  rw [homFromSingleExtend_f_zero, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ _ embeddingUpNat_f_zero,
    HomologicalComplex.extendSingleIso_inv_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The shape of upstream's `fieldToHolomorphicDeRhamComplexInt` precomposed with an
identification of the source: an extended map of single complexes followed by an extended
`fromSingle₀Equiv`, after `a[0]` and `extendSingleIso`, is `homFromSingleExtend` of the
composite `a ≫ f ≫ g`. -/
lemma single_map_comp_extendSingleIso_inv_comp {A B : C} (a : A ⟶ B) {B' : C} (f : B ⟶ B')
    {L : CochainComplex C ℕ} (g : B' ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat B 0 0
          embeddingUpNat_f_zero).inv ≫
        (HomologicalComplex.extendMap ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map f)
            ComplexShape.embeddingUpNat ≫
          HomologicalComplex.extendMap ((CochainComplex.fromSingle₀Equiv L B').symm ⟨g, hg⟩)
            ComplexShape.embeddingUpNat) =
      homFromSingleExtend L (a ≫ f ≫ g) (by simp [hg]) := by
  rw [← HomologicalComplex.extendMap_comp, extendSingleIso_inv_comp_extendMap,
    single_map_comp_homFromSingleExtend]
  congr 1
  rw [show (CochainComplex.fromSingle₀Equiv L B').symm ⟨g, hg⟩ =
      HomologicalComplex.mkHomFromSingle g (fun k hk => by
        obtain rfl : k = 1 := by simpa using hk.symm
        exact hg) from rfl, HomologicalComplex.comp_f,
    HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The previous lemma after `singleMapHomologicalComplex`, in the form of the composite that
defines `forgetUnitComplexIso` (rung `rational-hypercohomology-equiv`). -/
lemma singleMap_trans_extendSingleIso_hom_comp (F : C ⥤ D) [F.PreservesZeroMorphisms] {A : C}
    {B B' : D} (a : F.obj A ≅ B) (f : B ⟶ B') {L : CochainComplex D ℕ} (g : B' ⟶ L.X 0)
    (hg : g ≫ L.d 0 1 = 0) :
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app A ≪≫
        (HomologicalComplex.single D (ComplexShape.up ℤ) 0).mapIso a ≪≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat B 0 0
          embeddingUpNat_f_zero).symm).hom ≫
        (HomologicalComplex.extendMap ((HomologicalComplex.single D (ComplexShape.up ℕ) 0).map f)
            ComplexShape.embeddingUpNat ≫
          HomologicalComplex.extendMap ((CochainComplex.fromSingle₀Equiv L B').symm ⟨g, hg⟩)
            ComplexShape.embeddingUpNat) =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app A ≫
        homFromSingleExtend L (a.hom ≫ f ≫ g) (by simp [hg]) := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [single_map_comp_extendSingleIso_inv_comp]

variable (F : C ⥤ D) [F.Additive]

/-- Applying an additive functor to `homFromSingleExtend`, then upstream's comparison
`mapExtendCanonicalIso` and the extension of a chain map `φ`, gives `homFromSingleExtend` of
`F u ≫ φ⁰`, after `singleMapHomologicalComplex`. -/
lemma mapHomologicalComplex_homFromSingleExtend (K : CochainComplex C ℕ) {A : C}
    (u : A ⟶ K.X 0) (hu : u ≫ K.d 0 1 = 0) {L : CochainComplex D ℕ}
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (homFromSingleExtend K u hu) ≫
        (HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).hom ≫
          HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app A ≫
        homFromSingleExtend L (F.map u ≫ φ.f 0) (by
          rw [Category.assoc, φ.comm 0 1, Functor.mapHomologicalComplex_obj_d, ← Category.assoc,
            ← F.map_comp, hu, F.map_zero, zero_comp]) := by
  rw [← cancel_epi
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A),
    ← Category.assoc, Iso.inv_hom_id_app_assoc]
  apply homFromSingleExtend_ext
  simp [HomologicalComplex.extendMap_f _ _ embeddingUpNat_f_zero,
    HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ _ embeddingUpNat_f_zero]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, homFromSingleExtend_f_zero,
    Iso.inv_hom_id_assoc]

section Truncation

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c') (e : c.Embedding c')

/-- Applying a functor commutes with restriction along an embedding; the components are
identities. -/
def mapRestrictionIso [e.IsRelIff] :
    (F.mapHomologicalComplex c).obj (K.restriction e) ≅
      ((F.mapHomologicalComplex c').obj K).restriction e :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun _ _ _ => (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Applying an additive functor commutes with the stupid truncation:
upstream's `mapExtendCanonicalIso` on `K.restriction e`, then `mapRestrictionIso`. -/
def mapStupidTruncIso [e.IsTruncGE] :
    (F.mapHomologicalComplex c').obj (K.stupidTrunc e) ≅
      ((F.mapHomologicalComplex c').obj K).stupidTrunc e :=
  HomologicalComplex.mapExtendCanonicalIso F (K.restriction e) e ≪≫
    (e.extendFunctor D).mapIso (mapRestrictionIso F K e)

/-- `mapStupidTruncIso` carries `F` of the truncation inclusion to the truncation inclusion. -/
lemma mapStupidTruncIso_inclusion [e.IsTruncGE] :
    (F.mapHomologicalComplex c').map (HomologicalComplex.stupidTruncInclusion K e) =
      (mapStupidTruncIso F K e).hom ≫
        HomologicalComplex.stupidTruncInclusion ((F.mapHomologicalComplex c').obj K) e := by
  ext j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.stupidTruncInclusion_f _ _ rfl,
      HomologicalComplex.stupidTruncInclusion_f _ _ rfl,
      show (mapStupidTruncIso F K e).hom =
        (HomologicalComplex.mapExtendCanonicalIso F (K.restriction e) e).hom ≫
          HomologicalComplex.extendMap (mapRestrictionIso F K e).hom e from rfl]
    erw [HomologicalComplex.comp_f]
    rw [HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ _ rfl,
      HomologicalComplex.extendMap_f _ _ rfl]
    dsimp only [HomologicalComplex.stupidTruncXIso, HomologicalComplex.stupidTrunc]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [F.map_comp, eqToHom_map]
    congr 1
    exact (Category.id_comp _).symm
  · exact (F.map_isZero (K.isZero_stupidTrunc_X e _ (by simpa using hj))).eq_of_src _ _

end Truncation

end Generic

/-- Instance search misses `HodgeLadder.Cup.forgetSheaf_additive` at concrete spaces (red team of
`rational-hypercohomology-equiv`, finding 6a); the instance is supplied as a term. -/
local instance rdrForgetAdditive (X : Over (Spec ↧ℂ)) :
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).Additive :=
  Cup.forgetSheaf_additive _

section Forms

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The `ℚ`-vector space structure on upstream's holomorphic forms: restriction of scalars of
the `ℂ`-module structure along `ℚ → ℂ`. Upstream gives none (the red team of `wedge-presheaf`,
finding 2, found that `#synth` fails); by `holomorphicFormRatModule_unique` it is the only one. -/
instance holomorphicFormRatModule (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Module ℚ (HolomorphicForm X d U p) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-- `q • θ = (q : ℂ) • θ` on holomorphic forms, by definition. -/
theorem holomorphicForm_rat_smul_def (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (q : ℚ) (θ : HolomorphicForm X d U p) : q • θ = algebraMap ℚ ℂ q • θ := rfl

/-- The `ℚ`- and `ℂ`-actions on holomorphic forms are compatible. -/
instance holomorphicForm_isScalarTower (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    IsScalarTower ℚ ℂ (HolomorphicForm X d U p) :=
  ⟨fun q c m => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

/-- Every `ℚ`-module structure on the additive group of holomorphic forms is
`holomorphicFormRatModule` (Mathlib's `subsingleton_rat_module`). -/
theorem holomorphicFormRatModule_unique (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (inst : Module ℚ (HolomorphicForm X d U p)) : inst = holomorphicFormRatModule X d U p :=
  Subsingleton.elim _ _

/-- The presheaf of holomorphic `p`-forms on `X(ℂ)` as a presheaf of `ℚ`-vector spaces:
upstream's `HolomorphicForm X d U p` with restriction `holomorphicFormRestriction`, scalars
restricted to `ℚ`. -/
def rationalHolomorphicFormPresheaf (p : ℕ) :
    (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ ⥤ ModuleCat.{0} ℚ where
  obj U := ModuleCat.of ℚ (HolomorphicForm X d U p)
  map i := ModuleCat.ofHom ((holomorphicFormRestriction X d i p).restrictScalars ℚ)
  map_id U := ModuleCat.hom_ext <| LinearMap.ext fun x => by
    change holomorphicFormRestriction X d (𝟙 U) p x = x
    rw [holomorphicFormRestriction_id]
    rfl
  map_comp i j := ModuleCat.hom_ext <| LinearMap.ext fun x => by
    change holomorphicFormRestriction X d (i ≫ j) p x = _
    rw [holomorphicFormRestriction_comp]
    rfl

/-- Forgetting the `ℚ`-structure of `rationalHolomorphicFormPresheaf` gives upstream's
`holomorphicDeRhamPresheaf`, as functors, by `rfl`. -/
theorem rationalHolomorphicFormPresheaf_comp_forget (p : ℕ) :
    rationalHolomorphicFormPresheaf X d p ⋙ Cup.U = holomorphicDeRhamPresheaf X d p := rfl

/-- Upstream's exterior derivative `holomorphicFormDifferential`, as a map of presheaves of
`ℚ`-vector spaces. -/
def rationalHolomorphicFormDifferential (p : ℕ) :
    rationalHolomorphicFormPresheaf X d p ⟶ rationalHolomorphicFormPresheaf X d (p + 1) where
  app U := ModuleCat.ofHom ((holomorphicFormDifferential X d U p).restrictScalars ℚ)
  naturality _ _ i := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    (holomorphicFormRestriction_differential X d i p x).symm

/-- `d ∘ d = 0` on presheaves of `ℚ`-vector spaces. -/
theorem rationalHolomorphicFormDifferential_comp (p : ℕ) :
    rationalHolomorphicFormDifferential X d p ≫
      rationalHolomorphicFormDifferential X d (p + 1) = 0 :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext fun x =>
    holomorphicFormDifferential_squared X d U p x

/-- Forgetting the `ℚ`-structure of the differential gives upstream's
`holomorphicDeRhamDifferential`, by `rfl`. -/
theorem whiskerRight_rationalHolomorphicFormDifferential (p : ℕ) :
    Functor.whiskerRight (rationalHolomorphicFormDifferential X d p) Cup.U =
      holomorphicDeRhamDifferential X d p := rfl

/-- The constant presheaf `ℚ` to holomorphic zero-forms: `q ↦ [q]`, the class of the constant
function `(q : ℂ)` (upstream's `holomorphicFormOfConstant` after `ℚ → ℂ`). -/
def rationalConstantsToFormsPresheaf :
    (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (ModuleCat.of ℚ ℚ) ⟶
      rationalHolomorphicFormPresheaf X d 0 where
  app U := ModuleCat.ofHom
    (((holomorphicFormOfConstant X d U).restrictScalars ℚ).comp (Algebra.linearMap ℚ ℂ))
  naturality _ _ i := ModuleCat.hom_ext <| LinearMap.ext fun q =>
    (holomorphicFormRestriction_ofConstant X d i (algebraMap ℚ ℂ q)).symm

/-- Constants are closed: `d [q] = 0`. -/
theorem rationalConstantsToFormsPresheaf_comp_differential :
    rationalConstantsToFormsPresheaf X d ≫ rationalHolomorphicFormDifferential X d 0 = 0 :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext fun q =>
    holomorphicFormDifferential_ofConstant X d U (algebraMap ℚ ℂ q)

/-- `Ω^p_ℚ`: the sheafification, in sheaves of `ℚ`-vector spaces, of
`rationalHolomorphicFormPresheaf X d p`. -/
def rationalHolomorphicFormSheaf (p : ℕ) : Cup.ShQ (TopCat.of (ComplexPoint X)) :=
  (presheafToSheaf (Cup.J (TopCat.of (ComplexPoint X))) (ModuleCat.{0} ℚ)).obj
    (rationalHolomorphicFormPresheaf X d p)

/-- The sheafified differential `d : Ω^p_ℚ ⟶ Ω^{p+1}_ℚ`. -/
def rationalHolomorphicFormSheafDifferential (p : ℕ) :
    rationalHolomorphicFormSheaf X d p ⟶ rationalHolomorphicFormSheaf X d (p + 1) :=
  (presheafToSheaf (Cup.J (TopCat.of (ComplexPoint X))) (ModuleCat.{0} ℚ)).map
    (rationalHolomorphicFormDifferential X d p)

/-- The `ℕ`-indexed complex `Ω⁰_ℚ ⟶ Ω¹_ℚ ⟶ ⋯`, built as upstream's `holomorphicDeRhamComplex`
with `CochainComplex.of`. -/
def rationalHolomorphicDeRhamComplexNat :
    CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℕ :=
  CochainComplex.of (rationalHolomorphicFormSheaf X d)
    (rationalHolomorphicFormSheafDifferential X d)
    (fun p => by
      change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = 0
      rw [← Functor.map_comp, rationalHolomorphicFormDifferential_comp, Functor.map_zero]
      rfl)

/-- The differential of `rationalHolomorphicDeRhamComplexNat`. -/
@[simp] theorem rationalHolomorphicDeRhamComplexNat_d (p : ℕ) :
    (rationalHolomorphicDeRhamComplexNat X d).d p (p + 1) =
      rationalHolomorphicFormSheafDifferential X d p := by
  simp [rationalHolomorphicDeRhamComplexNat]

/-- `Ω^p_ℚ = 0` for `p` above the dimension. -/
theorem rationalHolomorphicFormSheaf_isZero_of_lt {p : ℕ} (hp : d < p) :
    IsZero (rationalHolomorphicFormSheaf X d p) := by
  refine (presheafToSheaf (Cup.J (TopCat.of (ComplexPoint X))) (ModuleCat.{0} ℚ)).map_isZero ?_
  refine Functor.isZero _ fun U => ?_
  let : Subsingleton ((rationalHolomorphicFormPresheaf X d p).obj U) :=
    ⟨fun x y => by
      rw [holomorphicForm_eq_zero_of_lt X d U hp x, holomorphicForm_eq_zero_of_lt X d U hp y]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Instance search does not find `HodgeLadder.Cup.preservesSheafification_U` at the concrete
space `TopCat.of (ComplexPoint X)` in reasonable time (an unrestricted probe ran past two
minutes); the instance is supplied as a term. -/
local instance rdrPreservesSheafification :
    (Cup.J (TopCat.of (ComplexPoint X))).PreservesSheafification Cup.U :=
  Cup.preservesSheafification_U _

/-- Mathlib's `sheafComposeNatIso` for `Cup.U = forget₂ (ModuleCat ℚ) AddCommGrpCat`:
sheafifying as abelian groups after forgetting is forgetting after sheafifying as `ℚ`-vector
spaces. The same isomorphism defines `HodgeLadder.Cup.forgetQX` through Mathlib's
`constantCommuteCompose`. -/
abbrev forgetSheafifyNatIso :=
  sheafComposeNatIso (Cup.J (TopCat.of (ComplexPoint X))) Cup.U
    (sheafificationAdjunction (Cup.J (TopCat.of (ComplexPoint X))) (ModuleCat.{0} ℚ))
    (sheafificationAdjunction (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0})

/-- `forget(Ω^p_ℚ) ≅ Ω^p`: `forgetSheafifyNatIso` at `rationalHolomorphicFormPresheaf X d p`,
whose underlying presheaf is upstream's `holomorphicDeRhamPresheaf X d p` by `rfl`. -/
def forgetRationalHolomorphicFormSheafIso (p : ℕ) :
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).obj (rationalHolomorphicFormSheaf X d p) ≅
      holomorphicDeRhamSheaf X d p :=
  ((forgetSheafifyNatIso X).app (rationalHolomorphicFormPresheaf X d p)).symm

/-- **The comparison is pinned by sheafification.** Forgetting the `ℚ`-structure of the rational
sheafification map `P_ℚ ⟶ Ω^p_ℚ` and applying `forgetRationalHolomorphicFormSheafIso` gives
upstream's sheafification map `P ⟶ Ω^p`, for `P = holomorphicDeRhamPresheaf X d p` (Mathlib's
`sheafComposeIso_inv_fac`). By the universal property of sheafification this determines the
comparison, so no automorphism of `Ω^p_ℚ` (such as `−1`) can enter it. -/
theorem toSheafify_comp_forgetRationalHolomorphicFormSheafIso (p : ℕ) :
    Functor.whiskerRight (toSheafify (Cup.J (TopCat.of (ComplexPoint X)))
        (rationalHolomorphicFormPresheaf X d p)) Cup.U ≫
      (sheafToPresheaf (Cup.J (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}).map
        (forgetRationalHolomorphicFormSheafIso X d p).hom =
    toSheafify (Cup.J (TopCat.of (ComplexPoint X))) (holomorphicDeRhamPresheaf X d p) :=
  sheafComposeIso_inv_fac (Cup.J (TopCat.of (ComplexPoint X))) Cup.U
    (rationalHolomorphicFormPresheaf X d p)

/-- The comparison commutes with the differentials, by naturality of `forgetSheafifyNatIso`. -/
theorem forget_rationalHolomorphicFormSheafDifferential (p : ℕ) :
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).map
        (rationalHolomorphicFormSheafDifferential X d p) ≫
        (forgetRationalHolomorphicFormSheafIso X d (p + 1)).hom =
      (forgetRationalHolomorphicFormSheafIso X d p).hom ≫
        holomorphicDeRhamSheafDifferential X d p :=
  (forgetSheafifyNatIso X).inv.naturality (rationalHolomorphicFormDifferential X d p)

/-- `forget(Ω•_ℚ) ≅ Ω•` for the `ℕ`-indexed complexes, degreewise
`forgetRationalHolomorphicFormSheafIso`. -/
def forgetRationalHolomorphicDeRhamComplexNatIso :
    ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (rationalHolomorphicDeRhamComplexNat X d) ≅ holomorphicDeRhamComplex X d :=
  HomologicalComplex.Hom.isoOfComponents (fun p => forgetRationalHolomorphicFormSheafIso X d p)
    (by
      rintro i j (rfl : i + 1 = j)
      rw [holomorphicDeRhamComplex_d, Functor.mapHomologicalComplex_obj_d,
        rationalHolomorphicDeRhamComplexNat_d]
      exact (forget_rationalHolomorphicFormSheafDifferential X d i).symm)

/-- `ℚ_X ⟶ Ω⁰_ℚ`: the sheafification of `rationalConstantsToFormsPresheaf` (Mathlib's constant
sheaf is the sheafified constant presheaf). -/
def rationalConstantsToFormsSheaf :
    Cup.QX (TopCat.of (ComplexPoint X)) ⟶ rationalHolomorphicFormSheaf X d 0 :=
  (presheafToSheaf (Cup.J (TopCat.of (ComplexPoint X))) (ModuleCat.{0} ℚ)).map
    (rationalConstantsToFormsPresheaf X d)

/-- Constants are closed, on sheaves. -/
theorem rationalConstantsToFormsSheaf_comp_differential :
    rationalConstantsToFormsSheaf X d ≫ rationalHolomorphicFormSheafDifferential X d 0 = 0 := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = 0
  rw [← Functor.map_comp, rationalConstantsToFormsPresheaf_comp_differential, Functor.map_zero]
  rfl

/-- **The unit in degree zero.** Forgetting the rational structure of `ℚ_X ⟶ Ω⁰_ℚ` and applying
the comparison gives `forget ℚ_X ≅ ℚ_X` (`HodgeLadder.Cup.forgetQX`) followed by upstream's
`ℚ_X ⟶ ℂ_X ⟶ Ω⁰`. Exact, no scalar. -/
theorem forget_rationalConstantsToFormsSheaf :
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).map (rationalConstantsToFormsSheaf X d) ≫
        (forgetRationalHolomorphicFormSheafIso X d 0).hom =
      (Cup.forgetQX (TopCat.of (ComplexPoint X))).hom ≫ fieldToComplexConstantSheaf ℚ X ≫
        constantsToHolomorphicDeRhamZeroSheaf X d := by
  have h := (forgetSheafifyNatIso X).inv.naturality (rationalConstantsToFormsPresheaf X d)
  change _ ≫ ((forgetSheafifyNatIso X).app _).inv = _ at h
  rw [forgetRationalHolomorphicFormSheafIso, Iso.symm_hom]
  refine h.trans ?_
  have hQX : (Cup.forgetQX (TopCat.of (ComplexPoint X))).hom =
      (forgetSheafifyNatIso X).inv.app _ ≫ (presheafToSheaf (Cup.J _) AddCommGrpCat.{0}).map
        ((Functor.compConstIso _ Cup.U).inv.app (ModuleCat.of ℚ ℚ)) := rfl
  rw [hQX]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  congr 1
  change (presheafToSheaf _ _).map _ =
    (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Forms

section Complex

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- `Ω•_ℚ`: the holomorphic de Rham complex of `X(ℂ)` in sheaves of `ℚ`-vector spaces, indexed by
the integers, `Ω^p_ℚ` in degree `p ≥ 0` and zero in negative degrees; charts use `dim X.left`,
as upstream's `Ω•(X)`. -/
def rationalDeRhamComplex : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ :=
  (rationalHolomorphicDeRhamComplexNat X (dim X.left)).extend ComplexShape.embeddingUpNat

/-- `Ω•_ℚ` is zero in negative degrees. -/
instance rationalDeRhamComplex_isStrictlyGE : (rationalDeRhamComplex X).IsStrictlyGE 0 := by
  unfold rationalDeRhamComplex
  infer_instance

/-- `Ω•_ℚ` is zero above the dimension. -/
instance rationalDeRhamComplex_isStrictlyLE :
    (rationalDeRhamComplex X).IsStrictlyLE (dim X.left) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    have hn0 : 0 ≤ n := by lia
    have hp : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    exact (rationalHolomorphicFormSheaf_isZero_of_lt X (dim X.left)
      (p := n.toNat) (by lia)).of_iso
      ((rationalHolomorphicDeRhamComplexNat X (dim X.left)).extendXIso
        ComplexShape.embeddingUpNat hp)

/-- **`forget(Ω•_ℚ) ≅ Ω•(X)`**: upstream's `mapExtendCanonicalIso`, then the extension of
`forgetRationalHolomorphicDeRhamComplexNatIso`. -/
def forgetRationalDeRhamIso : (forgetComplex X).obj (rationalDeRhamComplex X) ≅ Ω•(X) :=
  HomologicalComplex.mapExtendCanonicalIso (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) _ _ ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (forgetRationalHolomorphicDeRhamComplexNatIso X (dim X.left))

/-- The unit `ℚ_X[0] ⟶ Ω•_ℚ`, with degree-zero component `rationalConstantsToFormsSheaf`. The
source is `rationalUnitComplex X` of rung `rational-hypercohomology-equiv` (an `abbrev` for this
object). -/
def rationalDeRhamUnit :
    (CochainComplex.singleFunctor (Cup.ShQ (TopCat.of (ComplexPoint X))) 0).obj
      (Cup.QX (TopCat.of (ComplexPoint X))) ⟶ rationalDeRhamComplex X :=
  homFromSingleExtend (rationalHolomorphicDeRhamComplexNat X (dim X.left))
    (rationalConstantsToFormsSheaf X (dim X.left)) (by
      rw [rationalHolomorphicDeRhamComplexNat_d]
      exact rationalConstantsToFormsSheaf_comp_differential X _)

/-- **The unit lies over upstream's `fieldToHolomorphicDeRhamComplexInt ℚ X`.** Forgetting the
rational structure of the unit and applying `forgetRationalDeRhamIso` gives the isomorphism
`forget ℚ_X[0] ≅ constantFieldSheafComplexInt ℚ X` followed by upstream's
`ℚ_X[0] ⟶ ℂ_X[0] ⟶ Ω•(X)`. The isomorphism is written out as the composite
`singleMapHomologicalComplex ≪≫ singleFunctor.mapIso forgetQX ≪≫ e.symm`, with
`e = constantFieldSheafComplexIntIsoSingle ℚ X`, that defines `forgetUnitComplexIso` of rung
`rational-hypercohomology-equiv`, so that the statement through `forgetUnitComplexIso` (the
red team's change 8) follows by `exact`. Exact, no scalar. -/
theorem forget_rationalDeRhamUnit_unfolded :
    ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).app _ ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (Cup.forgetQX (TopCat.of (ComplexPoint X))) ≪≫
        (constantFieldSheafComplexIntIsoSingle ℚ X).symm).hom ≫
        fieldToHolomorphicDeRhamComplexInt ℚ X := by
  have hL := mapHomologicalComplex_homFromSingleExtend
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X)))
    (rationalHolomorphicDeRhamComplexNat X (dim X.left)) (rationalConstantsToFormsSheaf X _)
    (by rw [rationalHolomorphicDeRhamComplexNat_d]
        exact rationalConstantsToFormsSheaf_comp_differential X _)
    (forgetRationalHolomorphicDeRhamComplexNatIso X (dim X.left)).hom
  have hR := singleMap_trans_extendSingleIso_hom_comp
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X)))
    (Cup.forgetQX (TopCat.of (ComplexPoint X))) (fieldToComplexConstantSheaf ℚ X)
    (L := holomorphicDeRhamComplex X (dim X.left))
    (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) (by
      rw [holomorphicDeRhamComplex_d]
      exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential X _)
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 2
  exact forget_rationalConstantsToFormsSheaf X _

/-- **The unit lies over upstream's unit, through `forgetUnitComplexIso`** (red team of
`rational-hypercohomology-equiv`, change 8). Exact, no scalar. -/
theorem forget_rationalDeRhamUnit :
    (forgetComplex X).map (rationalDeRhamUnit X) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetUnitComplexIso X).hom ≫ fieldToHolomorphicDeRhamComplexInt ℚ X :=
  forget_rationalDeRhamUnit_unfolded X

/-- `rationalDeRhamUnit` in the shape of upstream's `fieldToHolomorphicDeRhamComplexInt`:
Mathlib's `extendSingleIso`, then the extension of `fromSingle₀Equiv`. -/
theorem rationalDeRhamUnit_eq_extendSingleIso :
    rationalDeRhamUnit X =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          (Cup.QX (TopCat.of (ComplexPoint X))) 0 0 embeddingUpNat_f_zero).inv ≫
        HomologicalComplex.extendMap
          ((CochainComplex.fromSingle₀Equiv (rationalHolomorphicDeRhamComplexNat X (dim X.left))
            (Cup.QX (TopCat.of (ComplexPoint X)))).symm
              ⟨rationalConstantsToFormsSheaf X (dim X.left), by
                rw [rationalHolomorphicDeRhamComplexNat_d]
                exact rationalConstantsToFormsSheaf_comp_differential X _⟩)
          ComplexShape.embeddingUpNat := by
  rw [extendSingleIso_inv_comp_extendMap]
  congr 1

/-- `F^p Ω•_ℚ`: the stupid truncation of `Ω•_ℚ` in degrees `≥ p`, as upstream's
`hodgeFilteredDeRhamComplex X p`. -/
def rationalHodgeFilteredComplex (p : ℤ) :
    CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ :=
  (rationalDeRhamComplex X).stupidTrunc (ComplexShape.embeddingUpIntGE p)

/-- The inclusion `F^p Ω•_ℚ ⟶ Ω•_ℚ`, as upstream's `hodgeFilteredDeRhamInclusion X p`. -/
def rationalHodgeFilteredInclusion (p : ℤ) :
    rationalHodgeFilteredComplex X p ⟶ rationalDeRhamComplex X :=
  HomologicalComplex.stupidTruncInclusion _ _

/-- `forget(F^p Ω•_ℚ) ≅ F^p Ω•(X)`: `mapStupidTruncIso`, then the truncation of
`forgetRationalDeRhamIso`. -/
def forgetRationalHodgeFilteredIso (p : ℤ) :
    (forgetComplex X).obj (rationalHodgeFilteredComplex X p) ≅ F^p Ω•(X) :=
  mapStupidTruncIso (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) _ _ ≪≫
    ((ComplexShape.embeddingUpIntGE p).stupidTruncFunctor _).mapIso (forgetRationalDeRhamIso X)

/-- **The truncations lie over upstream's.** The comparisons carry the inclusion
`F^p Ω•_ℚ ⟶ Ω•_ℚ` to upstream's `hodgeFilteredDeRhamInclusion X p`. -/
theorem forget_rationalHodgeFilteredInclusion (p : ℤ) :
    (forgetComplex X).map (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom =
      (forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p := by
  have h1 := mapStupidTruncIso_inclusion (Cup.forgetSheaf (TopCat.of (ComplexPoint X)))
    (rationalDeRhamComplex X) (ComplexShape.embeddingUpIntGE p)
  have h2 := HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p) (forgetRationalDeRhamIso X).hom
  exact (congrArg (· ≫ (forgetRationalDeRhamIso X).hom) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm))

/-- **Upstream's Hodge filtration through the rational truncation.** `F^p H_dR^n(X)` is the range
of the hypercohomology of `forget(F^p Ω•_ℚ) ⟶ forget(Ω•_ℚ) ≅ Ω•(X)`. -/
theorem hodgeFiltration_eq_range_rational (p n : ℤ) :
    hodgeFiltration X p n = (hypercohomologyMap X ((forgetComplex X).map
      (rationalHodgeFilteredInclusion X p) ≫ (forgetRationalDeRhamIso X).hom) n).range := by
  have h : hypercohomologyMap X ((forgetComplex X).map (rationalHodgeFilteredInclusion X p) ≫
      (forgetRationalDeRhamIso X).hom) n = hypercohomologyMap X
      ((forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p) n :=
    congrArg (hypercohomologyMap X · n) (forget_rationalHodgeFilteredInclusion X p)
  refine Eq.trans ?_ (congrArg AddMonoidHom.range h).symm
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨hypercohomologyMap X (forgetRationalHodgeFilteredIso X p).inv n y, ?_⟩
    refine (hypercohomologyMap_comp_apply X (forgetRationalHodgeFilteredIso X p).inv
      ((forgetRationalHodgeFilteredIso X p).hom ≫ hodgeFilteredDeRhamInclusion X p) n
        y).symm.trans ?_
    exact congrArg (hypercohomologyMap X · n y) (Iso.inv_hom_id_assoc _ _)
  · rintro ⟨y, rfl⟩
    exact ⟨_, (hypercohomologyMap_comp_apply X _ _ n y).symm⟩

end Complex

end HodgeLadder
