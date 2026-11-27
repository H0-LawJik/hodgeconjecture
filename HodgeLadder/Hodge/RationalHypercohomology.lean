module

public import HodgeLadder.Cup.ExtBridge
public import HodgeLadder.Cup.RationalExtHom
public import HodgeLadder.Cup.Product
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import HodgeLadder.Cup.SheafExact
public import HodgeLadder.Cup.SheafTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Rational hypercohomology as morphisms in the derived category of rational sheaves

Rung `rational-hypercohomology-equiv` (front `cup`, first sub-rung of `cup-hodge-filtration`,
red team finding 9). For a complex `C` of sheaves of `ℚ`-vector spaces on `X(ℂ)`, upstream's
hypercohomology `ℍ^n(X; forget C)` of the underlying complex of sheaves of abelian groups is
`Hom(ℚ_X[0], C[n])` in the derived category of sheaves of `ℚ`-vector spaces. The equivalence is
the derived form of the exact adjunction `ℚ ⊗ − ⊣ forget` (the complex version of Mathlib's
`Adjunction.extEquiv`), followed by `ℚ ⊗ ℤ_X ≅ ℚ_X` (`HodgeLadder.Cup.tensorQSheafInt`).

Instance spellings (recorded in `docs/sketches/cup-hodge-filtration.md`, section
"rational-hypercohomology-equiv: statement"): upstream's `HasDerivedCategory` and `HasExt.{0}`
instances are local, so they are repeated here; the instances of `HodgeLadder.Cup` are not found
by instance search at `TopCat.of (ComplexPoint X)` and are given as explicit terms; the forgetful
functor exists in two spellings, `forgetComplex` (target `AnalyticAdditiveSheaf X`, used in the
statements) and `forgetComplexSite` (target sheaves on the site of opens, used in the
construction), which are definitionally equal.

A consumer working at `X(ℂ)` activates the local instances with upstream's `implicit_reducible`
attributes (as at the top of this file) and

```
attribute [local instance] HodgeLadder.rhHasDerivedCategory HodgeLadder.rhSiteHasDerivedCategory
  HodgeLadder.rhHasExt HodgeLadder.rhQHasDerivedCategory HodgeLadder.rhTensorAdditive
  HodgeLadder.rhForgetAdditive HodgeLadder.rhTensorPFL HodgeLadder.rhTensorPFC
  HodgeLadder.rhForgetPFL HodgeLadder.rhForgetPFC
```

(add `HodgeLadder.catCommSqTensor HodgeLadder.catCommSqForget` to work with `adjDerived`).

## Main definitions

* `CategoryTheory.Adjunction.mapCochainComplex`: an adjunction on cochain complexes, degreewise
* `HodgeLadder.adjComplex`, `HodgeLadder.adjDerived`: `ℚ ⊗ − ⊣ forget` on complexes and on
  derived categories
* `HodgeLadder.rationalHypercohomologyEquiv`
* `HodgeLadder.unitHypercohomologyEquiv`: upstream's `ℍ^n(X; forget ℚ_X[0]) ≃+ H^n(X; ℚ)`

## Main results

* `HodgeLadder.adjDerived_commShift`: the derived adjunction commutes with shifts
* `HodgeLadder.rationalHypercohomologyEquiv_naturality`,
  `HodgeLadder.rationalHypercohomologyEquiv_map`: naturality in the complex
* `HodgeLadder.unitHypercohomologyEquiv_hom`: the unit side as a composite in the derived category
* `HodgeLadder.rationalHypercohomologyEquiv_rationalUnitComplex`: agreement with
  `HodgeLadder.Cup.rationalExtEquiv` on `ℚ_X[0]`, exact, no scalar
* `HodgeLadder.rationalHypercohomologyEquiv_one`: the unit goes to the identity of `ℚ_X[0]`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Localization AlgebraicGeometry ComplexPoint TopologicalSpace

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- Upstream's derived category of sheaves of abelian groups on `X(ℂ)` (upstream's instance is
local; this is the same term). -/
local instance rhHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The same instance, for the site spelling of the category. -/
local instance rhSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  rhHasDerivedCategory X

/-- Upstream's local `HasExt.{0}` instance, repeated. -/
local instance rhHasExt : HasExt.{0} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  inferInstance

/-- The derived category of sheaves of `ℚ`-vector spaces on `X(ℂ)`. -/
local instance rhQHasDerivedCategory :
    HasDerivedCategory (Cup.ShQ (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

/-- Forgetting the rational structure, on complexes. -/
abbrev forgetComplex :
    CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ ⥤
      CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `ℚ_X[0]`. -/
abbrev rationalUnitComplex : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (Cup.QX (TopCat.of (ComplexPoint X)))

/-- An adjunction between additive functors gives an adjunction on cochain complexes, degreewise. -/
def _root_.CategoryTheory.Adjunction.mapCochainComplex {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    [Preadditive 𝒜] [Preadditive ℬ] {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜} [F.Additive] [G.Additive]
    (adj : F ⊣ G) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⊣ G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K L =>
        { toFun := fun φ =>
            { f := fun i => adj.homEquiv _ _ (φ.f i)
              comm' := fun i j _ => by
                dsimp
                rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
                congr 1
                exact φ.comm i j }
          invFun := fun ψ =>
            { f := fun i => (adj.homEquiv _ _).symm (ψ.f i)
              comm' := fun i j _ => by
                dsimp
                rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
                congr 1
                exact ψ.comm i j }
          left_inv := fun φ => by ext i; simp
          right_inv := fun ψ => by ext i; simp }
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp [adj.homEquiv_naturality_left_symm]
      homEquiv_naturality_right := by
        intros
        ext
        simp [adj.homEquiv_naturality_right] }

section CommShift

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Preadditive 𝒜] [Preadditive ℬ]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜} [F.Additive] [G.Additive] (adj : F ⊣ G)

/-- The unit of `Adjunction.mapCochainComplex`, in degree `i`. -/
@[simp]
lemma _root_.CategoryTheory.Adjunction.mapCochainComplex_unit_app_f (K : CochainComplex 𝒜 ℤ)
    (i : ℤ) : (adj.mapCochainComplex.unit.app K).f i = adj.unit.app (K.X i) := by
  simp [Adjunction.mapCochainComplex, Adjunction.homEquiv_unit]

/-- The counit of `Adjunction.mapCochainComplex`, in degree `i`. -/
@[simp]
lemma _root_.CategoryTheory.Adjunction.mapCochainComplex_counit_app_f (L : CochainComplex ℬ ℤ)
    (i : ℤ) : (adj.mapCochainComplex.counit.app L).f i = adj.counit.app (L.X i) := by
  simp [Adjunction.mapCochainComplex, Adjunction.homEquiv_counit]

/-- `Adjunction.mapCochainComplex` commutes with shifts (the shift isomorphisms of
`mapHomologicalComplex` are identities in each degree). -/
instance _root_.CategoryTheory.Adjunction.mapCochainComplex_commShift :
    adj.mapCochainComplex.CommShift ℤ :=
  Adjunction.CommShift.mk' _ _ ⟨fun n => by
    ext K i
    simp [Functor.commShiftIso_comp_hom_app]⟩

end CommShift

section Exact

variable (Y : TopCat.{0})

/-- `ℚ ⊗ −` on sheaves is right exact (a left adjoint), stated for a general space so that it can
be instantiated by hand. -/
theorem tensorQSheaf_preservesFiniteColimits : PreservesFiniteColimits (Cup.tensorQSheaf Y) :=
  inferInstance

/-- Forgetting the rational structure of sheaves is left exact. -/
theorem forgetSheaf_preservesFiniteLimits : PreservesFiniteLimits (Cup.forgetSheaf Y) :=
  inferInstance

end Exact

section Derived

/- Instance search does not find the instances of `HodgeLadder.Cup` for the space
`TopCat.of (ComplexPoint X)`: the candidates list for `(Cup.tensorQSheaf _).Additive` omits
`Cup.tensorQSheaf_additive`. The instances are given here as explicit terms. -/
/-- Explicit instance: `ℚ ⊗ −` is additive. -/
local instance rhTensorAdditive : (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).Additive :=
  Cup.tensorQSheaf_additive _
/-- Explicit instance: forgetting is additive. -/
local instance rhForgetAdditive : (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).Additive :=
  Cup.forgetSheaf_additive _
/-- Explicit instance: `ℚ ⊗ −` is left exact. -/
local instance rhTensorPFL :
    PreservesFiniteLimits (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) :=
  Cup.tensorQSheaf_preservesFiniteLimits _
/-- Explicit instance: `ℚ ⊗ −` is right exact. -/
local instance rhTensorPFC :
    PreservesFiniteColimits (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) :=
  tensorQSheaf_preservesFiniteColimits _
/-- Explicit instance: forgetting is left exact. -/
local instance rhForgetPFL : PreservesFiniteLimits (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) :=
  forgetSheaf_preservesFiniteLimits _
/-- Explicit instance: forgetting is right exact. -/
local instance rhForgetPFC :
    PreservesFiniteColimits (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) :=
  Cup.forgetSheaf_preservesFiniteColimits _

/-- `ℚ ⊗ −` on complexes. -/
abbrev tensorQComplex :
    CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat.{0}) ℤ ⥤ CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ :=
  (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Forgetting the rational structure, on complexes, with target spelled as sheaves on the site of
opens (the spelling of `Cup.forgetSheaf`). -/
abbrev forgetComplexSite :
    CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ ⥤
      CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) ℤ :=
  (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The adjunction `ℚ ⊗ − ⊣ forget` on complexes. -/
def adjComplex : tensorQComplex X ⊣ forgetComplexSite X :=
  (Cup.adjQSheaf (TopCat.of (ComplexPoint X))).mapCochainComplex

/-- `ℚ ⊗ −` on complexes descends to `F.mapDerivedCategory`. -/
local instance catCommSqTensor :
    CatCommSq (tensorQComplex X) DerivedCategory.Q DerivedCategory.Q
      (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory :=
  ⟨(Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.symm⟩

/-- Forgetting on complexes descends to `G.mapDerivedCategory`. -/
local instance catCommSqForget :
    CatCommSq (forgetComplexSite X) DerivedCategory.Q DerivedCategory.Q
      (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory :=
  ⟨(Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.symm⟩

/-- The adjunction `ℚ ⊗ − ⊣ forget` on derived categories. -/
def adjDerived : (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory ⊣
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory :=
  (adjComplex X).localization DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    DerivedCategory.Q (HomologicalComplex.quasiIso _ _) _ _

/-- The adjunction on complexes commutes with shifts. -/
instance adjComplex_commShift : (adjComplex X).CommShift ℤ :=
  Adjunction.mapCochainComplex_commShift _

/-- Its unit commutes with shifts. -/
instance adjComplex_unit_commShift : NatTrans.CommShift (adjComplex X).unit ℤ :=
  Adjunction.CommShift.commShift_unit

/-- **The derived adjunction commutes with shifts**: its unit is the lift of the unit on
complexes, which commutes with shifts degreewise. -/
instance adjDerived_commShift : (adjDerived X).CommShift ℤ := by
  apply Adjunction.CommShift.mk'
  change NatTrans.CommShift (Adjunction.Localization.ε (adjComplex X) DerivedCategory.Q
    (HomologicalComplex.quasiIso _ _) DerivedCategory.Q _ _) ℤ
  unfold Adjunction.Localization.ε
  let : Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      ((tensorQComplex X ⋙ forgetComplexSite X) ⋙ DerivedCategory.Q)
      ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory ⋙
        (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory) :=
    Lifting.mk (CatCommSq.hComp (tensorQComplex X) (forgetComplexSite X) DerivedCategory.Q
      DerivedCategory.Q DerivedCategory.Q _ _).iso.symm
  have : NatTrans.CommShift (Lifting.iso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      ((tensorQComplex X ⋙ forgetComplexSite X) ⋙ DerivedCategory.Q)
      ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory ⋙
        (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory)).hom ℤ := by
    dsimp only [Lifting.iso, Iso.symm_hom]
    have : NatTrans.CommShift (CatCommSq.hComp (tensorQComplex X) (forgetComplexSite X)
        DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
        (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory
        (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory).iso.hom ℤ := by
      change NatTrans.CommShift ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (tensorQComplex X)
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) ℤ
      infer_instance
    exact NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (F₁ := DerivedCategory.Q)
      (F₂ := (tensorQComplex X ⋙ forgetComplexSite X) ⋙ DerivedCategory.Q)
      (Functor.whiskerRight (adjComplex X).unit DerivedCategory.Q) ℤ := ⟨fun n => by
    ext K
    have h := NatTrans.shift_app_comm (adjComplex X).unit n K
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      Category.id_comp] at h ⊢
    rw [← Functor.commShiftIso_hom_naturality, h]
    simp only [Functor.map_comp, Category.assoc]⟩
  exact NatTrans.CommShift.liftNatTrans _ _ _ _ _ _ _ _

/-- Postcomposition with an isomorphism, as an additive bijection of morphism groups. -/
@[simps]
def isoPostcompAddEquiv {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {A B B' : 𝒞} (e : B ≅ B') : (A ⟶ B) ≃+ (A ⟶ B') where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := Preadditive.add_comp _ _ _ _ _ _

/-- Precomposition with an isomorphism, as an additive bijection of morphism groups. -/
@[simps]
def isoPrecompAddEquiv {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {A A' B : 𝒞} (e : A ≅ A') : (A' ⟶ B) ≃+ (A ⟶ B) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := Preadditive.comp_add _ _ _ _ _ _

/-- Upstream's hypercohomology as morphisms in the derived category, additively. -/
def hyperAddEquiv (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    ℍ^n(X; K) ≃+ ShiftedHom (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
      (DerivedCategory.Q.obj K) n :=
  { SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q with
    map_add' := hypercohomologyEquiv_add X K n }

/-- Upstream's `ℤ_X[0]`, with its category spelled as sheaves on the site of opens. -/
abbrev intUnitSite : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) ℤ :=
  constantIntegerSheafComplexInt X

/-- `hyperAddEquiv` for the underlying complex of a rational complex, with the derived category
spelled on the site of opens. -/
def hyperAddEquivSite (C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ) (n : ℤ) :
    ℍ^n(X; (forgetComplex X).obj C) ≃+ ShiftedHom (DerivedCategory.Q.obj (intUnitSite X))
      (DerivedCategory.Q.obj ((forgetComplexSite X).obj C)) n :=
  hyperAddEquiv X ((forgetComplex X).obj C) n

/-- Upstream's `ℤ_X[0] ≅ (ULift ℤ)_X[0]` (`constantIntegerSheafComplexIntIsoSingleULift`), with
both sides spelled on the site of opens. -/
abbrev intUnitIsoSingle : intUnitSite X ≅ (CochainComplex.singleFunctor _ 0).obj
    (Cup.constAb (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of (ULift.{0} ℤ))) :=
  constantIntegerSheafComplexIntIsoSingleULift X

/-- `ℚ ⊗ ℤ_X[0] ≅ ℚ_X[0]` on complexes. -/
def tensorUnitComplexIso :
    (tensorQComplex X).obj (intUnitSite X) ≅ rationalUnitComplex X :=
  (tensorQComplex X).mapIso (intUnitIsoSingle X) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (Cup.tensorQSheafInt (TopCat.of (ComplexPoint X)))

/-- The source comparison in the derived category of rational sheaves. -/
def sourceIso : DerivedCategory.Q.obj (rationalUnitComplex X) ≅
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (intUnitSite X)) :=
  DerivedCategory.Q.mapIso (tensorUnitComplexIso X).symm ≪≫
    ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.app _).symm

/-- The target comparison in the derived category of sheaves of abelian groups. -/
def targetIso (C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ) (n : ℤ) :
    (DerivedCategory.Q.obj ((forgetComplexSite X).obj C))⟦n⟧ ≅
      (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.obj
        ((DerivedCategory.Q.obj C)⟦n⟧) :=
  (shiftFunctor _ n).mapIso
      ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.app C).symm ≪≫
    (((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso n).app
      (DerivedCategory.Q.obj C)).symm

/-- **Rational hypercohomology** (rung `rational-hypercohomology-equiv`). For a complex `C` of
sheaves of `ℚ`-vector spaces on `X(ℂ)`, upstream's hypercohomology of the underlying complex of
sheaves of abelian groups is `Hom(ℚ_X[0], C[n])` in the derived category of sheaves of
`ℚ`-vector spaces, through the exact adjunction `ℚ ⊗ − ⊣ forget` and `ℚ ⊗ ℤ_X ≅ ℚ_X`. -/
def rationalHypercohomologyEquiv
    (C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ) (n : ℤ) :
    ℍ^n(X; (forgetComplex X).obj C) ≃+
      ShiftedHom (DerivedCategory.Q.obj (rationalUnitComplex X)) (DerivedCategory.Q.obj C) n :=
  (hyperAddEquivSite X C n).trans <|
    (isoPostcompAddEquiv (targetIso X C n)).trans <|
      ((adjDerived X).homAddEquiv _ _).symm.trans (isoPrecompAddEquiv (sourceIso X))

/-- `hyperAddEquiv` carries upstream's `hypercohomologyMap` to postcomposition. -/
lemma hyperAddEquiv_map {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (g : K ⟶ L) (n : ℤ)
    (x : ℍ^n(X; K)) :
    hyperAddEquiv X L n (hypercohomologyMap X g n x) =
      hyperAddEquiv X K n x ≫ (DerivedCategory.Q.map g)⟦n⟧' := by
  change SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (x.comp (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl g) (zero_add n)) = _
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀]
  rfl

/-- Naturality of the target comparison. -/
lemma targetIso_naturality {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ}
    (f : C ⟶ C') (n : ℤ) :
    (DerivedCategory.Q.map ((forgetComplexSite X).map f))⟦n⟧' ≫ (targetIso X C' n).hom =
      (targetIso X C n).hom ≫
        (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
          ((DerivedCategory.Q.map f)⟦n⟧') := by
  simp only [targetIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc]
  have h1 :=
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at h1
  rw [h1, Functor.map_comp, Category.assoc]
  congr 1
  exact ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso
    n).inv.naturality (DerivedCategory.Q.map f)

/-- `hyperAddEquivSite` carries upstream's `hypercohomologyMap` to postcomposition. -/
lemma hyperAddEquivSite_map {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ}
    (f : C ⟶ C') (n : ℤ) (x : ℍ^n(X; (forgetComplex X).obj C)) :
    hyperAddEquivSite X C' n (hypercohomologyMap X ((forgetComplex X).map f) n x) =
      hyperAddEquivSite X C n x ≫ (DerivedCategory.Q.map ((forgetComplexSite X).map f))⟦n⟧' :=
  hyperAddEquiv_map X _ n x

/-- The equivalence, unfolded. -/
lemma rationalHypercohomologyEquiv_apply
    (C : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ) (n : ℤ)
    (x : ℍ^n(X; (forgetComplex X).obj C)) :
    rationalHypercohomologyEquiv X C n x = (sourceIso X).hom ≫
      ((adjDerived X).homEquiv _ _).symm (hyperAddEquivSite X C n x ≫ (targetIso X C n).hom) :=
  rfl

/-- **Naturality in the complex.** -/
theorem rationalHypercohomologyEquiv_naturality
    {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ} (f : C ⟶ C') (n : ℤ)
    (x : ℍ^n(X; (forgetComplex X).obj C)) :
    rationalHypercohomologyEquiv X C' n (hypercohomologyMap X ((forgetComplex X).map f) n x) =
      (rationalHypercohomologyEquiv X C n x).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map f)) (zero_add n) := by
  simp only [rationalHypercohomologyEquiv_apply]
  rw [ShiftedHom.comp_mk₀]
  have h := hyperAddEquivSite_map X f n x
  have h2 := targetIso_naturality X f n
  simp only [h, Category.assoc, h2]
  simp only [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]

/-- Naturality in the complex, as postcomposition with the shifted map. -/
theorem rationalHypercohomologyEquiv_map
    {C C' : CochainComplex (Cup.ShQ (TopCat.of (ComplexPoint X))) ℤ} (f : C ⟶ C') (n : ℤ)
    (x : ℍ^n(X; (forgetComplex X).obj C)) :
    rationalHypercohomologyEquiv X C' n (hypercohomologyMap X ((forgetComplex X).map f) n x) =
      rationalHypercohomologyEquiv X C n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  rw [rationalHypercohomologyEquiv_naturality, ShiftedHom.comp_mk₀]

/-- An isomorphism of complexes induces an additive bijection on upstream's hypercohomology. -/
@[simps]
def hypercohomologyMapIso {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (e : K ≅ L) (n : ℤ) :
    ℍ^n(X; K) ≃+ ℍ^n(X; L) where
  toFun := hypercohomologyMap X e.hom n
  invFun := hypercohomologyMap X e.inv n
  left_inv x := by
    rw [← hypercohomologyMap_comp_apply, e.hom_inv_id, hypercohomologyMap_id,
      AddMonoidHom.id_apply]
  right_inv x := by
    rw [← hypercohomologyMap_comp_apply, e.inv_hom_id, hypercohomologyMap_id,
      AddMonoidHom.id_apply]
  map_add' := map_add _

/-- The underlying complex of `ℚ_X[0]` is upstream's `ℚ_X[0]`. -/
def forgetUnitComplexIso :
    (forgetComplex X).obj (rationalUnitComplex X) ≅ constantFieldSheafComplexInt ℚ X :=
  (HomologicalComplex.singleMapHomologicalComplex
      (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (Cup.forgetQX (TopCat.of (ComplexPoint X))) ≪≫
    (constantFieldSheafComplexIntIsoSingle ℚ X).symm

/-- Upstream's identification of the hypercohomology of the underlying complex of `ℚ_X[0]` with
`H^n(X; ℚ)`. -/
def unitHypercohomologyEquiv (n : ℕ) :
    ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X)) ≃+ H^n(X; ℚ) :=
  (hypercohomologyMapIso X (forgetUnitComplexIso X) n).trans
    (hypercohomologyAddEquivConstantCohomology ℚ X n)

/-- `hyperAddEquiv_map`, stated with upstream's `SmallShiftedHom.equiv`. -/
lemma equiv_hypercohomologyMap {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (g : K ⟶ L)
    (n : ℤ) (x : ℍ^n(X; K)) :
    SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (hypercohomologyMap X g n x) =
      SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q x ≫
        (DerivedCategory.Q.map g)⟦n⟧' :=
  hyperAddEquiv_map X g n x

set_option maxHeartbeats 1000000 in
/-- The `Ext` class of the unit side, as a composite in the derived category. -/
lemma unitHypercohomologyEquiv_hom (n : ℕ)
    (x : ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X))) :
    (unitHypercohomologyEquiv X n x).hom =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).inv ≫
        hyperAddEquiv X _ n x ≫
          (DerivedCategory.Q.map ((forgetUnitComplexIso X).hom ≫
            (constantFieldSheafComplexIntIsoSingle ℚ X).hom))⟦(n : ℤ)⟧' := by
  change (hypercohomologyAddEquivConstantCohomology ℚ X n
    (hypercohomologyMap X (forgetUnitComplexIso X).hom n x)).hom = _
  rw [Cup.hyperEquiv_hom_comp, SmallShiftedHom.equiv_mk₀Inv]
  simp only [SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    equiv_hypercohomologyMap, Functor.map_comp, Category.assoc]
  congr 1
  rw [← cancel_epi (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom),
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X) _ _).hom_inv_id

/-- The source comparison on complexes, against upstream's `ULift` isomorphism. -/
lemma tensorUnitComplexIso_inv_comp :
    (tensorUnitComplexIso X).inv ≫ (tensorQComplex X).map (intUnitIsoSingle X).hom =
      (CochainComplex.singleFunctor _ 0).map
          (Cup.tensorQSheafInt (TopCat.of (ComplexPoint X))).inv ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).inv.app _ := by
  rw [Iso.inv_comp_eq]
  simp only [tensorUnitComplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  rw [← Functor.map_comp_assoc (CochainComplex.singleFunctor _ 0), Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The source comparison through Mathlib's `mapDerivedCategorySingleFunctor`. -/
lemma sourceIso_hom_eq :
    (sourceIso X).hom =
      (DerivedCategory.singleFunctor _ 0).map
          (Cup.tensorQSheafInt (TopCat.of (ComplexPoint X))).inv ≫
        ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
          (DerivedCategory.Q.map (intUnitIsoSingle X).inv) := by
  rw [← cancel_mono ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
    (DerivedCategory.Q.map (intUnitIsoSingle X).hom))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  have h1 :=
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv.naturality
    (intUnitIsoSingle X).hom
  have h2 := (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))
    ).mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
      (Cup.constAb (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of (ULift.{0} ℤ)))
  dsimp only [Functor.comp_map] at h1
  dsimp only [Functor.mapCochainComplexSingleFunctor] at h2
  simp only [sourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc]
  rw [← h1, ← Functor.map_comp_assoc, tensorUnitComplexIso_inv_comp, Functor.map_comp,
    Category.assoc, ← h2, Category.assoc, Iso.hom_inv_id_app]
  exact congrArg (fun t => _ ≫ t) (Category.comp_id _)

/-- The derived counit commutes with the shift. -/
lemma adjDerived_counit_shift (Y : DerivedCategory (Cup.ShQ (TopCat.of (ComplexPoint X)))) (n : ℤ) :
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
        (((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso n).inv.app
          Y) ≫ (adjDerived X).counit.app (Y⟦n⟧) =
      ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso n).hom.app
          _ ≫ ((adjDerived X).counit.app Y)⟦n⟧' := by
  rw [Adjunction.shift_counit_app (adjDerived X) n Y, Iso.hom_inv_id_app_assoc]

/-- The counit on complexes at `ℚ_X[0]`. -/
lemma adjComplex_counit_rationalUnitComplex :
    (adjComplex X).counit.app (rationalUnitComplex X) =
      (tensorQComplex X).map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X)))) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app _ ≫
        (CochainComplex.singleFunctor _ 0).map
          ((Cup.adjQSheaf (TopCat.of (ComplexPoint X))).counit.app
            (Cup.QX (TopCat.of (ComplexPoint X)))) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [adjComplex, Adjunction.mapCochainComplex_counit_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
  simp only [Adjunction.counit_naturality_assoc, Functor.id_obj, Iso.hom_inv_id,
    Category.comp_id]


set_option maxHeartbeats 1000000 in
/-- The derived counit at `ℚ_X[0]`, through Mathlib's `mapDerivedCategorySingleFunctor`. -/
lemma adjDerived_counit_rationalUnitComplex :
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
        ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv.app
          (rationalUnitComplex X)) ≫
      (adjDerived X).counit.app (DerivedCategory.Q.obj (rationalUnitComplex X)) =
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X))))) ≫
      ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategorySingleFunctor 0).hom.app
          _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((Cup.adjQSheaf (TopCat.of (ComplexPoint X))).counit.app
            (Cup.QX (TopCat.of (ComplexPoint X)))) := by
  have h := Adjunction.localization_counit_app (adjComplex X) DerivedCategory.Q
    (HomologicalComplex.quasiIso _ _) DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory (rationalUnitComplex X)
  have h3 := (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))
    ).mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).obj (Cup.QX (TopCat.of (ComplexPoint X))))
  dsimp only [Functor.mapCochainComplexSingleFunctor] at h3
  have h3' : ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategorySingleFunctor
      0).hom.app ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).obj
        (Cup.QX (TopCat.of (ComplexPoint X)))) =
      (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app _) := by
    rw [← h3, Iso.hom_inv_id_app_assoc]
  change _ ≫ ((adjComplex X).localization DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    DerivedCategory.Q (HomologicalComplex.quasiIso _ _) _ _).counit.app _ = _
  rw [h]
  change _ ≫ (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
    ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.hom.app
      (rationalUnitComplex X)) ≫
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.hom.app _ ≫ _ = _
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [h3', adjComplex_counit_rationalUnitComplex]
  simp only [Functor.map_comp, Category.assoc]
  have hn :=
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X))))
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rfl

/-- The forgetful image of `ℚ_X[0]` is the single complex on `forget ℚ_X`, with target spelled on
upstream's `AnalyticAdditiveSheaf X`. -/
abbrev forgetUnitSingle : (forgetComplex X).obj (rationalUnitComplex X) ⟶
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
      ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).obj (Cup.QX (TopCat.of (ComplexPoint X)))) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
      (Cup.QX (TopCat.of (ComplexPoint X)))

/-- `forgetUnitComplexIso` followed by upstream's single-complex identification and `forgetQX⁻¹`
is the comparison of single complexes. -/
lemma forgetUnitComplexIso_hom_comp :
    (forgetUnitComplexIso X).hom ≫ (constantFieldSheafComplexIntIsoSingle ℚ X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (Cup.forgetQX (TopCat.of (ComplexPoint X))).inv = forgetUnitSingle X := by
  dsimp only [forgetUnitComplexIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
    (Cup.forgetQX (TopCat.of (ComplexPoint X))).hom ≫
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        (Cup.forgetQX (TopCat.of (ComplexPoint X))).inv = _
  rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _


set_option maxHeartbeats 1000000 in
/-- The unit side composed with `forgetQX⁻¹`. -/
lemma unitHypercohomologyEquiv_hom_forgetQX (n : ℕ)
    (x : ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X))) :
    (unitHypercohomologyEquiv X n x).hom ≫ ((DerivedCategory.singleFunctor _ 0).map
        (Cup.forgetQX (TopCat.of (ComplexPoint X))).inv)⟦(n : ℤ)⟧' =
      DerivedCategory.Q.map (intUnitIsoSingle X).inv ≫ hyperAddEquivSite X _ n x ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X)))))⟦(n : ℤ)⟧' := by
  have hT : (DerivedCategory.Q.map ((forgetUnitComplexIso X).hom ≫
      (constantFieldSheafComplexIntIsoSingle ℚ X).hom))⟦(n : ℤ)⟧' ≫
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (Cup.forgetQX (TopCat.of (ComplexPoint X))).inv))⟦(n : ℤ)⟧' =
      (DerivedCategory.Q.map (forgetUnitSingle X))⟦(n : ℤ)⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, forgetUnitComplexIso_hom_comp]
  rw [unitHypercohomologyEquiv_hom]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  exact congrArg (fun t => _ ≫ _ ≫ t) hT

set_option maxHeartbeats 1000000 in
/-- The target comparison followed by the derived counit, at `ℚ_X[0]`. -/
lemma targetIso_counit (n : ℤ) :
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
        (targetIso X (rationalUnitComplex X) n).hom ≫
      (adjDerived X).counit.app ((DerivedCategory.Q.obj (rationalUnitComplex X))⟦n⟧) =
    (Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.map
        ((DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X)))))⟦n⟧') ≫
      ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso n).hom.app
          _ ≫
      (((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategorySingleFunctor 0).hom.app
          _)⟦n⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map
          ((Cup.adjQSheaf (TopCat.of (ComplexPoint X))).counit.app
            (Cup.QX (TopCat.of (ComplexPoint X)))))⟦n⟧' := by
  simp only [targetIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [adjDerived_counit_shift]
  have key := congrArg (fun f => f⟦n⟧') (adjDerived_counit_rationalUnitComplex X)
  simp only [Functor.map_comp] at key
  have nat := ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso
    n).hom.naturality
      ((Cup.forgetSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategoryFactors.inv.app
        (rationalUnitComplex X))
  have nat2 := ((Cup.tensorQSheaf (TopCat.of (ComplexPoint X))).mapDerivedCategory.commShiftIso
    n).hom.naturality (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Cup.forgetSheaf (TopCat.of (ComplexPoint X))) (ComplexShape.up ℤ) 0).hom.app
            (Cup.QX (TopCat.of (ComplexPoint X)))))
  dsimp only [Functor.comp_map] at nat nat2
  refine ((reassoc_of% nat) _).trans ?_
  refine Eq.trans ?_ ((reassoc_of% nat2) _).symm
  exact congrArg (fun t => _ ≫ t) key

set_option maxHeartbeats 1000000 in
/-- **Agreement with `rationalExtEquiv`, no scalar.** On `C = ℚ_X[0]`, the equivalence is
`HodgeLadder.Cup.rationalExtEquiv` after upstream's identification of `ℍ^n(X; ℚ_X[0])` with
`H^n(X; ℚ)`. Both sides are morphisms `ℚ_X[0] ⟶ ℚ_X[0][n]` in the derived category of sheaves of
`ℚ`-vector spaces; `Ext.hom` lands in this type since Mathlib's `DerivedCategory.singleFunctor _ 0`
is `CochainComplex.singleFunctor _ 0 ⋙ Q` by `Iso.refl`. -/
theorem rationalHypercohomologyEquiv_rationalUnitComplex (n : ℕ)
    (x : ℍ^n(X; (forgetComplex X).obj (rationalUnitComplex X))) :
    rationalHypercohomologyEquiv X (rationalUnitComplex X) n x =
      (Cup.rationalExtEquiv (TopCat.of (ComplexPoint X)) n
        (unitHypercohomologyEquiv X n x)).hom := by
  rw [Cup.rationalExtEquiv_hom, unitHypercohomologyEquiv_hom_forgetQX]
  simp only [rationalHypercohomologyEquiv_apply, Adjunction.homEquiv_counit]
  rw [sourceIso_hom_eq]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ _ ≫ _ ≫ t) (targetIso_counit X n)

/-- The unit goes to the identity of `ℚ_X[0]`, exactly. -/
theorem rationalHypercohomologyEquiv_one :
    rationalHypercohomologyEquiv X (rationalUnitComplex X) ((0 : ℕ) : ℤ)
        ((unitHypercohomologyEquiv X 0).symm (Cup.one X)) =
      ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp) (𝟙 _) := by
  rw [rationalHypercohomologyEquiv_rationalUnitComplex, AddEquiv.apply_symm_apply, Cup.one,
    Cup.oneY, AddEquiv.apply_symm_apply, Cup.oneExt, Abelian.Ext.mk₀_hom,
    CategoryTheory.Functor.map_id]
  rfl

end Derived

end HodgeLadder
