module

public import HodgeLadder.Supported.PullbackNamed

/-!
# The pulled-back pair cocycle of a relative cochain

Rung `supported-pullback-section` (sub-rung R4 of `supported-pullback-transport`). Let
`g : X' ⟶ X` be a morphism over `Spec ℂ`, `Z ⊆ X(ℂ)` and `Z' ⊆ X'(ℂ)` closed with
`g⁻¹ Z ⊆ Z'`, and `x` a relative singular cocycle of degree `p` on `(X(ℂ), X(ℂ) ∖ Z)`, in
abelian groups. Then the pair cocycle `pullbackCocycle g Z Z' hZ (supCocycle (rawMap x))` of rung
`supported-pullback-named` is `supCocycle (rawMap (relPullback x))`, where `relPullback` is the
pullback of relative cochains along the map of pairs `openPairPullback` given by `g` (upstream's
`relativeDualCochainShortComplexIntMap`, the dual of composition with `g` on singular chains).
Exact, with no sign and no scalar.

Proof. A cocycle out of the pair sheaf `ℤ[Y, Y ∖ Z]` is determined by the value of its
degree-zero component at the generator of `ℤ[Y]` (`pairCocycle_ext`). On the left, the pair map
`ℤ[X', X' ∖ Z'] ⟶ g⁻¹ ℤ[X, X ∖ Z]` sends the generator to the unit of `g⁻¹ ⊣ g_*` applied to the
generator (`gen_supportPairMap`), and the unit followed by `g_*` of the cochain pullback is
upstream's restriction of cochains (`unit_comp_singularPullbackInt`, from
`unit_comp_singularPullbackSheaf` of rung `singular-cochain-pullback`). The generator value of
`supCocycle (rawMap x)` is the sheafification of `x` read as a cochain on `X(ℂ)`
(`gen_supCocycle`). Upstream's `toSheafify_comp_singularRestrictionSheaf` moves the restriction
inside the sheafification, and on raw cochains the restriction along `g` and `relPullback` agree
by definition (`singularRestriction_relPullback`, closed by `rfl` after the comparison of
`relSeq` with upstream's short complex map). No step introduces a factor: the generator goes to
the generator, the unit and the adjunction transpose are identities on the nose, and the cochain
maps on both sides are composition with the same continuous map.

Instances: the named local instances `pointPullbackAdditive`,
`pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits` of
`HodgeLadder.Supported.SingularCochainPullback` and the derived-category instances
`finSiteHasDerivedCategory`, `finHasDerivedCategory` of `HodgeLadder.Cup.SupportedFinal`, as in
`HodgeLadder.Supported.PullbackNamed`. `set_option backward.isDefEq.respectTransparency false`
is set where the `TopCat.Sheaf` and site spellings of one category meet. Kernel type checking
at the pin (`lake env lean -Dprofiler=true`), about 110 s for the file, 82 s of it for
`pullbackCocycle_supCocycle`.

Non-vacuity: `HodgeLadder.Tests.supCocycle_relPullback_prodFst_ne_zero`
(`HodgeLadder.Tests.SupportedPullbackSection`) gives a relative cocycle on ℙ¹(ℂ) whose pulled-back
pair cocycle along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹ has nonzero derived class.

## Main definitions

* `HodgeLadder.Supported.openPairPullback`, `HodgeLadder.Supported.relPullback`

## Main results

* `HodgeLadder.Supported.pullbackCocycle_supCocycle`
* `HodgeLadder.Supported.pairCocycle_ext`, `HodgeLadder.Supported.gen_supportPairMap`,
  `HodgeLadder.Supported.fromSingleEquiv_precomp_map_postcomp`
* `HodgeLadder.Supported.singularPullbackInt_f_sInt_XIso`,
  `HodgeLadder.Supported.unit_comp_singularPullbackInt`,
  `HodgeLadder.Supported.singularRestriction_relPullback`, `HodgeLadder.Supported.gen_supCocycle`
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits TopologicalSpace Opposite Abelian CochainComplex HomComplex
  AlgebraicTopology.Singular

set_option linter.auxLemma false

namespace HodgeLadder.Supported

section General

/-- A Hom-complex cocycle out of the pair sheaf `ℤ[Y, U]` is determined by the value of its
degree-zero component at the generator of `ℤ[Y]`. -/
theorem pairCocycle_ext {Y : TopCat.{0}} (U : Opens Y)
    {K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) ℤ}
    {n : ℤ} (z₁ z₂ : Cocycle ((CochainComplex.singleFunctor _ 0).obj
      (TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq _))) K n)
    (h : CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ (K.X n)
        (cokernel.π _ ≫ Cochain.fromSingleEquiv (zero_add n) z₁.1) =
      CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ (K.X n)
        (cokernel.π _ ≫ Cochain.fromSingleEquiv (zero_add n) z₂.1)) :
    z₁ = z₂ := by
  apply Cocycle.ext
  apply (Cochain.fromSingleEquiv (zero_add n)).injective
  exact (CategoryTheory.Sheaf.pairSheafHomAddEquiv _ _).injective (Subtype.ext h)

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D)
  [F.Additive]

/-- The degree-zero component of a cocycle out of a single complex, mapped by `F`, precomposed
with a map into `F A` and postcomposed with a map of complexes. -/
theorem fromSingleEquiv_precomp_map_postcomp {A : C} {A' : D} {K : CochainComplex C ℤ}
    {L : CochainComplex D ℤ} {n : ℤ} (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) K n)
    (s : A' ⟶ F.obj A) (φ : (F.mapHomologicalComplex _).obj K ⟶ L) :
    Cochain.fromSingleEquiv (zero_add n)
        (((HodgeLadder.ExtMapCocycle.cocycleMap F z).precomp
          ((CochainComplex.singleFunctor _ 0).map s ≫
            (F.mapCochainComplexSingleFunctor 0).inv.app _)).postcomp φ).1 =
      s ≫ F.map (Cochain.fromSingleEquiv (zero_add n) z.1) ≫ φ.f n := by
  simp [Cochain.fromSingleEquiv, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v]

variable {Y Y' : TopCat.{0}} (f : Y' ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- **The pair map on generators.** For `h : ℤ[Y, Y ∖ Z] ⟶ G` and `ψ : f⁻¹ G ⟶ G'`, the
composite `ℤ[Y', Y' ∖ Z'] ⟶ f⁻¹ ℤ[Y, Y ∖ Z] ⟶ f⁻¹ G ⟶ G'` sends the generator to the image of
the section `h(gen)` under the unit of `f⁻¹ ⊣ f_*` followed by `f_* ψ`. -/
theorem gen_supportPairMap (Z : Closeds Y) (Z' : Closeds Y')
    (hZ : Z'.compl ≤ (Opens.map f).obj Z.compl) {G : TopCat.Sheaf AddCommGrpCat Y}
    {G' : TopCat.Sheaf AddCommGrpCat Y'}
    (h : CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology Y)
      (homOfLE (le_top : Z.compl ≤ ⊤)) ⟶ G)
    (ψ : (TopCat.Sheaf.pullbackAb f).obj G ⟶ G') :
    CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ G'
        (cokernel.π _ ≫ supportPairMap f Z Z' hZ ≫ (TopCat.Sheaf.pullbackAb f).map h ≫ ψ) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app G ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map ψ).hom.app (op ⊤)
        (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ G (cokernel.π _ ≫ h)) := by
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit
  have e1 : cokernel.π _ ≫ supportPairMap f Z Z' hZ =
      (CategoryTheory.Sheaf.freeAbelianSheaf _).map (homOfLE (fun _ _ => trivial) :
        (⊤ : Opens Y') ⟶ (Opens.map f).obj ⊤) ≫ freePullback f ⊤ ≫
        (TopCat.Sheaf.pullbackAb f).map (cokernel.π _) := by
    rw [supportPairMap, CategoryTheory.Sheaf.pairSheafMap, ← Category.assoc, cokernel.π_desc,
      Category.assoc, π_pairPullback]
  rw [← Category.assoc, e1]
  simp only [Category.assoc]
  rw [CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_map_comp]
  have hb : (homOfLE (fun _ _ => trivial) : (⊤ : Opens Y') ⟶ (Opens.map f).obj ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hb, op_id]
  erw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [← Functor.map_comp_assoc, CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_comp, freePullback,
    AddEquiv.apply_symm_apply]
  have hη := η.naturality (cokernel.π _ ≫ h)
  have e2 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op ⊤)) hη)
    (CategoryTheory.Sheaf.freeAbelianSheafGenerator (⊤ : Opens Y))
  exact (congrArg (ψ.hom.app (op ((Opens.map f).obj ⊤))) e2).symm

end General

section Variety

open AlgebraicGeometry ComplexPoint HodgeLadder.Cup

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory

/-- The map of open pairs `(X'(ℂ), X'(ℂ) ∖ Z') ⟶ (X(ℂ), X(ℂ) ∖ Z)` given by `g`. -/
def openPairPullback (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') :
    openInclusionPair (TopCat.of (ComplexPoint X')) (Opens.infLELeft ⊤ Z'.compl) ⟶
      openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun y => ⟨pointMap g y.1, trivial⟩,
      ((pointMap g).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun y => ⟨pointMap g y.1,
      ⟨trivial, compl_le_of_preimage_subset g Z Z' hZ y.2.2⟩⟩,
      ((pointMap g).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    rfl

/-- Pullback of relative singular cochains along `openPairPullback`, in abelian groups. -/
def relPullback (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') :
    (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁ ⟶
      (relSeq (TopCat.of (ComplexPoint X')) Z'.compl ⊤).X₁ :=
  ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁

set_option backward.isDefEq.respectTransparency false in
/-- `singularPullbackInt g` in degree `p ≥ 0` is `singularPullbackSheaf` through the degree
identifications `sInt_XIso`. -/
theorem singularPullbackInt_f_sInt_XIso (p : ℕ) :
    (singularPullbackInt g).f (p : ℤ) ≫
        (sInt_XIso (X := TopCat.of (ComplexPoint X')) (rfl : (p : ℤ) = p)).hom =
      (TopCat.Sheaf.pullbackAb (pointMap g)).map
          (sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom ≫
        singularPullbackSheaf (pointMap g) p := by
  simp only [singularPullbackInt, sInt_XIso, HomologicalComplex.comp_f,
    HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ ComplexShape.embeddingUpNat
      (i := p) (j := (p : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit of `g⁻¹ ⊣ g_*` followed by `g_*` of the cochain pullback is upstream's restriction
of cochains, in degree `p ≥ 0`. -/
theorem unit_comp_singularPullbackInt (p : ℕ) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (pointMap g)).unit.app _ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (pointMap g)).map
          ((singularPullbackInt g).f (p : ℤ) ≫
            (sInt_XIso (X := TopCat.of (ComplexPoint X')) (rfl : (p : ℤ) = p)).hom) =
      (sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom ≫
        singularRestrictionSheaf ℚ (pointMap g) p := by
  have hn := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (pointMap g)).unit.naturality
    (sInt_XIso (X := TopCat.of (ComplexPoint X)) (rfl : (p : ℤ) = p)).hom
  rw [singularPullbackInt_f_sInt_XIso, Functor.map_comp, ← Category.assoc]
  erw [← hn]
  rw [Category.assoc, unit_comp_singularPullbackSheaf]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Raw cochains.** Upstream's restriction of raw cochains along `g`, on the cochain of `X(ℂ)`
underlying a relative cochain `x`, is the cochain of `X'(ℂ)` underlying `relPullback x`. -/
theorem singularRestriction_relPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {p : ℕ}
    (x : RelCochain X Z p) :
    (singularRestrictionToRawPushforward ℚ (pointMap g) p).app (op ⊤)
        (((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint X))
          (Opens.infLELeft ⊤ Z.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f p = p)).hom
          ((relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f p x)) =
      ((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint X'))
          (Opens.infLELeft ⊤ Z'.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f p = p)).hom
          ((relSeq (TopCat.of (ComplexPoint X')) Z'.compl ⊤).f.f p
            ((relPullback g Z Z' hZ).f p x)) := by
  let a := (relativeDualCochainShortComplexNatMap ℚ (openPairPullback g Z Z' hZ)).τ₂
  let E := ((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint X))
    (Opens.infLELeft ⊤ Z.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f p = p))
  let E' := ((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint X'))
    (Opens.infLELeft ⊤ Z'.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f p = p))
  have e3 : (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat).f (p : ℤ) ≫ E'.hom =
      E.hom ≫ a.f p := by
    rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl]
    simp only [E', Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have e1 : relPullback g Z Z' hZ ≫ (relSeq (TopCat.of (ComplexPoint X')) Z'.compl ⊤).f =
      (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f ≫
        ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) := by
    have := congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (relativeDualCochainShortComplexIntMap ℚ
        (openPairPullback g Z Z' hZ)).comm₁₂
    simp only [Functor.map_comp] at this
    exact this
  have e2 := ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ)) e1) x
  have e4 := ConcreteCategory.congr_hom e3 ((relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).f.f p x)
  change _ = E'.hom ((relSeq (TopCat.of (ComplexPoint X')) Z'.compl ⊤).f.f p
            ((relPullback g Z Z' hZ).f p x))
  refine Eq.trans ?_ ((congrArg E'.hom.hom e2).trans e4).symm
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The generator value of `supCocycle (rawMap x)`**: the sheafification of the relative cochain
`x`, read as a cochain on `X(ℂ)`. -/
theorem gen_supCocycle (Y : Over (Spec ↧ℂ)) [T2Space (ComplexPoint Y)]
    [∀ U : Opens (ComplexPoint Y), ParacompactSpace U] (Z : Closeds (ComplexPoint Y)) {p : ℕ}
    (x : RelCochain Y Z p)
    (hx : (relSeq (TopCat.of (ComplexPoint Y)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) :
    (sInt_XIso (X := TopCat.of (ComplexPoint Y)) (rfl : (p : ℤ) = p)).hom.hom.app (op ⊤)
        (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ _ (cokernel.π _ ≫
          Cochain.fromSingleEquiv (zero_add (p : ℤ)) (supCocycle Y Z
            ((rawMap (TopCat.of (ComplexPoint Y)) Z.compl ⊤).τ₁.f p x)
            (map_d_eq_zero _ x hx)).1)) =
      (toSheafify (Opens.grothendieckTopology _)
        (singularCochainPresheaf ℚ (TopCat.of (ComplexPoint Y)) p)).app (op ⊤)
        (((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint Y))
          (Opens.infLELeft ⊤ Z.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f p = p)).hom
          ((relSeq (TopCat.of (ComplexPoint Y)) Z.compl ⊤).f.f p x)) := by
  set s₀ := (rawMap (TopCat.of (ComplexPoint Y)) Z.compl ⊤).τ₁.f p x
  set z := supCocycle Y Z s₀ (map_d_eq_zero _ x hx)
  have hes : (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint Y))
      Z.compl ⊤ Z.compl (top_inf_eq _) (sInt (TopCat.of (ComplexPoint Y)))).hom.f (p : ℤ) z.1 =
      s₀ := by
    have h1 := congrArg (fun φ => HomologicalComplex.Hom.f φ (p : ℤ))
      (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint Y)) Z.compl ⊤
        Z.compl (top_inf_eq _) (sInt (TopCat.of (ComplexPoint Y)))).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h1
    exact ConcreteCategory.congr_hom h1 s₀
  have h1 := supportedSection_eq_pairEval' (Y := TopCat.of (ComplexPoint Y)) Z.compl ⊤ Z.compl
    (top_inf_eq _) (rfl : (p : ℤ) = p) (z.1 : Cochain _ (sInt (TopCat.of (ComplexPoint Y))) p)
  have h2 : (sInt_XIso (X := TopCat.of (ComplexPoint Y)) (rfl : (p : ℤ) = p)).hom.hom.app (op ⊤)
      ((supSeq (TopCat.of (ComplexPoint Y)) Z.compl ⊤).f.f (p : ℤ) s₀) =
      (toSheafify (Opens.grothendieckTopology _)
        (singularCochainPresheaf ℚ (TopCat.of (ComplexPoint Y)) p)).app (op ⊤)
        (((relativeDualCochainShortComplexNat ℚ (openInclusionPair (TopCat.of (ComplexPoint Y))
          (Opens.infLELeft ⊤ Z.compl))).X₂.extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f p = p)).hom
          ((relSeq (TopCat.of (ComplexPoint Y)) Z.compl ⊤).f.f p x)) := by
    rw [rawMap_comm₁₂_apply (TopCat.of (ComplexPoint Y))]
    exact rawMapMid_apply (TopCat.of (ComplexPoint Y)) Z.compl ⊤ p _
  rw [← h2, ← hes]
  exact h1.symm

variable [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
  [T2Space (ComplexPoint X')] [∀ U : Opens (ComplexPoint X'), ParacompactSpace U]

set_option backward.isDefEq.respectTransparency false in
/-- **The pulled-back pair cocycle of a relative cochain.** For a relative cocycle `x` on
`(X(ℂ), X(ℂ) ∖ Z)`, the pullback along `g` of the pair cocycle `supCocycle (rawMap x)` is the
pair cocycle `supCocycle (rawMap (relPullback x))` of the pulled-back relative cocycle on
`(X'(ℂ), X'(ℂ) ∖ Z')`. Exact: no sign, no scalar. -/
theorem pullbackCocycle_supCocycle (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {p : ℕ}
    (x : RelCochain X Z p)
    (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) :
    pullbackCocycle g Z Z' hZ (supCocycle X Z
      ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x) (map_d_eq_zero _ x hx)) =
      supCocycle X' Z' ((rawMap (TopCat.of (ComplexPoint X')) Z'.compl ⊤).τ₁.f p
        ((relPullback g Z Z' hZ).f p x)) (map_d_eq_zero _ _ (map_d_eq_zero _ x hx)) := by
  let e' := sInt_XIso (X := TopCat.of (ComplexPoint X')) (rfl : (p : ℤ) = p)
  have he' : Function.Injective (e'.hom.hom.app (op ⊤)) := by
    intro a b hab
    have hl : ∀ c, e'.inv.hom.app (op ⊤) (e'.hom.hom.app (op ⊤) c) = c := fun c =>
      ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op ⊤)) e'.hom_inv_id) c
    rw [← hl a, hab, hl b]
  apply pairCocycle_ext (Y := TopCat.of (ComplexPoint X')) Z'.compl
  apply he'
  refine Eq.trans ?_ (gen_supCocycle X' Z' _ (map_d_eq_zero _ x hx)).symm
  rw [← singularRestriction_relPullback g Z Z' hZ x]
  rw [pullbackCocycle, fromSingleEquiv_precomp_map_postcomp]
  set h := Cochain.fromSingleEquiv (zero_add (p : ℤ)) (supCocycle X Z
    ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x) (map_d_eq_zero _ x hx)).1
  have hA := gen_supportPairMap (pointMap g) Z Z' (compl_le_of_preimage_subset g Z Z' hZ) h
    ((singularPullbackInt g).f p)
  have hU := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op ⊤))
    (unit_comp_singularPullbackInt g p))
    (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ _ (cokernel.π _ ≫ h))
  have hG := gen_supCocycle X Z x hx
  have hR := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_singularRestrictionSheaf ℚ (pointMap g) p) (op ⊤))
  refine (congrArg (e'.hom.hom.app (op ⊤)) hA).trans ?_
  refine hU.trans ?_
  refine (congrArg ((singularRestrictionSheaf ℚ (pointMap g) p).hom.app (op ⊤)) hG).trans ?_
  exact hR _

end Variety

end HodgeLadder.Supported
