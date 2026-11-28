module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainRestriction
public import LefschetzPort.Oka.Topology.Sheaves.Cohomology.Pullback
public import HodgeLadder.Cup.PullbackVariety
public import HodgeLadder.Cup.EndClass
public import HodgeLadder.Cup.SupportedRawMap
public import Other.AlgebraicGeometry.Cohomology.SupportSingularComparison
public import HodgeLadder.General.LocallyConstantSheaf

/-!
# Pullback of sheafified singular cochains

Rung `singular-cochain-pullback` (sub-rung R1 of `supported-pullback-transport`). Upstream's
`singularRestrictionSheaf ℚ f n : 𝒮ⁿ_X ⟶ f_* 𝒮ⁿ_Y` restricts sheafified singular cochains along
any continuous `f : Y ⟶ X` (the file speaks of open embeddings; the map is a bare morphism of
`TopCat`). Its adjoint under `f⁻¹ ⊣ f_*` (Mathlib's `TopCat.Sheaf.pullbackPushforwardAdjunction`)
is the cochain pullback `f⁻¹ 𝒮ⁿ_X ⟶ 𝒮ⁿ_Y`. Here `f⁻¹` is the port's `TopCat.Sheaf.pullbackAb f`.

Three identities, all exact, with no sign and no scalar:

* `singularPullbackSheaf_comm`: the pullback commutes with the singular coboundary.
* `constants_comp_singularPullbackSheaf`: on constants it is the port's
  `pullbackConstantSheafIso f : f⁻¹ ℚ_X ≅ ℚ_Y` followed by the inclusion of constants into
  zero-cochains. The proof transposes both sides under `f⁻¹ ∘ const ⊣ Γ(Y, -)` and compares them
  on the constant section `r`, where upstream's
  `constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward` gives the raw
  identity.
* `iotaQ_comp_singularPullbackInt`: the same square for the integer-indexed resolution
  `iotaQ X : ℚ_X[0] ⟶ 𝒮_X` of rung `end-class-right-mult`, along `g : X' ⟶ X` over `Spec ℂ`.

`constants_comp_singularPullbackSheaf_ne_zero` checks that the constants square is a nonzero map
on every nonempty `Y`.

Instance search does not find `(pullbackAb (pointMap g)).Additive` at the concrete map (the
`TopCat.of` key), so the three exactness facts are stated at a variable map and installed in the
`Variety` section as the named local instances `pointPullbackAdditive`,
`pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits`; a consumer activates
them with `attribute [local instance]`.

`set_option backward.isDefEq.respectTransparency false` is set on five declarations,
`constants_comp_singularPullbackSheaf`, `constants_comp_singularPullbackSheafComplex`,
`constants_comp_singularPullbackSheaf_ne_zero`, `singularPullbackSheaf_zero_ne_zero` and
`singularPullbackInt`: each fails without it at the pin (red team scratch; a local test for
`singularPullbackSheaf_zero_ne_zero`), from the two spellings `TopCat.Sheaf AddCommGrpCat Y`
and `Y.AbSheaf` of one category. `iotaQ_comp_singularPullbackInt` takes about 37 s of kernel time,
unfolding upstream's `iotaQ`.

## Main definitions

* `HodgeLadder.Supported.singularPullbackSheaf`,
  `HodgeLadder.Supported.singularPullbackSheafComplex`
* `HodgeLadder.Supported.singularPullbackInt`
* `HodgeLadder.Supported.PairCocycle`, `HodgeLadder.Supported.RelCochain`: the Hom-complex
  cocycles out of the pair sheaf and the relative singular cochains used by the later sub-rungs

## Main results

* `HodgeLadder.Supported.singularPullbackSheaf_comm`,
  `HodgeLadder.Supported.unit_comp_singularPullbackSheaf`
* `HodgeLadder.Supported.constants_comp_singularPullbackSheaf`,
  `HodgeLadder.Supported.constants_comp_singularPullbackSheaf_ne_zero`,
  `HodgeLadder.Supported.singularPullbackSheaf_zero_ne_zero`
* `HodgeLadder.Supported.iotaQ_comp_singularPullbackInt`
* `HodgeLadder.extendMap_single_square` (general): extending to `ℤ`-degrees a square out of a
  single complex
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology.Singular

namespace HodgeLadder

section Extend

open HomologicalComplex

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]

/-- Extending to `ℤ`-degrees a square out of a single complex: if `F c ≫ φ` agrees in degree zero
with `u ≫ c'`, then the extended maps agree through the single-complex comparison of `F`. -/
theorem extendMap_single_square {A : C} {B : D} {K : CochainComplex C ℕ}
    {L : CochainComplex D ℕ} (c : (CochainComplex.single₀ C).obj A ⟶ K)
    (φ : (F.mapHomologicalComplex _).obj K ⟶ L) (u : F.obj A ⟶ B)
    (c' : (CochainComplex.single₀ D).obj B ⟶ L)
    (h : F.map (c.f 0) ≫ φ.f 0 = F.map (singleObjXSelf (ComplexShape.up ℕ) 0 A).hom ≫ u ≫
      (singleObjXSelf (ComplexShape.up ℕ) 0 B).inv ≫ c'.f 0) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
          extendMap c ComplexShape.embeddingUpNat) ≫
      (mapExtendCanonicalIso F K ComplexShape.embeddingUpNat).hom ≫
        extendMap φ ComplexShape.embeddingUpNat =
    (singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app A ≫
      (single D (ComplexShape.up ℤ) 0).map u ≫
        (extendSingleIso ComplexShape.embeddingUpNat B 0 0 rfl).inv ≫
          extendMap c' ComplexShape.embeddingUpNat := by
  refine (Iso.inv_comp_eq ((singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app A)).mp ?_
  apply from_single_hom_ext
  simp only [comp_f, Functor.mapHomologicalComplex_map_f, Iso.app_inv,
    singleMapHomologicalComplex_inv_app_self,
    extendSingleIso_inv_f ComplexShape.embeddingUpNat A 0 0 rfl,
    extendSingleIso_inv_f ComplexShape.embeddingUpNat B 0 0 rfl,
    extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl,
    mapExtendCanonicalIso_hom_f _ _ ComplexShape.embeddingUpNat (i := 0) (j := 0) rfl,
    single_map_f_self, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]
  rw [reassoc_of% h]
  simp

end Extend

end HodgeLadder

namespace HodgeLadder.Supported

section General

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

/-- **Pullback of sheafified singular cochains** `f⁻¹ 𝒮ⁿ_X ⟶ 𝒮ⁿ_Y`: the adjoint under
`f⁻¹ ⊣ f_*` of upstream's restriction `singularRestrictionSheaf ℚ f n : 𝒮ⁿ_X ⟶ f_* 𝒮ⁿ_Y`. -/
def singularPullbackSheaf (n : ℕ) :
    (TopCat.Sheaf.pullbackAb f).obj (singularCochainSheaf ℚ X n) ⟶ singularCochainSheaf ℚ Y n :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv _ _).symm
    (singularRestrictionSheaf ℚ f n)

/-- The defining property of `singularPullbackSheaf`: its image under `f_*` after the unit is
upstream's restriction. -/
theorem unit_comp_singularPullbackSheaf (n : ℕ) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app _ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map (singularPullbackSheaf f n) =
    singularRestrictionSheaf ℚ f n :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The cochain pullback commutes with the coboundary**, exactly. -/
theorem singularPullbackSheaf_comm (n : ℕ) :
    (TopCat.Sheaf.pullbackAb f).map (singularCochainSheafCoboundary ℚ X n) ≫
      singularPullbackSheaf f (n + 1) =
    singularPullbackSheaf f n ≫ singularCochainSheafCoboundary ℚ Y n := by
  have h := (singularRestrictionSheafComplex ℚ f).comm n (n + 1)
  rw [singularCochainSheafComplex_d, Functor.mapHomologicalComplex_obj_d,
    singularCochainSheafComplex_d] at h
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv_naturality_left_symm
    _ _).symm.trans ((congrArg _ h.symm).trans
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv_naturality_right_symm
        _ _))

set_option backward.isDefEq.respectTransparency false in
/-- **The constants pin.** On constants, the cochain pullback is `f⁻¹ ℚ_X ≅ ℚ_Y` (the port's
`pullbackConstantSheafIso`, the `leftAdjointUniq` of `f⁻¹ ∘ const ⊣ Γ(Y, -)` against
`const ⊣ Γ(Y, -)`) followed by the inclusion of constants into zero-cochains. Exact: no sign, no
scalar. -/
theorem constants_comp_singularPullbackSheaf :
    (TopCat.Sheaf.pullbackAb f).map (constantsToSingularCochainZeroSheaf ℚ X) ≫
      singularPullbackSheaf f 0 =
    (TopCat.Sheaf.pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ) ≫
      constantsToSingularCochainZeroSheaf ℚ Y := by
  let adjC := TopCat.Sheaf.pullbackConstantSheafAdj f
  let A := AddCommGrpCat.of ℚ
  have hR : adjC.homEquiv A _ ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app A ≫
      constantsToSingularCochainZeroSheaf ℚ Y) =
      (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
        ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat).obj (op ⊤)).map
          (constantsToSingularCochainZeroSheaf ℚ Y) :=
    (adjC.homEquiv_naturality_right _ _).trans
      (congrArg (· ≫ _) (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _))
  have hL : adjC.homEquiv A _ ((TopCat.Sheaf.pullbackAb f).map
      (constantsToSingularCochainZeroSheaf ℚ X) ≫ singularPullbackSheaf f 0) =
      (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)).map
          (constantsToSingularCochainZeroSheaf ℚ X ≫ singularRestrictionSheaf ℚ f 0) := by
    simp only [adjC, TopCat.Sheaf.pullbackConstantSheafAdj, Adjunction.comp_homEquiv]
    rw [singularPullbackSheaf, ← Adjunction.homEquiv_naturality_left_symm]
    exact (congrArg ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}
      isTerminalTop).homEquiv _ _) (Equiv.apply_symm_apply _ _)).trans
        (Adjunction.homEquiv_unit _ _ _ _)
  apply (adjC.homEquiv _ _).injective
  rw [hL, hR]
  ext r
  change (singularRestrictionSheaf ℚ f 0).hom.app (op ⊤)
      ((constantsToSingularCochainZeroSheaf ℚ X).hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op ⊤) r)) =
    (constantsToSingularCochainZeroSheaf ℚ Y).hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology Y) ((Functor.const _).obj A)).app (op ⊤) r)
  have h1 := toSheafify_naturality (Opens.grothendieckTopology X)
    (constantsToSingularCochainZero ℚ X)
  have h2 := toSheafify_naturality (Opens.grothendieckTopology Y)
    (constantsToSingularCochainZero ℚ Y)
  have h3 := toSheafify_comp_singularRestrictionSheaf ℚ f 0
  have h4 := constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward ℚ f
  have e1 := (ConcreteCategory.congr_hom (NatTrans.congr_app h1 (op ⊤)) r).symm
  have e2 := (ConcreteCategory.congr_hom (NatTrans.congr_app h2 (op ⊤)) r).symm
  have e3 := ConcreteCategory.congr_hom (NatTrans.congr_app h3 (op ⊤))
    ((constantsToSingularCochainZero ℚ X).app (op ⊤) r)
  have e4 := ConcreteCategory.congr_hom (NatTrans.congr_app h4 (op ⊤)) r
  refine (congrArg _ e1).trans (e3.trans ?_)
  refine (congrArg _ e4).trans ?_
  exact e2.symm

/-- The pullback of singular cochain sheaves as a map of `ℕ`-graded complexes,
`f⁻¹ 𝒮•_X ⟶ 𝒮•_Y`, with components `singularPullbackSheaf`. -/
def singularPullbackSheafComplex :
    ((TopCat.Sheaf.pullbackAb f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (singularCochainSheafComplex ℚ X) ⟶ singularCochainSheafComplex ℚ Y where
  f n := singularPullbackSheaf f n
  comm' i j hij := by
    obtain rfl := hij
    change _ = (TopCat.Sheaf.pullbackAb f).map ((singularCochainSheafComplex ℚ X).d i (i + 1)) ≫ _
    rw [singularCochainSheafComplex_d, singularCochainSheafComplex_d]
    exact (singularPullbackSheaf_comm f i).symm

set_option backward.isDefEq.respectTransparency false in
/-- `constants_comp_singularPullbackSheaf` in the degree-zero form of complexes out of `ℚ_X[0]`. -/
theorem constants_comp_singularPullbackSheafComplex :
    (TopCat.Sheaf.pullbackAb f).map ((constantsToSingularCochainSheafComplex ℚ X).f 0) ≫
      (singularPullbackSheafComplex f).f 0 =
    (TopCat.Sheaf.pullbackAb f).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 𝓒(X; ℚ)).hom ≫
      (TopCat.Sheaf.pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 𝓒(Y; ℚ)).inv ≫
          (constantsToSingularCochainSheafComplex ℚ Y).f 0 :=
  (constants_comp_singularPullbackSheaf f).trans (by
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      constantsToSingularCochainSheafComplex])

/-- `f⁻¹` is additive, stated at a variable map so that it can be installed at a concrete one. -/
theorem pullbackAb_additive : (TopCat.Sheaf.pullbackAb f).Additive := inferInstance

/-- `f⁻¹` preserves finite limits, stated at a variable map. -/
theorem pullbackAb_preservesFiniteLimits : PreservesFiniteLimits (TopCat.Sheaf.pullbackAb f) :=
  inferInstance

/-- `f⁻¹` preserves finite colimits, stated at a variable map. -/
theorem pullbackAb_preservesFiniteColimits : PreservesFiniteColimits (TopCat.Sheaf.pullbackAb f) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- **Non-vacuity.** On a nonempty `Y` the constants square of
`constants_comp_singularPullbackSheaf` is a nonzero map: `ℚ_Y` has the nonzero constant
section `1`, and the inclusion of constants into zero-cochains is a monomorphism. -/
theorem constants_comp_singularPullbackSheaf_ne_zero [Nonempty Y] :
    (TopCat.Sheaf.pullbackAb f).map (constantsToSingularCochainZeroSheaf ℚ X) ≫
      singularPullbackSheaf f 0 ≠ 0 := by
  rw [constants_comp_singularPullbackSheaf]
  intro h
  have h0 : (constantsToSingularCochainZeroSheaf ℚ Y : (𝓒(Y; ℚ) : TopCat.AbSheaf Y) ⟶
      (singularCochainSheaf ℚ Y 0 : TopCat.AbSheaf Y)) = 0 := by
    rw [← cancel_epi ((TopCat.Sheaf.pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ)), h,
      comp_zero]
  have hm : Mono (constantsToSingularCochainZeroSheaf ℚ Y : (𝓒(Y; ℚ) : TopCat.AbSheaf Y) ⟶
      (singularCochainSheaf ℚ Y 0 : TopCat.AbSheaf Y)) :=
    constantsToSingularCochainZeroSheaf_mono ℚ Y
  have hid : (𝟙 (𝓒(Y; ℚ) : TopCat.AbSheaf Y)) = 0 :=
    (cancel_mono (constantsToSingularCochainZeroSheaf ℚ Y : (𝓒(Y; ℚ) : TopCat.AbSheaf Y) ⟶
      (singularCochainSheaf ℚ Y 0 : TopCat.AbSheaf Y))).mp (by rw [h0, comp_zero, zero_comp])
  obtain ⟨y⟩ := ‹Nonempty Y›
  let x := (toSheafify (Opens.grothendieckTopology Y)
    ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℚ))).app (op ⊤) (1 : ℚ)
  have hx : x = 0 :=
    congrArg (fun φ : (𝓒(Y; ℚ) : TopCat.AbSheaf Y) ⟶ 𝓒(Y; ℚ) => φ.hom.app (op ⊤) x) hid
  have hc := congrArg ((constantSheafIsoLocallyConstantSheaf Y ℚ).hom.hom.app (op ⊤)) hx
  rw [constantSheafIsoLocallyConstantSheaf_hom_app_toSheafify, map_zero] at hc
  have hc' : (LocallyConstant.const (⊤ : Opens Y) (1 : ℚ) : LocallyConstant (⊤ : Opens Y) ℚ) = 0 :=
    hc
  have := DFunLike.congr_fun hc' (⟨y, trivial⟩ : (⊤ : Opens Y))
  simp at this

set_option backward.isDefEq.respectTransparency false in
/-- On a nonempty `Y` the degree-zero cochain pullback is a nonzero map. -/
theorem singularPullbackSheaf_zero_ne_zero [Nonempty Y] :
    (singularPullbackSheaf f 0 : (TopCat.Sheaf.pullbackAb f).obj (singularCochainSheaf ℚ X 0) ⟶
      singularCochainSheaf ℚ Y 0) ≠ 0 := by
  intro h
  apply constants_comp_singularPullbackSheaf_ne_zero f
  rw [h]
  exact comp_zero

end General

section Variety

open AlgebraicGeometry ComplexPoint HodgeLadder.Cup

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

/-- `pullbackAb_additive` installed at `pointMap g`, where instance search misses it. -/
local instance pointPullbackAdditive : (TopCat.Sheaf.pullbackAb (pointMap g)).Additive :=
  pullbackAb_additive _

/-- `pullbackAb_preservesFiniteLimits` installed at `pointMap g`. -/
local instance pointPullbackPreservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullbackAb (pointMap g)) :=
  pullbackAb_preservesFiniteLimits _

/-- `pullbackAb_preservesFiniteColimits` installed at `pointMap g`. -/
local instance pointPullbackPreservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Sheaf.pullbackAb (pointMap g)) :=
  pullbackAb_preservesFiniteColimits _

set_option backward.isDefEq.respectTransparency false in
/-- **The cochain pullback in integer degrees**, `g⁻¹ 𝒮_X ⟶ 𝒮_{X'}` on the resolutions extended
by zero, along `g : X' ⟶ X` over `Spec ℂ`: upstream's `mapExtendCanonicalIso` followed by the
extension of `singularPullbackSheafComplex (pointMap g)`. -/
def singularPullbackInt :
    ((TopCat.Sheaf.pullbackAb (pointMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (singularCochainSheafComplexInt X ℚ) ⟶ singularCochainSheafComplexInt X' ℚ :=
  (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.pullbackAb (pointMap g))
      (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap (singularPullbackSheafComplex (pointMap g))
      ComplexShape.embeddingUpNat

/-- **The constants pin in integer degrees.** Along `g`, the pullback of the resolution
`iotaQ X : ℚ_X[0] ⟶ 𝒮_X` is `iotaQ X'` after `g⁻¹ (ℚ_X[0]) ≅ (g⁻¹ ℚ_X)[0]` (Mathlib's
`mapCochainComplexSingleFunctor`) and `g⁻¹ ℚ_X ≅ ℚ_{X'}`. Exact: no sign, no scalar. -/
theorem iotaQ_comp_singularPullbackInt :
    ((TopCat.Sheaf.pullbackAb (pointMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (iotaQ X) ≫ singularPullbackInt g =
    ((TopCat.Sheaf.pullbackAb (pointMap g)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map
        ((TopCat.Sheaf.pullbackConstantSheafIso (pointMap g)).hom.app (AddCommGrpCat.of ℚ)) ≫
      iotaQ X' :=
  extendMap_single_square (TopCat.Sheaf.pullbackAb (pointMap g)) _ _ _ _
    (constants_comp_singularPullbackSheafComplex (pointMap g))

/-- Hom-complex cocycles of degree `n` from the pair sheaf `ℤ[X, X ∖ Z]` in degree zero to the
integer-indexed singular cochain sheaves: the cocycles naming supported classes. -/
abbrev PairCocycle (X : Over (Spec ↧ℂ)) (Z : Closeds (ComplexPoint X)) (n : ℕ) :=
  CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj
      (TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
    (singularCochainSheafComplexInt X ℚ) n

/-- Degree-`p` relative singular cochains of the pair `(X(ℂ), X(ℂ) ∖ Z)`, in abelian groups. -/
abbrev RelCochain (X : Over (Spec ↧ℂ)) (Z : Closeds (ComplexPoint X)) (p : ℕ) :=
  (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.X (p : ℤ)

end Variety

end HodgeLadder.Supported
