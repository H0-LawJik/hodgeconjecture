module

public import HodgeLadder.Normalization.Germ
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtensionVanishing

/-!
# `cycle-class-germ` without the regularity hypothesis, by local purity

Rung `cycle-class-germ-no-reg` (route R2 of the red team on `analytic-smooth-locus`).

Let `x` be a point of coheight `p` of a smooth integral projective `X` over `ℂ`, with
`Z = cycleComponentAnalyticClosedSupport X x` and `U = cycleComponentSmoothSupportAmbientOpen X x`
(the complement of `Z_sing(ℂ)`). The checked rung `cycle-class-germ` identifies, near a point
`y ∈ e.source ∩ U` of a holomorphic chart `e` adapted to `Z`, upstream's transport of the
supported cycle class `[Z]` with `chartNormalProjectionCoclass` of `e`. This file removes the
hypothesis `y ∈ U` and proves the identity on all of `e.source`. Exact: no sign, no scalar.

Route:

1. Local purity on an open (`singularBoundarySectionCohomology_isZero_of_lt`): for every open `V`,
   cohomology of `V` with supports in `Z_sing(ℂ)` vanishes below degree `2(p + 1)`. Upstream
   proves it at `V = ⊤`, through the nested-support sequence of its singular filtration; the
   general lemmas of the section `General` run that induction on any open `W`, with the last
   term of the sequence identified on `W ⊓ U` (`nestedSupportRestrictionLastComplexIsoOnOpen`,
   built from upstream's `sheafSectionsBetweenOpensOnOpenIso`).
2. Injectivity (`restrict_smoothSupportAmbientOpen_injective`): restriction from `V` to `V ⊓ U`
   is injective on `H^{2p}(·, · ∖ Z; ℚ)`, from the nested-support sequence `Z_sing ⊆ Z` and step
   1 at `n = 2p`, transported to singular cohomology by naturality of upstream's
   `complexSupportInjectiveSectionCohomologyEquiv`.
3. On an open inside `U` a class is determined by its section of `𝓗^{2p}_Z`
   (`supportRelativeCohomologyToSheaf_injective_of_le`), since the lower supported cohomology
   sheaves vanish there.
4. On `e.source ⊓ U` the germs of the two sides agree by `cycle-class-germ`, so the two sections
   agree (`TopCat.Presheaf.section_ext`), and by steps 3 and 2 the two classes agree on
   `e.source`.

Steps 2 to 4 move only equalities through injective maps; no comparison sign enters. Conventions
(`docs/conventions.md`): rows "Local purity on an open", "Complex orientation of ℂ^p",
"Fundamental-class normalization", "Normalization iso against the singular transport",
"Holomorphic adapted chart".

## Main definitions

* `HodgeLadder.Normalization.betweenOpensSectionsIso`,
  `HodgeLadder.Normalization.nestedSupportRestrictionLastComplexIsoOnOpen`: the last term of the
  nested-support sequence on an open `W`, as sections on `W ⊓ U`.

## Main results

* `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass_source`:
  the rung, the identity on `e.source`.
* `HodgeLadder.Normalization.transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted`:
  the `∃ W` form, `cycle-class-germ` without `hyU`.
* `HodgeLadder.Normalization.singularBoundarySectionCohomology_isZero_of_lt`: local purity on
  every open.
* `HodgeLadder.Normalization.restrict_smoothSupportAmbientOpen_injective`: injectivity of
  restriction to `V ⊓ U` in degree `2p`.
* `HodgeLadder.Normalization.supportRelativeCohomologyToSheaf_injective_of_le`: classes on opens
  inside `U` are determined by their sheaf sections.
* `HodgeLadder.Normalization.complexSupportInjectiveSectionCohomologyEquiv_naturality`:
  naturality of upstream's transport under restriction of opens.
* General lemmas on an open `W`: `nestedSupportRestrictionLastComplexIsoOnOpen_g`,
  `nestedSupportRestriction_middle_homology_isZero_onOpen`,
  `homologyMap_sectionComplexRestriction_mono`, `finiteNestedSupport_homology_isZero_onOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology.Singular Topology Filter

namespace HodgeLadder.Normalization

section General

open TopCat.Sheaf

universe u

variable (T : TopCat.{u}) {U V : Opens T} (h : V ≤ U)

/-- Sections on `W` of `j_{U*}(F|_U)` are `F(W ⊓ U)`. -/
def pushforwardSectionsInfIso (U W : Opens T) (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((openRestrictionPushforward T U).obj F).obj.obj (op W) ≅ F.obj.obj (op (W ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U W)))

/-- The identification `pushforwardSectionsInfIso` is natural in the sheaf. -/
@[reassoc]
theorem pushforwardSectionsInfIso_naturality (U W : Opens T)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (f : F ⟶ G) :
    ((openRestrictionPushforward T U).map f).hom.app (op W) ≫
        (pushforwardSectionsInfIso T U W G).hom =
      (pushforwardSectionsInfIso T U W F).hom ≫ f.hom.app (op (W ⊓ U)) :=
  (f.hom.naturality _).symm

include h in
/-- For `V ≤ U`, the opens `W` and `W ⊓ U` have the same image `W ⊓ V` under `j_V`. -/
theorem openRestrictionImage_inf_eq (W : Opens T) :
    openRestrictionImage T V W = openRestrictionImage T V (W ⊓ U) := by
  have h1 : openRestrictionImage T V W = W ⊓ V := by simp
  have h2 : openRestrictionImage T V (W ⊓ U) = W ⊓ U ⊓ V := by simp
  rw [h1, h2, inf_assoc, inf_eq_right.mpr h]


/-- For `V ≤ U`, sections on `W` and on `W ⊓ U` of `j_{V*}(F|_V)` agree: both are `F(W ⊓ V)`. -/
def pushforwardTargetIsoOnOpen (W : Opens T) (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((openRestrictionPushforward T V).obj F).obj.obj (op W) ≅
      ((openRestrictionPushforward T V).obj F).obj.obj (op (W ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (openRestrictionImage_inf_eq T h W)))

/-- The comparison of the two restriction arrows is a presheaf restriction square. -/
theorem pushforwardTargetIsoOnOpen_square (W : Opens T) (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((openRestrictionPushforwardMap T h).app F).hom.app (op W) ≫
        (pushforwardTargetIsoOnOpen T h W F).hom =
      (pushforwardSectionsInfIso T U W F).hom ≫
        ((toOpenRestrictionPushforward T V).app F).hom.app (op (W ⊓ U)) := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

/-- For `V ≤ U` and an open `W`: sections on `W` of `ker(j_{U*}(F|_U) → j_{V*}(F|_V))` are the
sections on `W ⊓ U` of the subsheaf of `F` supported in `X ∖ V`. Both are
`ker(F(W ⊓ U) → F(W ⊓ V))`. At `W = ⊤` this is upstream's `sheafSectionsBetweenOpensGlobalIso`. -/
def betweenOpensSectionsIso (W : Opens T) (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((sheafSectionsBetweenOpens T h).obj F).obj.obj (op W) ≅
      ((sheafSectionsSupportedOutside T V).obj F).obj.obj (op (W ⊓ U)) :=
  sheafSectionsBetweenOpensOnOpenIso T h W F ≪≫
    kernel.mapIso _ _ (pushforwardSectionsInfIso T U W F) (pushforwardTargetIsoOnOpen T h W F)
      (pushforwardTargetIsoOnOpen_square T h W F) ≪≫
    (sheafSectionsSupportedOutsideOnOpenIso T V (W ⊓ U) F).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison preserves the inclusion into sections on `W ⊓ U`. -/
@[reassoc]
theorem betweenOpensSectionsIso_hom_inclusion (W : Opens T) (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (betweenOpensSectionsIso T h W F).hom ≫
        ((sheafSectionsSupportedOutsideInclusion T V).app F).hom.app (op (W ⊓ U)) =
      ((sheafSectionsBetweenOpensInclusion T h).app F).hom.app (op W) ≫
        (pushforwardSectionsInfIso T U W F).hom := by
  rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι T V (W ⊓ U) F]
  simp only [betweenOpensSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, kernel.mapIso_hom, kernel.map,
    kernel.lift_ι]
  rw [sheafSectionsBetweenOpensOnOpenIso_hom_ι_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of `betweenOpensSectionsIso` in the coefficient sheaf. -/
@[reassoc]
theorem betweenOpensSectionsIso_naturality (W : Opens T)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (f : F ⟶ G) :
    (((sheafSectionsBetweenOpens T h).map f).hom.app (op W)) ≫
        (betweenOpensSectionsIso T h W G).hom =
      (betweenOpensSectionsIso T h W F).hom ≫
        (((sheafSectionsSupportedOutside T V).map f).hom.app (op (W ⊓ U))) := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion T V).app G).hom.app (op (W ⊓ U))) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι T V (W ⊓ U) G]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion T V).app G).hom.app
    (op (W ⊓ U)))).1
  rw [Category.assoc, betweenOpensSectionsIso_hom_inclusion]
  have h₁ := congrArg (fun q => q.hom.app (op W))
    ((sheafSectionsBetweenOpensInclusion T h).naturality f)
  have h₂ := congrArg (fun q => q.hom.app (op (W ⊓ U)))
    ((sheafSectionsSupportedOutsideInclusion T V).naturality f)
  change (((sheafSectionsSupportedOutside T V).map f).hom.app (op (W ⊓ U))) ≫
      ((sheafSectionsSupportedOutsideInclusion T V).app G).hom.app (op (W ⊓ U)) =
    ((sheafSectionsSupportedOutsideInclusion T V).app F).hom.app (op (W ⊓ U)) ≫
      f.hom.app (op (W ⊓ U)) at h₂
  change (((sheafSectionsBetweenOpens T h).map f).hom.app (op W)) ≫
      ((sheafSectionsBetweenOpensInclusion T h).app G).hom.app (op W) =
    ((sheafSectionsBetweenOpensInclusion T h).app F).hom.app (op W) ≫
      (((openRestrictionPushforward T U).map f).hom.app (op W)) at h₁
  rw [Category.assoc, h₂, betweenOpensSectionsIso_hom_inclusion_assoc]
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (fun q =>
    ((sheafSectionsBetweenOpensInclusion T h).app F).hom.app (op W) ≫ q)
      (pushforwardSectionsInfIso_naturality T U W f)

/-- `betweenOpensSectionsIso` as a natural isomorphism of functors to abelian groups. -/
def betweenOpensSectionsNatIso (W : Opens T) :
    sheafSectionsBetweenOpens T h ⋙ supportEvaluation T W ≅
      sheafSectionsSupportedOutside T V ⋙ supportEvaluation T (W ⊓ U) :=
  NatIso.ofComponents (betweenOpensSectionsIso T h W)
    (fun f => betweenOpensSectionsIso_naturality T h W f)

/-- **The last term of the nested-support sequence on an open `W`.** For `V ≤ U` and a complex of
sheaves `K`, the third complex of `nestedSupportRestrictionSectionsComplexShortComplex T h W K`
is the complex of sections on `W ⊓ U` of `K` with supports in `X ∖ V`. At `W = ⊤` this is
upstream's `nestedSupportRestrictionLastComplexIso`. -/
def nestedSupportRestrictionLastComplexIsoOnOpen (W : Opens T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex T h W K).X₃ ≅
      ((supportEvaluation T (W ⊓ U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafSectionsSupportedOutside T V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (NatIso.mapHomologicalComplex (betweenOpensSectionsNatIso T h W) (ComplexShape.up ℤ)).app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The last map of the nested-support sequence on `W`, under `betweenOpensSectionsIso`, is
restriction of supported sections from `W` to `W ⊓ U`. -/
@[reassoc]
theorem toSheafSectionsBetweenOpens_comparison_onOpen (W : Opens T)
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((toSheafSectionsBetweenOpens T h).app F).hom.app (op W) ≫
        (betweenOpensSectionsIso T h W F).hom =
      ((sheafSectionsSupportedOutside T V).obj F).obj.map
        (homOfLE (inf_le_left : W ⊓ U ≤ W)).op := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion T V).app F).hom.app (op (W ⊓ U))) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι T V (W ⊓ U) F]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion T V).app F).hom.app
    (op (W ⊓ U)))).1
  rw [Category.assoc, betweenOpensSectionsIso_hom_inclusion]
  have hι := ((sheafSectionsSupportedOutsideInclusion T V).app F).hom.naturality
    (homOfLE (inf_le_left : W ⊓ U ≤ W)).op
  rw [hι, ← Category.assoc]
  have hg : ((toSheafSectionsBetweenOpens T h).app F).hom.app (op W) ≫
      ((sheafSectionsBetweenOpensInclusion T h).app F).hom.app (op W) =
    ((sheafSectionsSupportedOutsideInclusion T V).app F).hom.app (op W) ≫
      ((toOpenRestrictionPushforward T U).app F).hom.app (op W) := by
    change (((toSheafSectionsBetweenOpens T h).app F) ≫
      ((sheafSectionsBetweenOpensInclusion T h).app F)).hom.app (op W) = _
    simp only [toSheafSectionsBetweenOpens, sheafSectionsBetweenOpensInclusion,
      kernel.map, kernel.lift_ι]
    rfl
  rw [hg, Category.assoc]
  congr 1
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The last-complex identification on `W` carries the last map of the nested-support sequence
to restriction of section complexes from `W` to `W ⊓ U`. At `W = ⊤` this is upstream's
`nestedSupportRestrictionLastComplexIso_g`. -/
@[reassoc]
theorem nestedSupportRestrictionLastComplexIsoOnOpen_g (W : Opens T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex T h W K).g ≫
        (nestedSupportRestrictionLastComplexIsoOnOpen T h W K).hom =
      sectionComplexRestriction T (ComplexShape.up ℤ)
        (((sheafSectionsSupportedOutside T V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (homOfLE (inf_le_left : W ⊓ U ≤ W)) := by
  ext n : 1
  exact toSheafSectionsBetweenOpens_comparison_onOpen T h W (K.X n)

include h in
/-- **Nested supports on an open `W`.** For `V ≤ U` and a termwise flasque complex `K`, vanishing
of `H^n` of sections on `W` supported in `X ∖ U`, and of sections on `W ⊓ U` supported in
`X ∖ V`, gives vanishing of `H^n` of sections on `W` supported in `X ∖ V`. At `W = ⊤` this is
upstream's `nestedSupportRestriction_middle_homology_isZero`. -/
theorem nestedSupportRestriction_middle_homology_isZero_onOpen (W : Opens T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hsmall : IsZero ((((supportEvaluation T W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafSectionsSupportedOutside T U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K)).homology n))
    (hlayer : IsZero ((((supportEvaluation T (W ⊓ U)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((sheafSectionsSupportedOutside T V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K)).homology n)) :
    IsZero ((((supportEvaluation T W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafSectionsSupportedOutside T V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K)).homology n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex T h W K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque T h W K hK
  have hlast : IsZero (S.X₃.homology n) := hlayer.of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (nestedSupportRestrictionLastComplexIsoOnOpen T h W K))
  exact (hS.homology_exact₂ n).isZero_X₂
    (hsmall.eq_zero_of_src _) (hlast.eq_zero_of_tgt _)

include h in
/-- **Restriction is injective when the smaller support vanishes.** For `V ≤ U` and a termwise
flasque complex `K`, if `H^n` of sections on `W` supported in `X ∖ U` vanishes, then restriction
from `W` to `W ⊓ U` is a monomorphism on `H^n` of sections supported in `X ∖ V`. -/
theorem homologyMap_sectionComplexRestriction_mono (W : Opens T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hsmall : IsZero ((((supportEvaluation T W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafSectionsSupportedOutside T U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K)).homology n)) :
    Mono (HomologicalComplex.homologyMap (sectionComplexRestriction T (ComplexShape.up ℤ)
      (((sheafSectionsSupportedOutside T V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (homOfLE (inf_le_left : W ⊓ U ≤ W))) n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex T h W K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque T h W K hK
  have hg : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g (hsmall.eq_zero_of_src _)
  have hc : Mono (HomologicalComplex.homologyMap
      (S.g ≫ (nestedSupportRestrictionLastComplexIsoOnOpen T h W K).hom) n) := by
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  exact (congrArg (fun f => HomologicalComplex.homologyMap f n)
    (nestedSupportRestrictionLastComplexIsoOnOpen_g T h W K)) ▸ hc

/-- **A finite filtration of supports on an open `W`.** For an increasing sequence of opens
`O 0 ≤ … ≤ O N = ⊤` and a termwise flasque complex `K`, if `H^n` of sections on `W ⊓ O (k + 1)`
supported in `X ∖ O k` vanishes for every `k < N`, then `H^n` of sections on `W` supported in
`X ∖ O k` vanishes for every `k ≤ N`. At `W = ⊤` this is upstream's
`finiteNestedSupport_homology_isZero`. -/
theorem finiteNestedSupport_homology_isZero_onOpen (W : Opens T)
    (O : ℕ → Opens T) (hO : Monotone O) (N : ℕ) (hN : O N = ⊤)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hlayer : ∀ k, k < N → IsZero
      ((((supportEvaluation T (W ⊓ O (k + 1))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafSectionsSupportedOutside T (O k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)).homology n))
    (k : ℕ) (hk : k ≤ N) :
    IsZero ((((supportEvaluation T W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafSectionsSupportedOutside T (O k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K)).homology n) := by
  induction hk using Nat.decreasingInduction with
  | self =>
      rw [hN]
      exact supportedSections_top_homology_isZero T W K n
  | of_succ k hk ih =>
      exact nestedSupportRestriction_middle_homology_isZero_onOpen T
        (hO (Nat.le_succ k)) W K hK n ih (hlayer k (by omega))

end General

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

section Purity

/-- **Layer vanishing on an open.** On `V ⊓ (X ∖ S_{k+1})`, cohomology with supports in the
`k`-th closed set `S_k` of upstream's singular filtration of `Z` vanishes below degree
`2(p + 1)`. Upstream's `cycleComponentSingularLayerSectionCohomology_isZero_of_lt` is the case
`V = ⊤`; the proof is the same, from upstream's cofinal local vanishing. -/
theorem singularLayerSectionCohomology_isZero_of_lt (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (k : ℕ) (V : Opens (ComplexPoint X)) (n : ℤ)
    (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (V ⊓ (cycleComponentSingularAnalyticClosedFiltration X x
        (k + 1)).compl)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (complexSupportInjectiveComplex X
            (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j ↦ TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X))
      (cycleComponentSingularAnalyticClosedFiltration X x k).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V' hyV' ↦
      cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x hx k j (hj.trans_lt hn) y hy.2 V' hyV'

/-- **Purity along the singular filtration, on an open.** On every open `V`, cohomology with
supports in `S_k` vanishes below degree `2(p + 1)`, for every `k` up to the filtration length.
Upstream proves the case `V = ⊤` (private
`cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt`). -/
theorem singularFiltrationSectionCohomology_isZero_of_lt (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (V : Opens (ComplexPoint X)) (k : ℕ)
    (hk : k ≤ cycleComponentSingularFiltrationLength X x) (n : ℤ)
    (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  let O (j : ℕ) := (cycleComponentSingularAnalyticClosedFiltration X x j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (cycleComponentSingularAnalyticClosedFiltration_antitone X x hab hyb)
  have hN : O (cycleComponentSingularFiltrationLength X x) = ⊤ := by
    dsimp only [O]
    rw [cycleComponentSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X))) ↔ y ∈ Set.univ
    simp
  exact finiteNestedSupport_homology_isZero_onOpen
    (TopCat.of (ComplexPoint X)) V O hO (cycleComponentSingularFiltrationLength X x) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => singularLayerSectionCohomology_isZero_of_lt X x hx j V n hn) k hk

/-- **Route R2, local purity.** For every open `V` of `X(ℂ)`, cohomology of `V` with supports in
`Z_sing(ℂ)` (upstream's `cycleComponentSingularAnalyticClosedFiltration X x 0`) vanishes below
degree `2(p + 1)`, in upstream's supported injective model. Upstream proves the case `V = ⊤`
(private `cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`); here `⊤` is replaced by
`V` through the nested-support sequence on an open
(`nestedSupportRestriction_middle_homology_isZero_onOpen`). No sign or scalar: a vanishing. -/
theorem singularBoundarySectionCohomology_isZero_of_lt (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (V : Opens (ComplexPoint X)) (n : ℤ)
    (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) :=
  singularFiltrationSectionCohomology_isZero_of_lt X x hx V 0 (Nat.zero_le _) n hn

end Purity

section Transport

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- **Naturality of upstream's transport.** Upstream's
`complexSupportInjectiveSectionCohomologyEquiv X S V n` (supported injective model to
`H^n(V, V ∖ S; ℚ)`) commutes with restriction from `V` to a smaller open `W`: restriction of
section complexes on one side, pullback along the inclusion of pairs on the other. No sign. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_naturality (S : Closeds (ComplexPoint X))
    {V W : Opens (ComplexPoint X)} (a : W ⟶ V) (n : ℕ)
    (z : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X S)).homology (n : ℤ)) :
    complexSupportInjectiveSectionCohomologyEquiv X S W n
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X))
            (ComplexShape.up ℤ) (complexSupportInjectiveComplex X S) a) (n : ℤ) z) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set (ComplexPoint X)))
          (V := (V : Set (ComplexPoint X))) (leOfHom a) (S : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X S V n z) := by
  let Y := TopCat.of (ComplexPoint X)
  let eV := complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  let eW := complexSupportedSingularInjectiveHomologyIso X S.compl W (n : ℤ)
  have hsq : eV.hom ≫ HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
        (complexSupportInjectiveComplex X S) a) (n : ℤ) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
          (supportedRationalSingularCochainComplex Y S.compl) a) (n : ℤ) ≫ eW.hom := by
    change HomologicalComplex.homologyMap _ _ ≫ _ = _ ≫ HomologicalComplex.homologyMap _ _
    refine (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      (Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ _))
    exact congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ))
      (((TopCat.Sheaf.supportEvaluationRestriction Y a).mapHomologicalComplex _).naturality _)
  have hinv : eW.inv (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
        (complexSupportInjectiveComplex X S) a) (n : ℤ) z) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
          (supportedRationalSingularCochainComplex Y S.compl) a) (n : ℤ) (eV.inv z) := by
    have h1 := congrArg (fun t => eW.inv (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
        (complexSupportInjectiveComplex X S) a) (n : ℤ) t)) (Iso.inv_hom_id_apply eV z).symm
    have h2 := congrArg eW.inv (ConcreteCategory.congr_hom hsq (eV.inv z))
    exact h1.trans (h2.trans (Iso.hom_inv_id_apply eW _))
  change supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed W n
      (eW.inv _) =
    relativeCohomologyMap ℚ n _
      (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed V n
        (eV.inv z))
  rw [hinv]
  exact supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality Y S S.isClosed
    a n _

/-- **Route R2, step 2.** On every open `V`, restriction from `V` to
`V ⊓ (X(ℂ) ∖ Z_sing(ℂ))` is injective on `H^{2p}(·, · ∖ Z; ℚ)`. From
`singularBoundarySectionCohomology_isZero_of_lt` at `n = 2p` and the nested-support sequence
`Z_sing ⊆ Z` on `V` (`homologyMap_sectionComplexRestriction_mono`), transported to singular
cohomology by `complexSupportInjectiveSectionCohomologyEquiv_naturality`. -/
theorem restrict_smoothSupportAmbientOpen_injective (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (V : Opens (ComplexPoint X)) :
    Function.Injective (relativeCohomologyMap ℚ (2 * p)
      (neighborhoodSupportInclusionPairMap
        (W := ((V ⊓ cycleComponentSmoothSupportAmbientOpen X x : Opens (ComplexPoint X)) :
          Set (ComplexPoint X)))
        (V := (V : Set (ComplexPoint X))) (fun _ h => h.1)
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))) := by
  let Y := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  have hZU : Z.compl ≤ U := cycleComponentSupportComplement_le_smoothAmbientOpen X x
  have hmono := homologyMap_sectionComplexRestriction_mono Y hZU V
    (ambientRationalInjectiveComplex X) (fun j => TopCat.Sheaf.injective_isFlasque _ _)
    ((2 * p : ℕ) : ℤ)
    (singularBoundarySectionCohomology_isZero_of_lt X x hx V _ (by push_cast; omega))
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction Y (ComplexShape.up ℤ)
        (complexSupportInjectiveComplex X Z) (homOfLE (inf_le_left : V ⊓ U ≤ V)))
      ((2 * p : ℕ) : ℤ)) :=
    (AddCommGrpCat.mono_iff_injective _).mp hmono
  intro a b hab
  apply (complexSupportInjectiveSectionCohomologyEquiv X Z V (2 * p)).symm.injective
  apply hinj
  apply (complexSupportInjectiveSectionCohomologyEquiv X Z (V ⊓ U) (2 * p)).injective
  rw [complexSupportInjectiveSectionCohomologyEquiv_naturality,
    complexSupportInjectiveSectionCohomologyEquiv_naturality, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  exact hab

/-- **Route R2, step 3.** On an open `W` inside `X(ℂ) ∖ Z_sing(ℂ)`, a class in
`H^{2p}(W, W ∖ Z; ℚ)` is determined by its section of the sheaf `𝓗^{2p}_Z`: below degree `2p` the
supported cohomology sheaves vanish on `W` (upstream's
`cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing`), so the canonical map
to sections is the lowest-degree isomorphism (`openRestrictedLowestSectionCohomologyIso_hom`),
and upstream's `complexSupportInjectiveCohomologySheafIsoRelative_section_apply` carries it to
the sheafification unit. -/
theorem supportRelativeCohomologyToSheaf_injective_of_le (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) (W : Opens (ComplexPoint X))
    (hW : W ≤ cycleComponentSmoothSupportAmbientOpen X x) :
    Function.Injective ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)).app (op W)) := by
  let Y := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let K := complexSupportInjectiveComplex X Z
  have hK : ∀ j, j < ((2 * p : ℕ) : ℤ) → IsZero ((((W.isOpenEmbedding.sheafPullback
      AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j) :=
    fun j hj => TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections Y K W j
      (fun y hy V' hyV' => cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
        X x hx j (by push_cast at hj; omega) y (hW hy) V' hyV')
  let L := TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso Y W K 0 ((2 * p : ℕ) : ℤ) hK
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque Y Z.compl
      ((ambientRationalInjectiveComplex X).X j))
  have hL : L.hom = TopCat.Sheaf.sectionCohomologyToSheafSection Y K ((2 * p : ℕ) : ℤ) W :=
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom _ _ _ _ _ _ _
  let I := complexSupportInjectiveCohomologySheafIsoRelative X Z (2 * p)
  have hI : Function.Injective (I.hom.hom.app (op W)) :=
    ((TopCat.Sheaf.supportEvaluation Y W).mapIso I).addCommGroupIsoToAddEquiv.injective
  let E := complexSupportInjectiveSectionCohomologyEquiv X Z W (2 * p)
  intro a b hab
  obtain ⟨a', rfl⟩ := E.surjective a
  obtain ⟨b', rfl⟩ := E.surjective b
  have ha := complexSupportInjectiveCohomologySheafIsoRelative_section_apply X Z (2 * p) W a'
  have hb := complexSupportInjectiveCohomologySheafIsoRelative_section_apply X Z (2 * p) W b'
  have h2 := hI (ha.trans (hab.trans hb.symm))
  have h3 : L.hom a' = L.hom b' := by
    rw [hL]
    exact h2
  rw [L.addCommGroupIsoToAddEquiv.injective h3]

end Transport

section Germ

open scoped Manifold ContDiff

/-- The germ form of `cycle-class-germ` at a point of `e.source ∩ U`: the germ at `y` of
upstream's transport of `[Z]` is the germ of `chartNormalProjectionCoclass` of `e`. The first step
of the checked `transport_supportedClass_eq_chartNormalProjectionCoclass`, stated on its own. -/
theorem germ_transport_supportedClass_eq_chartNormalProjectionCoclass (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p) ⊤ y trivial
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
          ⊤ (2 * p)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)
            (cycleComponentSupportedInjectiveClass X x hx))) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
        ⟨e.source, e.open_source⟩ y hy
        (chartNormalProjectionCoclass E p e
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS e.source
          subset_rfl) := by
  by_cases hyZ : y ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))
  · refine (supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
      (U := cycleComponentSmoothSupportAmbientOpen X x) (V := ⊤) le_top y hyU _).symm.trans ?_
    refine (congrArg ((𝓗_[cycleComponentSupport X x]^(2 * p)
      (TopCat.of (ComplexPoint X); ℚ)).presheaf.germ
      (cycleComponentSmoothSupportAmbientOpen X x) y hyU)
        (coclassSection_eq_singular X x hx).symm).trans ?_
    exact germ_coclassSection_eq X x hx e L he hS y hy hyU hyZ
  · exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
        (cycleComponentAnalyticClosedSupport X x).isClosed ⊤ y trivial hyZ _).trans
      (supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p)
        (cycleComponentAnalyticClosedSupport X x).isClosed _ y hy hyZ _).symm

/-- **Rung `cycle-class-germ-no-reg`: `cycle-class-germ` without `hyU`, on the whole source.**
For a holomorphic chart `e` adapted to `Z` (the hypotheses of
`transport_supportedClass_eq_chartNormalProjectionCoclass`, without `hyU`), the restriction to
`e.source` of upstream's transport of the supported cycle class `[Z]` is
`chartNormalProjectionCoclass` of `e` on `e.source`. Exact, no sign and no scalar; conventions
as in `transport_supportedClass_eq_chartNormalProjectionCoclass` (`docs/conventions.md`, rows
"Complex orientation of ℂ^p", "Fundamental-class normalization", "Normalization iso against the
singular transport", "Holomorphic adapted chart", "Local purity on an open").

Route R2 (purity): restriction from `e.source` to `e.source ⊓ U` is injective
(`restrict_smoothSupportAmbientOpen_injective`), a class on `e.source ⊓ U` is determined by its
sheaf section (`supportRelativeCohomologyToSheaf_injective_of_le`), and the germs of the two
sides agree at every point of `e.source ⊓ U` by `cycle-class-germ`. Only equalities are moved
through injective maps, so no comparison sign enters. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_source (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0) :
    relativeCohomologyMap ℚ (2 * p)
        (neighborhoodSupportInclusionPairMap
          (W := e.source)
          (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
        (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
          ⊤ (2 * p)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)
            (cycleComponentSupportedInjectiveClass X x hx))) =
      chartNormalProjectionCoclass E p e
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS e.source
          subset_rfl := by
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := cycleComponentAnalyticClosedSupport X x
  let Vs : Opens (ComplexPoint X) := ⟨e.source, e.open_source⟩
  let U := cycleComponentSmoothSupportAmbientOpen X x
  apply restrict_smoothSupportAmbientOpen_injective X x hx Vs
  apply supportRelativeCohomologyToSheaf_injective_of_le X x hx (Vs ⊓ U) inf_le_right
  apply TopCat.Presheaf.section_ext
  intro y hy
  have h1 := supportRelativeCohomologyGerm_restrict Y Z (2 * p) (U := Vs ⊓ U) (V := Vs)
    inf_le_left y hy
  have h2 := supportRelativeCohomologyGerm_restrict Y Z (2 * p) (U := Vs) (V := ⊤) le_top y hy.1
  have h3 := germ_transport_supportedClass_eq_chartNormalProjectionCoclass X x hx e L he hS y
    hy.1 hy.2
  exact (h1 _).trans ((h2 _).trans (h3.trans (h1 _).symm))

/-- **`cycle-class-germ` without `hyU`, germ form.** For every holomorphic chart adapted to `Z`
and every `y ∈ e.source`, the restriction of upstream's transport of `[Z]` equals
`chartNormalProjectionCoclass` of `e` on an open `W ∋ y` inside `e.source` (here
`W = e.source`). Exact, no sign. One term from
`transport_supportedClass_eq_chartNormalProjectionCoclass_source`. -/
theorem transport_supportedClass_eq_chartNormalProjectionCoclass_of_adapted (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin p → ℂ)))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (Fin (dim X.left) → ℂ))
    (he : e.trans L.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (dim X.left) → ℂ) ω (ComplexPoint X))
    (hS : ∀ z ∈ e.source,
      z ∈ (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) ↔ (e z).2 = 0)
    (y : ComplexPoint X) (hy : y ∈ e.source) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ e.source), y ∈ W ∧
      relativeCohomologyMap ℚ (2 * p)
          (neighborhoodSupportInclusionPairMap
            (W := (W : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
            ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p)
              (cycleComponentSupportedInjectiveClass X x hx))) =
        chartNormalProjectionCoclass E p e
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) hS W hW :=
  ⟨⟨e.source, e.open_source⟩, subset_rfl, hy,
    transport_supportedClass_eq_chartNormalProjectionCoclass_source X x hx e L he hS⟩

end Germ

end HodgeLadder.Normalization
