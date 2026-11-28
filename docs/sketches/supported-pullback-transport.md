# Sketch: `supported-pullback-transport`

Date 2026-11-27, issue #235, `main` at `5fcf509`, upstream pin `2ead713`. Sub-rung of `fibre-class-pullback`. This is a plan. Nothing below is checked: every identity is a target, and the Lean statements were elaborated with `sorry` in a scratch file (since deleted; about 100 s for all of them).

## Statement

**Plain words.** Let g : X' ⟶ X be a morphism over Spec ℂ, both integral and smooth, with X(ℂ), X'(ℂ) Hausdorff and every open paracompact. Let Z ⊆ X(ℂ), Z' ⊆ X'(ℂ) be closed with g⁻¹ Z ⊆ Z', and α ∈ H^n_Z(X; ℚ). Then the singular class of the supported pullback g^*α in H^n(X', X' ∖ Z'; ℚ) is the pullback, along the map of pairs given by g, of the singular class of α in H^n(X, X ∖ Z; ℚ). Exact, sign +, no scalar. Literature: the comparison H^n_Z(X; A) ≅ H^n(X, X ∖ Z; A), computed by the resolution of A_X by sheafified singular cochains, is natural in continuous maps [`Bredon1997`, ch. III; `Iversen1986`; sections unverified]. Mathlib's f⁻¹ is the left adjoint of pushforward (`TopCat.Sheaf.pullback`, the sheafified presheaf pullback by `TopCat.Sheaf.pullbackIso`), which is the literature's inverse image up to that canonical isomorphism.

**Proposed Lean** (namespace `HodgeLadder.Supported`; `supportedPullback`, `compl_le_of_preimage_subset` from `HodgeLadder.Supported.Pullback`; `supportedEquivPair`, `pointMap`, `pullbackCoh` from `HodgeLadder.Cup`; `neighborhoodSupportPullbackPairMap` from `HodgeLadder.LocalClassPullback`; the instance block of finding 9 of `docs/sketches/supported-class-pullback.redteam.md` on X and X'). The first is finding 9's spelling, the second the ledger note's (pair map at ⊤ against upstream's transport, so `restrict_pullback_eq_chartNormalProjectionCoclass` applies by term), the third the absolute case Z = Z' = ⊤:

```lean
theorem supportedEquivPair_supportedPullback (g : X' ⟶ X) (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X')) (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α) =
      relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha))
        (supportedEquivPair X Z n α)

theorem transport_supportedPullback [IsProjective X.hom] [IsProjective X'.hom] (g : X' ⟶ X) (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X')) (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv X' Z' ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology X' Z' n (supportedPullback g Z Z' hZ n α)) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPullbackPairMap (Point.map g) (Point.continuous_map _)
          (W' := ((⊤ : Opens (ComplexPoint X')) : Set (ComplexPoint X')))
          (W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial) (fun _ _ h => hZ h))
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α))

theorem singular_pullbackCoh (g : X' ⟶ X) (n : ℕ) (β : H^n(X; ℚ)) :
    rationalCohomologyAddEquivSingularCohomology X' n (pullbackCoh g n β) =
      cohomologyMap ℚ n (pointMap g) (rationalCohomologyAddEquivSingularCohomology X n β)
```

## Why the ladder needs it

`supported-class-pullback` pins g^* only through `forgetSupport`, which is injective only for Z' = ⊤ (its red team, finding 4). `fibre-class-pullback` at pr₁ needs g^*[∞]_supp = [{∞} × ℙ¹]_supp with Z' = {∞} × ℙ¹; upstream's normalization reads a supported class through its transport (`normalization_singular`), and `transport_supportedPullback` turns the transport of g^*[∞] into the pullback of the transport of [∞], where `infty_transport_eq_lineAdaptedChart_coclass` and `p1p1Fst_chartNormalProjectionCoclass_pullback` act. Side payoff: since `supportedEquivPair` is an equivalence, `supported-pullback-functorial` (finding 10 there) follows from `relativeCohomologyMap_id` and `relativeCohomologyMap_comp`.

## Proof idea

1. **Cochain pullback.** Upstream's `singularRestrictionSheafComplex ℚ j : 𝒮•_X ⟶ j_* 𝒮•_Y` takes any continuous j (the file speaks of open embeddings; the variable is a bare `j : U ⟶ X`). Its adjoint under `pullbackPushforwardAdjunction` is φ : f⁻¹ 𝒮•_X ⟶ 𝒮•_Y, extended to ℤ-degrees with `mapExtendCanonicalIso`.
2. **Augmentation.** φ ∘ f⁻¹(ℚ_X → 𝒮⁰_X) = (ℚ_Y → 𝒮⁰_Y) ∘ (f⁻¹ ℚ_X ≅ ℚ_Y), the last being the port's `pullbackConstantSheafIso`. Both sides are maps out of a constant sheaf, so compare them on the constant section 1; the raw identity is upstream's `constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward`.
3. **Exact functors and named classes.** For exact F, F.mapDerivedCategory carries the class named by a Hom-complex cocycle z to the class named by z mapped degreewise, through `mapDerivedCategoryFactors`.
4. **Named classes pull back to named classes.** Unfold `supportedPullback` (mk₀ of the pair map, `mapExactFunctor`, mk₀ of the coefficient iso) with `Ext.mapExactFunctor_hom`; with 2 and 3, if α ∘ ι_X is named by z then g^*α ∘ ι_{X'} is named by the transported cocycle.
5. **Section computation.** For z = `supCocycle` of `rawMap x` (`exists_supported_rep`), the transported cocycle is `supCocycle` of `rawMap` of the cochain pullback of x: evaluate at the generator (`freePullback`, `π_pairPullback`, adjunction naturality), then `toSheafify_comp_singularRestrictionSheaf`.
6. **Named class to singular class.** If β ∘ ι is named by `supCocycle (rawMap y)`, then `supportedEquivPair β` is the class of y: the second half of the proof of `exists_supported_rep` (`relHSupportedOfFlasque_mk`) with `supported_singular_class`.
7. **Assembly.** Step 6 on X and on X', upstream's `relativeDualCochainCohomologyEquiv_naturality`, and equal pair maps on points; transport form by `supportedEquivPair_eq_transport` on both sides; absolute case by `forgetSupport_supportedPullback`, `forgetRel_supportedEquivPair`, `forgetRel_relativeCohomologyMap`, `forgetSupport_surjective_of_eq_top`.

f⁻¹ 𝒮•_X need not be flasque: classes on X' are read through Hom-complex cocycles, so the route does not use naturality of upstream's flasque model (finding 9's concern).

## What Mathlib has

Checked by `grep` at the pin. Mathlib: `TopCat.Sheaf.pullbackPushforwardAdjunction`, `TopCat.Sheaf.pushforward`, `Abelian.Ext.mapExactFunctor_hom`, `Abelian.Ext.mapExactFunctor_mk₀`, `Abelian.Ext.mapExactFunctor_comp`, `Functor.mapDerivedCategoryFactors` with its `NatTrans.CommShift` instance, `Functor.mapCochainComplexSingleFunctor`, `Functor.mapCochainComplexShiftIso`, `CochainComplex.HomComplex.Cochain.map`, `CochainComplex.HomComplex.δ_map`, `Cocycle.precomp`, `Cocycle.postcomp`, `Cocycle.equivHomShift_symm_precomp`, `Cocycle.equivHomShift_symm_postcomp`. Upstream: `singularRestrictionToRawPushforward`, `singularRestrictionSheaf`, `singularRestrictionSheafComplex`, `toSheafify_comp_singularRestrictionSheaf`, `globalSingularSheafRestriction_naturality`, `constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward`, `HomologicalComplex.mapExtendCanonicalIso`, `relativeDualCochainShortComplexIntMap`, `relativeDualCochainCohomologyEquiv_naturality`. Port: `TopCat.Sheaf.pullbackAb`, `pullbackConstantSheafIso`. Ladder: `supportPairMap`, `freePullback`, `π_pairPullback`, `terminal_square`, `exists_supported_rep`, `supCocycle`, `rawMap`, `relSeq`, `supported_singular_class`, `relHSupportedOfFlasque_mk`, `pairCohIso_hom_apply`, `supportedEquivPair_eq_transport`, `forgetRel_supportedEquivPair`, `forgetRel_relativeCohomologyMap`.

## What is missing

`Cocycle.map` (Mathlib maps cochains only) and step 3; the sheaf-level augmentation for an arbitrary map (upstream proves it only for `analyticComplementInclusion` against `rationalRestrictionSheaf`); φ itself; steps 4 to 7. Elaboration notes from scratch: instance search fails on `(pullbackAb (pointMap g)).Additive` (the `TopCat.of` key of gaps' instance rows) while the general-`f` instance applies, so state `pullbackAb_additive` (and finite limits, colimits) for a variable map and install them at `pointMap g`; `mapExtendCanonicalIso` at `pullbackAb` needs `set_option backward.isDefEq.respectTransparency false` (category instances of `TopCat.Sheaf` and `AbSheaf`); both `HasDerivedCategory` local instances of `HodgeLadder.Cup.SupportedFinal` are needed.

## Sub-rungs

| id | kind | statement | lines | depends_on | reuses |
|---|---|---|---|---|---|
| `singular-cochain-pullback` (R1) | foundation | φ, its ℤ-extension, the augmentation square | 200 to 300 | none | upstream restriction file; `terminal_square` pattern |
| `ext-map-cocycle` (R2) | foundation | exact functors carry cocycle-named derived maps to cocycle-named maps | 80 to 150 | none | Mathlib commShift API |
| `supported-pullback-named` (R3) | foundation | named α gives named g^*α | 150 to 250 | R1, R2, `supported-class-pullback` | `mapExactFunctor_hom`, `equivHomShift_symm_*` |
| `supported-pullback-section` (R4) | foundation | transported `supCocycle` is `supCocycle` of the cochain pullback | 200 to 350 | R1, R3 | `π_pairPullback`, `toSheafify_comp_singularRestrictionSheaf` |
| `supported-pair-named` (R5) | foundation | named β has the singular class of its cocycle | 60 to 100 | R1 (abbreviations only) | `exists_supported_rep` proof, `supported_singular_class` |
| `supported-pullback-transport` (R6) | foundation | the three statements above | 100 to 180 | R3, R4, R5, `supported-pair-forget` | `relativeDualCochainCohomologyEquiv_naturality` |
| `supported-pullback-transport-test` | test | g^*[∞] ≠ 0 in degree 2 on pr₁ | 30 to 60 | R6, `local-class-pullback-submersion-p1p1` | `p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero` |

Order: R1, R2, R5 in parallel; then R3, R4, R6, the test. **Dispatch R1 first**: it is the input the ledger names, and R3 to R5 use its definitions. Exact statements (all elaborated; `Cup`, `Supported`, `TopCat.Sheaf`, `CochainComplex.HomComplex` open; f : Y ⟶ X in `TopCat.{0}`, g as above; binders shown as `(Z Z' hZ)` carry the types of the main statement, which the scratch spelled out). Test proof: `transport_supportedPullback`, restrict to the two chart sources (`inclusion_comp_pullbackPairMap` is `rfl`), `infty_transport_eq_lineAdaptedChart_coclass`, `p1p1Fst_chartNormalProjectionCoclass_pullback_source_ne_zero`.

```lean
-- R1 (HodgeLadder.Supported.CochainPullback)
def singularPullbackSheaf (n : ℕ) : (pullbackAb f).obj (singularCochainSheaf ℚ X n) ⟶ singularCochainSheaf ℚ Y n :=
  ((pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv _ _).symm (singularRestrictionSheaf ℚ f n)
theorem singularPullbackSheaf_comm (n : ℕ) : (pullbackAb f).map (singularCochainSheafCoboundary ℚ X n) ≫
    singularPullbackSheaf f (n + 1) = singularPullbackSheaf f n ≫ singularCochainSheafCoboundary ℚ Y n
-- singularPullbackSheafComplex f : (f⁻¹).mapHomologicalComplex (up ℕ) of 𝒮•_X ⟶ 𝒮•_Y, components singularPullbackSheaf
theorem constants_comp_singularPullbackSheaf : (pullbackAb f).map (constantsToSingularCochainZeroSheaf ℚ X) ≫
    singularPullbackSheaf f 0 = (pullbackConstantSheafIso f).hom.app (AddCommGrpCat.of ℚ) ≫ constantsToSingularCochainZeroSheaf ℚ Y
def singularPullbackInt : ((pullbackAb (pointMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (singularCochainSheafComplexInt X ℚ) ⟶ singularCochainSheafComplexInt X' ℚ :=
  (HomologicalComplex.mapExtendCanonicalIso (pullbackAb (pointMap g)) (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat).hom ≫ HomologicalComplex.extendMap (singularPullbackSheafComplex (pointMap g)) ComplexShape.embeddingUpNat
theorem iotaQ_comp_singularPullbackInt : ((pullbackAb (pointMap g)).mapHomologicalComplex (ComplexShape.up ℤ)).map (iotaQ X) ≫
    singularPullbackInt g = ((pullbackAb (pointMap g)).mapCochainComplexSingleFunctor 0).hom.app _ ≫ (CochainComplex.singleFunctor _ 0).map ((pullbackConstantSheafIso (pointMap g)).hom.app (AddCommGrpCat.of ℚ)) ≫ iotaQ X'
abbrev PairCocycle (X) (Z : Closeds (ComplexPoint X)) (n : ℕ) := Cocycle ((CochainComplex.singleFunctor (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) 0).obj (pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _))) (singularCochainSheafComplexInt X ℚ) n
abbrev RelCochain (X) (Z : Closeds (ComplexPoint X)) (p : ℕ) := (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.X (p : ℤ)
-- R2 (HodgeLadder.General.ExtMapCocycle), F : C ⥤ D additive and exact, both with derived categories
def cocycleMap (z : Cocycle K L n) : Cocycle ((F.mapHomologicalComplex _).obj K) ((F.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map F) (n + 1) rfl (by rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])
theorem mapDerivedCategory_shiftedHom_cocycle (z : Cocycle K L n) :
    ShiftedHom.map (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) F.mapDerivedCategory =
      F.mapDerivedCategoryFactors.hom.app K ≫ ShiftedHom.map (Cocycle.equivHomShift.symm (cocycleMap F z)) DerivedCategory.Q ≫ (F.mapDerivedCategoryFactors.inv.app L)⟦n⟧'
-- R3 (HodgeLadder.Supported.PullbackNamed)
def pullbackCocycle (Z Z' hZ) (z : PairCocycle X Z n) : PairCocycle X' Z' n :=
  ((cocycleMap (pullbackAb (pointMap g)) z).precomp ((CochainComplex.singleFunctor _ 0).map (supportPairMap (pointMap g) Z Z'
    (compl_le_of_preimage_subset g Z Z' hZ)) ≫ ((pullbackAb (pointMap g)).mapCochainComplexSingleFunctor 0).inv.app _)).postcomp (singularPullbackInt g)
theorem supportedPullback_named (Z Z' hZ) (α : H_[Z]^n(X; ℚ)) (z : PairCocycle X Z n)
    (hα : α.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(n : ℤ)⟧' = ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) :
    (supportedPullback g Z Z' hZ n α).hom ≫ (DerivedCategory.Q.map (iotaQ X'))⟦(n : ℤ)⟧' =
      ShiftedHom.map (Cocycle.equivHomShift.symm (pullbackCocycle g Z Z' hZ z)) DerivedCategory.Q
-- R4 (HodgeLadder.Supported.PullbackSection); openPairPullback g Z Z' hZ : openInclusionPair X'(ℂ) (Opens.infLELeft ⊤ Z'.compl) ⟶ openInclusionPair X(ℂ) (Opens.infLELeft ⊤ Z.compl) is TopPair.ofHom of y ↦ pointMap g y on both parts;
-- relPullback g Z Z' hZ := ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).map (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁
theorem pullbackCocycle_supCocycle (Z Z' hZ) (x : RelCochain X Z p) (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) :
    pullbackCocycle g Z Z' hZ (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p x) (map_d_eq_zero _ x hx)) =
      supCocycle X' Z' ((rawMap (TopCat.of (ComplexPoint X')) Z'.compl ⊤).τ₁.f p ((relPullback g Z Z' hZ).f p x)) (map_d_eq_zero _ _ (map_d_eq_zero _ x hx))
-- R5 (HodgeLadder.Supported.PairNamed), instances on X only
theorem supportedEquivPair_of_named (Z) (β : H_[Z]^p(X; ℚ)) (y : RelCochain X Z p) (hy : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) y = 0)
    (hβ : β.hom ≫ (DerivedCategory.Q.map (iotaQ X))⟦(p : ℤ)⟧' = ShiftedHom.map (Cocycle.equivHomShift.symm
      (supCocycle X Z ((rawMap (TopCat.of (ComplexPoint X)) Z.compl ⊤).τ₁.f p y) (map_d_eq_zero _ y hy))) DerivedCategory.Q) :
    supportedEquivPair X Z p β = relativeCohomologyMap ℚ p (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom
      (relativeDualCochainCohomologyEquiv ℚ (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl)) p
        ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ (openInclusionPair (TopCat.of (ComplexPoint X))
          (Opens.infLELeft ⊤ Z.compl))).X₁.sc p) (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) y hy)))
-- test (HodgeLadder.Tests.SupportedPullbackTransport), with attribute [local instance] p1p1_openParacompactSpace
theorem supportedPullback_fst_infty_ne_zero : supportedPullback (prod.fst : p1p1 ⟶ projectiveLine)
    (cycleComponentAnalyticClosedSupport projectiveLine infty) (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst)
    (fun z hz => (map_fst_mem_infty_support_iff z).mp hz) (2 * 1)
    (cycleComponentSupportedInjectiveClass projectiveLine infty (by rw [Nat.cast_one]; exact coheight_infty)) ≠ 0
```

### A shorter route for the pr₁ consumer?

Compared honestly, none found. (a) Germs only: g^* is defined on Ext and germs live on singular cochains, so any local identity for g^*[∞] still crosses R1 to R4, plus a restriction step. (b) `cycleComponentSupportedInjectiveClass_unique` with the checked germs needs the normalization of g^*[∞], read through the same transport (`normalization_singular`): same crossing. (c) Absolute only: prove `singular_pullbackCoh` directly, then Ψ injective, `forgetRel_supportedEquivPair` on both sides, and g^*Φ[∞] = Φ[{∞} × ℙ¹] in H²(Y, Y ∖ F) by purity injectivity (`restrict_smoothSupportAmbientOpen_injective`, `supportRelativeCohomologyToSheaf_injective_of_le`) and germs. This skips the pair-sheaf generator work of R4 but needs absolute twins of R3 to R5 through hypercohomology and global sections (`globalSections_of_singClass`, `step3_named_class`) and the κ bookkeeping of `pullback-port-agreement`; R1 and R2 stay. Estimated no smaller, and it yields the absolute statement only, which R6 gives in about 60 lines. (d) A pullback-free variant of `cup-positive-degree-test`, [{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] ≠ 0, is checked: `HodgeLadder.Tests.p1p1Fibres_cup_ne_zero` (rung `p1p1-point-class-nonzero`, #221). It is a different statement from `cup-positive-degree-test`, which needs `fibre-class-pullback` to identify pr₁^*[∞] with [{∞} × ℙ¹]; both open rungs stay open.

### Kill criteria

R2 lies on every route: if two prover sessions leave it open, stop and record a decision (consider route (d) for the test). If any of R3 to R6 exceeds 600 s of kernel time (`Supported.Pullback` takes 164 s), split it or state it over `TopCat` with named spaces (finding 12 there). If R4 or R5 closes only with a scalar or a sign, mark this rung refuted with the factor in the note and open the signed rung. Re-plan if the total passes 1500 lines.

### Signs and normalizations

Degree-zero values (`pullbackCoh_one`) exclude −1 in degree 0; the degree-2 test excludes vacuity and leaves an even-degree twist to R2 and R3. Steps and where each possible factor is fixed:

| Step | Possible sign or scalar | Where it cancels or is fixed |
|---|---|---|
| cone identifications inside `supportedRationalSingularSectionCohomologyEquivRelative` | an ε(n) from `shortExactHomologyIsoCone` | entered on X and on X' through `supported_singular_class` (checked, no sign); g acts on relative cocycles only, so a common ε(n) cancels |
| Hom-complex naming (`equivHomShift`, right shift) | sign conventions of shifts | same convention on both sides; R2 transports it exactly (`mapCochainComplexShiftIso` is the identity degreewise, F additive) |
| `mapExactFunctor` | a degree twist ε(n) (red team of `supported-class-pullback`, finding 7) | excluded by R2 and R3 computing the image exactly |
| f⁻¹ ℚ_X ≅ ℚ_Y | any nonzero scalar on connected Y | pinned to 1 by `constants_comp_singularPullbackSheaf` |
| ℤ[Y, Y ∖ Z'] ⟶ f⁻¹ ℤ[X, X ∖ Z] | generator image | generator to generator (`freePullback`), evaluated in R4 |
| transport form | pair isomorphisms | identity on points (`ofSubsetIsoNeighborhoodTop`) |

## Sources

`Bredon1997` (ch. III, sheaf against singular cohomology and its naturality; sections unverified); `Iversen1986` (cohomology with supports and inverse image; chapters unverified); `Hatcher2002` (relative singular cohomology and maps of pairs; section unverified for this use). Declaration names are checked by `grep` at the pin; the literature claims are recalled, unverified.
