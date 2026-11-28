module

public import HodgeLadder.Supported.PullbackSection
public import HodgeLadder.Supported.PairNamed
public import HodgeLadder.Cup.SupportedPairForget
public import HodgeLadder.Local.ClassPullback

/-!
# The supported pullback through the singular transport

Rung `supported-pullback-transport` (sub-rung R6, the closing step of the supported-pullback
transport). Let `g : X' ⟶ X` be a morphism over `Spec ℂ` of integral smooth varieties whose
complex points are Hausdorff with every open paracompact, and let `Z ⊆ X(ℂ)`, `Z' ⊆ X'(ℂ)` be
closed with `g⁻¹ Z ⊆ Z'`. For `α ∈ H^n_Z(X; ℚ)`, the singular class of the supported pullback
`g^*α` in `H^n(X'(ℂ), X'(ℂ) ∖ Z'; ℚ)` is `relativeCohomologyMap` along the map of pairs given by
`g`, applied to the singular class of `α` in `H^n(X(ℂ), X(ℂ) ∖ Z; ℚ)`. Exact, with sign `+` and
no scalar.

Three forms:

* `supportedEquivPair_supportedPullback`, through `supportedEquivPair`, along
  `TopPair.ofSubsetHom (pointMap g) _`;
* `singular_pullbackCoh`, the absolute case `Z = Z' = ⊤`: through
  `rationalCohomologyAddEquivSingularCohomology`, `pullbackCoh g n` is `cohomologyMap ℚ n
  (pointMap g)`;
* `transport_supportedPullback`, for projective `X` and `X'`, through upstream's transport
  `complexSupportInjectiveSectionCohomologyEquiv` at the neighborhood `⊤` on both sides, along
  `neighborhoodSupportPullbackPairMap (Point.map g)` at `⊤`, the form in which
  `restrict_pullback_eq_chartNormalProjectionCoclass` applies by term.

Proof. Choose a relative cocycle `x` naming `α` (`exists_supported_rep`). Rung
`supported-pullback-named` names `g^*α` by `pullbackCocycle g Z Z' hZ (supCocycle (rawMap x))`,
which rung `supported-pullback-section` rewrites to `supCocycle (rawMap (relPullback x))`. Rung
`supported-pair-named` reads both named classes as singular classes of `x` and of
`relPullback x`; `relPullback` is the cochain map of `relativeCohomologyMap` along
`openPairPullback`, so upstream's `relativeDualCochainCohomologyEquiv_naturality` and the
agreement of the two spellings of the map of pairs (`topPairIso_hom_comp_openPairPullback`, by
`rfl` on points) close the identity. Every step is a rewrite by an equality of maps; no step
multiplies by a scalar. The absolute case follows through `forgetSupport` and `forgetRel`
(rung `supported-pair-forget`); the transport form through `supportedEquivPair_eq_transport`
on both sides.

Instances: the named local instances `pointPullbackAdditive`,
`pointPullbackPreservesFiniteLimits`, `pointPullbackPreservesFiniteColimits` of
`HodgeLadder.Supported.SingularCochainPullback` and `finSiteHasDerivedCategory`,
`finHasDerivedCategory` of `HodgeLadder.Cup.SupportedFinal`, as in
`HodgeLadder.Supported.PullbackSection`.

Non-vacuity is rung `supported-pullback-transport-test` (`g^*[∞] ≠ 0` in degree 2 along
pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹), a separate ledger rung.

## Main results

* `HodgeLadder.Supported.supportedEquivPair_supportedPullback`
* `HodgeLadder.Supported.singular_pullbackCoh`
* `HodgeLadder.Supported.transport_supportedPullback`
* `HodgeLadder.Supported.topPairIso_hom_comp_openPairPullback`,
  `HodgeLadder.Supported.mapHomologyIso_cls_relPullback`,
  `HodgeLadder.Supported.transport_eq_supportedEquivPair`
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits TopologicalSpace Opposite Abelian CochainComplex HomComplex
  AlgebraicTopology.Singular AlgebraicGeometry ComplexPoint HodgeLadder.Cup

set_option linter.auxLemma false

namespace HodgeLadder.Supported

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory

/-- The map of open pairs `openPairPullback` given by `g` and the map of subset pairs
`TopPair.ofSubsetHom (pointMap g) _` agree through `topPairIso` on both sides; both are
`y ↦ pointMap g y` on points. -/
theorem topPairIso_hom_comp_openPairPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') :
    (topPairIso (TopCat.of (ComplexPoint X')) Z'.compl).hom ≫ openPairPullback g Z Z' hZ =
      TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha) ≫
        (topPairIso (TopCat.of (ComplexPoint X)) Z.compl).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The homology class of `relPullback x`, read in modules through `mapHomologyIso`, is the
homology map of upstream's `relativeDualCochainShortComplexIntMap` along `openPairPullback`
applied to the class of `x`. -/
theorem mapHomologyIso_cls_relPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z') {p : ℕ}
    (x : RelCochain X Z p)
    (hx : (relSeq (TopCat.of (ComplexPoint X)) Z.compl ⊤).X₁.d (p : ℤ) ((p : ℤ) + 1) x = 0) :
    (ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
        (openInclusionPair (TopCat.of (ComplexPoint X')) (Opens.infLELeft ⊤ Z'.compl))).X₁.sc p)
        (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
        (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) ((relPullback g Z Z' hZ).f p x)
          (map_d_eq_zero _ x hx)) =
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁ p)
        ((ShortComplex.mapHomologyIso ((relativeDualCochainShortComplexInt ℚ
          (openInclusionPair (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ Z.compl))).X₁.sc p)
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
          (cls _ (p : ℤ) ((p : ℤ) + 1) (by simp) x hx)) := by
  rw [relPullback, ← homologyMap_cls _ _ _ _ x hx]
  exact ConcreteCategory.congr_hom (ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ (p : ℤ)).map
      (relativeDualCochainShortComplexIntMap ℚ (openPairPullback g Z Z' hZ)).τ₁)
    (forget₂ (ModuleCat ℚ) AddCommGrpCat)) _

variable [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
  [∀ U : Opens (ComplexPoint X), ParacompactSpace U] [IsIntegral X'.left] [Smooth X'.hom]
  [T2Space (ComplexPoint X')] [∀ U : Opens (ComplexPoint X'), ParacompactSpace U]

set_option backward.isDefEq.respectTransparency false in
/-- **The supported pullback through the singular comparison.** For `g : X' ⟶ X` and closed
`Z ⊆ X(ℂ)`, `Z' ⊆ X'(ℂ)` with `g⁻¹ Z ⊆ Z'`, the singular class in `H^n(X'(ℂ), X'(ℂ) ∖ Z'; ℚ)` of
the supported pullback `g^*α` is `relativeCohomologyMap` along the map of pairs given by `g`,
applied to the singular class of `α` in `H^n(X(ℂ), X(ℂ) ∖ Z; ℚ)`. Exact: sign `+`, no scalar. -/
theorem supportedEquivPair_supportedPullback (Z : Closeds (ComplexPoint X))
    (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    supportedEquivPair X' Z' n (supportedPullback g Z Z' hZ n α) =
      relativeCohomologyMap ℚ n
        (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha))
        (supportedEquivPair X Z n α) := by
  obtain ⟨x, hx, -, hα⟩ := exists_supported_rep X Z α
  have h3 := supportedPullback_named g Z Z' hZ α _ hα
  rw [pullbackCocycle_supCocycle g Z Z' hZ x hx] at h3
  rw [supportedEquivPair_of_named X' Z' _ _ (map_d_eq_zero _ x hx) h3,
    supportedEquivPair_of_named X Z α x hx hα, mapHomologyIso_cls_relPullback g Z Z' hZ x hx]
  erw [relativeDualCochainCohomologyEquiv_naturality]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, ← LinearMap.comp_apply,
    ← relativeCohomologyMap_comp, topPairIso_hom_comp_openPairPullback]

set_option backward.isDefEq.respectTransparency false in
/-- **The absolute case.** Through `rationalCohomologyAddEquivSingularCohomology` on both sides,
the pullback `pullbackCoh g n` of sheaf cohomology is `cohomologyMap ℚ n (pointMap g)` of singular
cohomology. Exact: sign `+`, no scalar. -/
theorem singular_pullbackCoh (n : ℕ) (β : H^n(X; ℚ)) :
    rationalCohomologyAddEquivSingularCohomology X' n (pullbackCoh g n β) =
      cohomologyMap ℚ n (pointMap g) (rationalCohomologyAddEquivSingularCohomology X n β) := by
  obtain ⟨α, rfl⟩ := forgetSupport_surjective_of_eq_top (X := X) ⊤ rfl n β
  rw [← forgetSupport_supportedPullback g ⊤ ⊤ (fun _ _ => trivial) n α,
    ← forgetRel_supportedEquivPair, ← forgetRel_supportedEquivPair,
    supportedEquivPair_supportedPullback, forgetRel_relativeCohomologyMap]
  rfl

open HodgeLadder.LocalClassPullback in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Upstream's transport `complexSupportInjectiveSectionCohomologyEquiv` at the neighborhood `⊤`
is `supportedEquivPair` followed by `relativeCohomologyMap` along the inverse of
`ofSubsetIsoNeighborhoodTop`, the identity on points. -/
theorem transport_eq_supportedEquivPair {Y : Over (Spec ↧ℂ)} [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] [T2Space (ComplexPoint Y)]
    [∀ U : Opens (ComplexPoint Y), ParacompactSpace U]
    (W : Closeds (ComplexPoint Y)) (n : ℕ) (β : H_[W]^n(Y; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv Y W ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology Y W n β) =
      relativeCohomologyMap ℚ n (ofSubsetIsoNeighborhoodTop W).inv
        (supportedEquivPair Y W n β) := by
  rw [supportedEquivPair_eq_transport, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.inv_hom_id, relativeCohomologyMap_id, LinearMap.id_apply]

open HodgeLadder.LocalClassPullback in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The supported pullback through upstream's transport.** For projective `X` and `X'`,
through `complexSupportInjectiveSectionCohomologyEquiv` at the neighborhood `⊤` on both sides,
the supported pullback `g^*α` is `relativeCohomologyMap` along
`neighborhoodSupportPullbackPairMap (Point.map g)` at `⊤`. Exact: sign `+`, no scalar. -/
theorem transport_supportedPullback [IsProjective X.hom] [IsProjective X'.hom]
    (Z : Closeds (ComplexPoint X)) (Z' : Closeds (ComplexPoint X'))
    (hZ : ⇑(Point.continuousMap g) ⁻¹' (Z : Set (ComplexPoint X)) ⊆ Z')
    (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    complexSupportInjectiveSectionCohomologyEquiv X' Z' ⊤ n
        (rationalSupportAddEquivSupportedInjectiveHomology X' Z' n
          (supportedPullback g Z Z' hZ n α)) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPullbackPairMap (Point.map g) (Point.continuous_map _)
          (W' := ((⊤ : Opens (ComplexPoint X')) : Set (ComplexPoint X')))
          (W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (fun _ _ h => hZ h))
        (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ n
          (rationalSupportAddEquivSupportedInjectiveHomology X Z n α)) := by
  have hp : (ofSubsetIsoNeighborhoodTop Z').inv ≫
      (TopPair.ofSubsetHom (pointMap g) (fun _ ha => compl_le_of_preimage_subset g Z Z' hZ ha) ≫
        (ofSubsetIsoNeighborhoodTop Z).hom) =
      neighborhoodSupportPullbackPairMap (Point.map g) (Point.continuous_map _)
          (W' := ((⊤ : Opens (ComplexPoint X')) : Set (ComplexPoint X')))
          (W := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
          (fun _ _ h => hZ h) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  rw [transport_eq_supportedEquivPair (Y := X') Z', supportedEquivPair_supportedPullback,
    supportedEquivPair_eq_transport X Z n α, ← hp, relativeCohomologyMap_comp,
    relativeCohomologyMap_comp]
  rfl

end HodgeLadder.Supported
