module

public import HodgeLadder.Hodge.DeRhamRationalSpan

/-!
# Rational classes independent over `ℚ` have de Rham images independent over `ℂ`

Rung `de-rham-rational-independent`, an input of target T1 of the Markman inventory
(`docs/sketches/cup-hodge-filtration.md`, section "de-rham-rational-independent: statement";
proposed in `docs/sketches/de-rham-rational-span.redteam.md`, finding 1). For a smooth integral
scheme `X` over `ℂ` and upstream's `ι = fieldToDeRhamCohomology ℚ X n`, a family of classes in
`H^n(X(ℂ); ℚ)` that is linearly independent over `ℚ` has image linearly independent over `ℂ` in
`H_dR^n(X)`. Together with rung `de-rham-rational-span` this makes
`ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)` bijective.

`de-rham-injective` gives injectivity of `ι` over `ℚ` only, which is weaker: `ℚ² → ℂ`,
`(a, b) ↦ a + b √2` is injective and its image spans `ℂ` over `ℂ`.

The proof stays on the sheaf side. A relation `∑ zᵢ • ι vᵢ = 0` is, by
`smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt` and the holomorphic Poincaré lemma
(`complexConstantCohomologyDeRhamAddEquiv`), a relation `∑ (ratScaled zᵢ)_* vᵢ = 0` in complex
constant-sheaf cohomology. Pushing it along a `ℚ`-linear functional `φ : ℂ → ℚ`, an additive map
of coefficients, gives `∑ φ(zᵢ) • vᵢ = 0` in `H^n(X(ℂ); ℚ)`, because `φ ∘ ratScaled z` is
multiplication by `φ z` and upstream's `ℚ`-action is change of coefficients along that
multiplication. Independence of the `vᵢ` gives `φ zᵢ = 0` for every `φ`, so `zᵢ = 0`.
No finiteness of cohomology, no Hausdorffness and no projectivity are used, and the comparison
with singular cohomology is not needed.

## Main results

* `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`: the statement for
  smooth integral `X`.
* `HodgeLadder.linearIndependent_fieldToDeRhamCohomology_rat`: the rung as posted, with
  `IsProjective`.
* `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth`,
  `HodgeLadder.injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat`: the equivalent form,
  injectivity of `LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)`.
* `HodgeLadder.constantCoefficientSheafComplexIntMap_comp`: change of coefficients on the
  constant sheaf complex is functorial in additive maps.
* `HodgeLadder.bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span`,
  `HodgeLadder.finrank_deRham_eq_finrank_rat_of_span`: with the span equality for one `X`, the
  base-change map is bijective and `finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`.
* `HodgeLadder.bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_simplicialComplexSpan`,
  `HodgeLadder.finrank_deRham_eq_finrank_rat_of_simplicialComplexSpan`: the same for smooth
  projective integral `X`, conditional on `SimplicialComplexSpan` (rung
  `de-rham-rational-base-change`, checked in `HodgeLadder.Hodge.DeRhamRationalBaseChange`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLadder

variable (X : Over (Spec ↧ℂ))

/-- Change of coefficients on constant sheaves is functorial in additive maps. -/
lemma constantCoefficientSheafMap_comp {R S T : Type} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+ S) (g : S →+ T) :
    AlgebraicTopology.Singular.constantCoefficientSheafMap f (TopCat.of (ComplexPoint X)) ≫
      AlgebraicTopology.Singular.constantCoefficientSheafMap g (TopCat.of (ComplexPoint X)) =
      AlgebraicTopology.Singular.constantCoefficientSheafMap (g.comp f)
        (TopCat.of (ComplexPoint X)) := by
  change (presheafToSheaf _ _).map _ ≫ (presheafToSheaf _ _).map _ = (presheafToSheaf _ _).map _
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Change of coefficients on the integer-indexed constant sheaf complex is functorial in
additive maps. -/
lemma constantCoefficientSheafComplexIntMap_comp {R S T : Type} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+ S) (g : S →+ T) :
    constantCoefficientSheafComplexIntMap X f ≫ constantCoefficientSheafComplexIntMap X g =
      constantCoefficientSheafComplexIntMap X (g.comp f) := by
  unfold constantCoefficientSheafComplexIntMap
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp, constantCoefficientSheafMap_comp]

/-- Change of coefficients along `q ↦ r q` on `ℚ` is upstream's scalar endomorphism
`fieldScalarComplex ℚ X r`. -/
lemma constantCoefficientSheafComplexIntMap_mulLeft (r : ℚ) :
    constantCoefficientSheafComplexIntMap X (AddMonoidHom.mulLeft r) = fieldScalarComplex ℚ X r :=
  rfl

/-- A `ℚ`-linear functional `φ : ℂ → ℚ` after `ratScaled z` is multiplication by `φ z`. -/
lemma toAddMonoidHom_comp_ratScaled (φ : ℂ →ₗ[ℚ] ℚ) (z : ℂ) :
    φ.toAddMonoidHom.comp (ratScaled z) = AddMonoidHom.mulLeft (φ z) := by
  ext q
  change φ (z * (q : ℂ)) = φ z * q
  rw [mul_comm z, ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Independence for smooth integral `X`: `ℚ`-independent rational classes have
`ℂ`-independent de Rham images. -/
theorem linearIndependent_fieldToDeRhamCohomology_rat_of_smooth [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) {ι : Type*} {v : ι → H^n(X; ℚ)} (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (fieldToDeRhamCohomology ℚ X n ∘ v) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  let E := hypercohomologyAddEquivConstantCohomology ℚ X n
  let e := hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)
  let M : ℂ → _ := fun z ↦
    hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (ratScaled z)) (n : ℤ)
  have h1 : ∀ j, g j • fieldToDeRhamCohomology ℚ X n (v j) = e (M (g j) (E.symm (v j))) :=
    fun j ↦ smul_hypercohomologyMap_fieldToHolomorphicDeRhamComplexInt X n (g j) (E.symm (v j))
  have h2 : ∑ j ∈ s, M (g j) (E.symm (v j)) = 0 := by
    apply (complexConstantCohomologyDeRhamAddEquiv X n).injective
    change e _ = e 0
    rw [map_sum, map_zero]
    simp_rw [← h1]
    exact hg
  have h3 : ∀ φ : Module.Dual ℚ ℂ, φ (g i) = 0 := by
    intro φ
    have hrel : ∑ j ∈ s, φ (g j) • v j = 0 := by
      apply E.symm.injective
      rw [map_sum, map_zero]
      have h4 := congrArg (hypercohomologyMap X
        (constantCoefficientSheafComplexIntMap X φ.toAddMonoidHom) (n : ℤ)) h2
      rw [map_sum, map_zero] at h4
      refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) h4
      rw [hypercohomologyAddEquivConstantCohomology_symm_smul, ← hypercohomologyMap_comp_apply,
        constantCoefficientSheafComplexIntMap_comp, toAddMonoidHom_comp_ratScaled,
        constantCoefficientSheafComplexIntMap_mulLeft]
      rfl
    exact linearIndependent_iff'.mp hv s _ hrel i hi
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (g i)).mp h3

/-- **Rung `de-rham-rational-independent`.** For a smooth projective integral scheme `X` over
`ℂ`, `ℚ`-independent rational classes have `ℂ`-independent de Rham images. The proof uses only
`IsIntegral` and `Smooth` (`linearIndependent_fieldToDeRhamCohomology_rat_of_smooth`). -/
theorem linearIndependent_fieldToDeRhamCohomology_rat [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℕ) {ι : Type} {v : ι → H^n(X; ℚ)}
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (fieldToDeRhamCohomology ℚ X n ∘ v) :=
  linearIndependent_fieldToDeRhamCohomology_rat_of_smooth X n hv

/-- The base-change form for smooth integral `X`: the `ℂ`-linear extension
`ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)` of `ι` is injective. -/
theorem injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ) :
    Function.Injective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)) := by
  let b := Module.Basis.ofVectorSpace ℚ H^n(X; ℚ)
  let c := b.baseChange ℂ
  let F := LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)
  have hFc : F ∘ c = fieldToDeRhamCohomology ℚ X n ∘ b := by
    funext i
    simp only [Function.comp_apply, c, Module.Basis.baseChange_apply, F,
      LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hli : LinearIndependent ℂ (F ∘ c) := by
    rw [hFc]
    exact linearIndependent_fieldToDeRhamCohomology_rat_of_smooth X n b.linearIndependent
  intro x y hxy
  apply c.repr.injective
  apply hli
  rw [← Finsupp.apply_linearCombination, ← Finsupp.apply_linearCombination,
    c.linearCombination_repr, c.linearCombination_repr]
  exact hxy

/-- The base-change form under the ledger's hypotheses. -/
theorem injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Function.Injective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)) :=
  injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth X n

/-! ### Toward the base-change identity

Rung `de-rham-rational-base-change`, checked in `HodgeLadder.Hodge.DeRhamRationalBaseChange`. -/

/-- Given the span equality of rung `de-rham-rational-span` for one `X` and degree `n`, the
`ℂ`-linear extension `ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)`, `c ⊗ m ↦ c • ι m`, is bijective. -/
theorem bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span [IsIntegral X.left]
    [Smooth X.hom] (n : ℕ)
    (hspan : Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤) :
    Function.Bijective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)) := by
  refine ⟨injective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_smooth X n, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨1 ⊗ₜ x, by simp only [LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩

/-- Given the span equality for one `X` and degree `n`,
`finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`. Both sides are `0` when infinite-dimensional,
so the equality carries content only together with finiteness. -/
theorem finrank_deRham_eq_finrank_rat_of_span [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (hspan : Submodule.span ℂ (Set.range (fieldToDeRhamCohomology ℚ X n)) = ⊤) :
    Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ) := by
  rw [← (LinearEquiv.ofBijective _
    (bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span X n hspan)).finrank_eq,
    Module.finrank_baseChange]

/-- Conditional on `SimplicialComplexSpan`: for a smooth projective integral `X`, the map
`ℂ ⊗_ℚ H^n(X(ℂ); ℚ) → H_dR^n(X)` is bijective. -/
theorem bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_simplicialComplexSpan
    (hS : SimplicialComplexSpan) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) :
    Function.Bijective (LinearMap.liftBaseChange ℂ (fieldToDeRhamCohomologyLinear ℚ X n)) :=
  bijective_liftBaseChange_fieldToDeRhamCohomologyLinear_rat_of_span X n
    (deRhamRationalSpan_of_simplicialComplexSpan hS X n)

/-- Conditional on `SimplicialComplexSpan`: for a smooth projective integral `X`,
`finrank_ℂ H_dR^n(X) = finrank_ℚ H^n(X(ℂ); ℚ)`. -/
theorem finrank_deRham_eq_finrank_rat_of_simplicialComplexSpan (hS : SimplicialComplexSpan)
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ) :=
  finrank_deRham_eq_finrank_rat_of_span X n (deRhamRationalSpan_of_simplicialComplexSpan hS X n)

end HodgeLadder
