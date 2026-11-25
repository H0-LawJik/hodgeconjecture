module

public import HodgeLadder.Tests.ClassNonzero
public import Other.AlgebraicGeometry.Cycle.Component.PointPurity
public import Other.AlgebraicGeometry.Cycle.SmoothPair.PointCoclassSection
public import Other.AlgebraicGeometry.Cycle.Component.CoclassNonzero

/-!
# Degree-two cohomology of a curve from a point

Part of rung `projective-line-h2`. Let `X` be a smooth projective complex curve and `x` a closed
point with analytic support `Z = {p}`. If the complement `X(ℂ) ∖ Z` has no rational cohomology in
degrees one and two, then forgetting support is an isomorphism `H_[Z]^2(X; ℚ) ≅ H^2(X; ℚ)`
(`forget-support-exact`). Upstream identifies the supported group with relative singular
cohomology `H^2(X(ℂ), X(ℂ) ∖ Z; ℚ)` and shows that singular cohomology supported at a point is
spanned by one nonzero local coclass. So `H^2(X; ℚ)` is one-dimensional.

## Main results

* `HodgeLadder.Tests.finrank_cohomologyWithSupport_point`
* `HodgeLadder.Tests.finrank_H2_of_subsingleton`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Order AlgebraicTopology.Singular

namespace HodgeLadder.Tests

variable {M : Type} [TopologicalSpace M]

/-- The pair `(M, M ∖ {p})` written as the pair of the whole space and the complement of a set
equal to `{p}`. -/
def univPointPairIso (S : Set M) (p : M) (hS : S = {p}) :
    neighborhoodSupportComplementPair (Set.univ : Set M) S ≅ pointComplementPair p where
  hom := neighborhoodSupportToPointPairMap Set.univ S p (hS ▸ rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1, trivial⟩, fun h => w.2 (by rw [hS] at h; exact h)⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w; rfl
    · ext w; rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w; rfl
    · ext w; rfl

/-- An isomorphism of pairs induces a linear equivalence in relative cohomology. -/
noncomputable def relativeCohomologyLinearEquiv {P Q : TopPair.{0}} (e : P ≅ Q) (n : ℕ) :
    RelativeCohomology ℚ Q n ≃ₗ[ℚ] RelativeCohomology ℚ P n :=
  LinearEquiv.ofLinearMap (relativeCohomologyMap ℚ n e.hom) (relativeCohomologyMap ℚ n e.inv)
    (by rw [← relativeCohomologyMap_comp, e.hom_inv_id, relativeCohomologyMap_id])
    (by rw [← relativeCohomologyMap_comp, e.inv_hom_id, relativeCohomologyMap_id])

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] in

/-- Rational singular cohomology of `X(ℂ)` supported at a point is one-dimensional in the top
degree. -/
theorem finrank_cohomologyWithSupport_point (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    Module.finrank ℚ (CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) {p} (2 * d)) = 1 := by
  have hc : analyticPointLocalCoclass X d p ≠ 0 := by
    intro h
    have h1 := analyticPointLocalCoclass_apply_localClass X d p
    rw [analyticPointLocalCoclassDual, h, map_zero] at h1
    exact zero_ne_one h1
  rw [← finrank_top, ← span_analyticPointLocalCoclass_eq_top X d p, finrank_span_singleton hc]

/-- An additive equivalence of rational vector spaces is `ℚ`-linear. -/
def addEquivToRat {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℚ A] [Module ℚ B]
    (e : A ≃+ B) : A ≃ₗ[ℚ] B :=
  { e with map_smul' := map_rat_smul e.toAddMonoidHom }

/-- **Degree-two cohomology of a curve is one-dimensional** when the complement of the support
of a point has no rational cohomology in degrees one and two. -/
theorem finrank_H2_of_subsingleton [SmoothOfRelativeDimension 1 X.hom] (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (h1 : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 1 (cycleComponentAnalyticClosedSupport X x).compl))
    (h2 : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 2 (cycleComponentAnalyticClosedSupport X x).compl)) :
    Module.finrank ℚ (H^(2 * 1)(X; ℚ)) = 1 := by
  let Z := cycleComponentAnalyticClosedSupport X x
  have hinj := forgetSupport_injective_of_subsingleton X Z 1 h1
  have hsurj := forgetSupport_surjective_of_subsingleton X Z 2 h2
  let eA := AddEquiv.ofBijective (forgetSupport ℚ X Z 2) ⟨hinj, hsurj⟩
  let eB := rationalSupportAddEquivSupportedInjectiveHomology X Z 2
  let eC := complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ 2
  obtain ⟨z, -⟩ := exists_cycleComponent_smooth_complexPoint X x
  have hS : ((Z : Set (ComplexPoint X))) = {cycleComponentMap X x z} :=
    cycleComponentSupport_eq_singleton_of_coheight_eq_dimension (d := 1) X x hx z
  let eD := relativeCohomologyLinearEquiv (univPointPairIso (Z : Set (ComplexPoint X))
    (cycleComponentMap X x z) hS) 2
  let L : H^(2 * 1)(X; ℚ) ≃ₗ[ℚ]
      CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) {cycleComponentMap X x z} (2 * 1) :=
    (addEquivToRat (eA.symm.trans (eB.trans eC))).trans eD.symm
  rw [L.finrank_eq]
  exact finrank_cohomologyWithSupport_point X 1 _

end HodgeLadder.Tests
