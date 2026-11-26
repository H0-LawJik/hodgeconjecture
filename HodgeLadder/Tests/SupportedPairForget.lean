module

public import HodgeLadder.Cup.SupportedPairForget
public import HodgeLadder.Normalization.Germ
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison

/-!
# Non-vacuity of `supported-pair-forget`

Both statements of rung `supported-pair-forget` relate nonzero classes on upstream's own cycle
classes (red team on `supported-pair-forget`, section 7b, change C).

* (b), `supportedEquivPair_eq_transport`: for every scheme point `x` of coheight `p`, the class
  `supportedEquivPair [Z_x]` is nonzero, so both sides of (b) are nonzero. Through (b) it is the
  pullback of upstream's transport `T [Z_x]`, whose sheafified restriction to `X ∖ Z_sing` is
  nonzero (`toSheaf_transport_supportedClass_ne_zero`).
* (a), `forgetRel_supportedEquivPair`: at the generic point (`Z = X(ℂ)`, degree `0`) the left side
  is nonzero, so both sides of (a) are nonzero. Through (a) it is `Ψ (forgetSupport [X])`; `Ψ` is
  an equivalence, forgetting the support `X(ℂ)` is injective (upstream
  `forgetSupport_injective_of_eq_top`), and `N [X] ≠ 0` (`normalization_genericPoint_ne_zero`).

Both hold on every smooth integral projective `X` over `ℂ`; `Spec ℂ` is one
(`HodgeLadder.Tests.exists_smooth_projective_integral`).

## Main results

* `HodgeLadder.Tests.supportedEquivPair_supportedClass_ne_zero`
* `HodgeLadder.Tests.forgetRel_supportedEquivPair_genericPoint_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace AlgebraicTopology.Singular
  HodgeLadder.Cup HodgeLadder.Normalization

namespace HodgeLadder.Tests

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- **Non-vacuity of (b).** The supported comparison on `(X, X ∖ Z)` of upstream's supported
cycle class of every component is nonzero. -/
theorem supportedEquivPair_supportedClass_ne_zero (x : X.left) {p : ℕ}
    (hx : Order.coheight x = p) :
    supportedEquivPair X (cycleComponentAnalyticClosedSupport X x) (2 * p)
      (cycleComponentSupportedInjectiveClass X x hx) ≠ 0 := by
  intro h
  apply toSheaf_transport_supportedClass_ne_zero X x hx
  rw [supportedEquivPair_eq_transport] at h
  have h' := congrArg (relativeCohomologyMap ℚ _ (ofSubsetIsoNeighborhoodTop
    (cycleComponentAnalyticClosedSupport X x)).inv) h
  rw [relativeCohomologyMap_inv_hom_apply, map_zero] at h'
  rw [h', map_zero]
  exact map_zero _

/-- **Non-vacuity of (a).** At the generic point, forgetting the subspace after the supported
comparison of the fundamental class `[X]` gives a nonzero class in `H⁰(X; ℚ)`. -/
theorem forgetRel_supportedEquivPair_genericPoint_ne_zero :
    forgetRel (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
        ((cycleComponentAnalyticClosedSupport X (genericPoint X.left)).compl :
          Set (ComplexPoint X))) (2 * 0)
      (supportedEquivPair X (cycleComponentAnalyticClosedSupport X (genericPoint X.left)) (2 * 0)
        (cycleComponentSupportedInjectiveClass X (genericPoint X.left)
          (coheight_genericPoint_eq_zero X))) ≠ 0 := by
  rw [forgetRel_supportedEquivPair]
  intro h
  apply normalization_genericPoint_ne_zero X
  have h1 := (rationalCohomologyAddEquivSingularCohomology X _).injective (h.trans (map_zero _).symm)
  have h2 := forgetSupport_injective_of_eq_top ℚ X _
    (cycleComponentAnalyticClosedSupport_genericPoint_eq_top X) _ (h1.trans (map_zero _).symm)
  rw [h2, map_zero]

end HodgeLadder.Tests
