module

public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization

/-!
# Upstream's normalization iso of a supported cycle class, through the singular transport

Rung `normalization-singular` (front `cycle-class-multiplicative`, glue). Let `x` be a point of
coheight `p` with closed analytic support `Z = cycleComponentAnalyticClosedSupport X x` and smooth
ambient open `U = cycleComponentSmoothSupportAmbientOpen X x` (the complement of the singular
locus of `Z`). Upstream's normalization isomorphism `N = cycleComponentSupportedClassNormalizationIso`
sends a supported class `a ∈ H^{2p}_Z(X; ℚ)` to a section over `U` of the supported cohomology sheaf.
This file computes `N a` on the singular side: it is the sheafification unit
`supportRelativeCohomologyToSheaf` at `U`, applied to the restriction from the pair
`(X, X ∖ Z)` to `(U, U ∖ Z)` of upstream's transport
`complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ (2p)` of `a`.

No sign and no scalar enter: every step is an upstream equation between actual maps
(`cycleComponentSupportedClassNormalizationIso_apply`,
`openRestrictedLowestSectionCohomologyIso_hom`,
`complexSupportInjectiveCohomologySheafIsoRelative_restriction_section`) followed by the
naturality square of the sheafification unit for the inclusion `U ≤ ⊤`, whose presheaf map is
`relativeCohomologyMap` along `neighborhoodSupportInclusionPairMap` by definition.

## Main results

* `HodgeLadder.Normalization.normalization_singular`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology.Singular

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every open of `X(ℂ)` is paracompact (upstream's `openParacompactSpace`). Kept to match the
statement fixed in the sketch; at the pin the transport provides this instance itself. -/
local instance : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- Upstream's normalization isomorphism of a supported cycle class `a ∈ H^{2p}_Z(X; ℚ)` is the
sheafification unit at the smooth ambient open `U` applied to the restriction, from
`(X, X ∖ Z)` to `(U, U ∖ Z)`, of upstream's singular transport of `a` at `⊤`. The identity holds
exactly, with no sign. -/
theorem normalization_singular (x : X.left) {p : ℕ} (hx : Order.coheight x = p)
    (a : CycleComponentSupportedCohomology X x p) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
        (relativeCohomologyMap ℚ (2 * p)
          (neighborhoodSupportInclusionPairMap
            (W := (cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint X)))
            (V := ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))) (fun _ _ => trivial)
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
          (complexSupportInjectiveSectionCohomologyEquiv X (cycleComponentAnalyticClosedSupport X x)
            ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p) a))) := by
  have hnorm := cycleComponentSupportedClassNormalizationIso_apply X x hx a
  refine hnorm.trans ?_
  have hL : (cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom =
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ)) (cycleComponentSmoothSupportAmbientOpen X x) :=
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom _ _ _ _ _ _ _
  rw [hL]
  have h := ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section X
      (cycleComponentAnalyticClosedSupport X x) (2 * p)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)))
    (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * p) a)
  refine h.trans ?_
  exact ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X x) (2 * p)).naturality
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)).op).symm _

end HodgeLadder.Normalization
