/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization

/-!
# Port supplement: main's component normalization, read in the injective model

Upstream main builds a component's supported class and its normalization in the `Ext` model of
cohomology with support. The upstream stack computes in the injective model. `componentTransport`
is main's comparison equivalence for one component in degree `2 = 2 * 1`, and
`cycleComponentSupportedClassNormalizationIso_transport_apply` evaluates main's normalization on a
transported class, from main's `cycleComponentSupportedClassNormalizationIso_apply`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Main's comparison equivalence from the `Ext` model to the injective model, for the component
with generic point `x`, in degree `2 = 2 * 1`. -/
abbrev componentTransport (x : X.left) :
    CycleComponentSupportedCohomology X x 1 ≃+
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 : ℤ) :=
  rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
    (2 * 1)

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Main's normalization of a class given in the injective model, after transport to the `Ext`
model, is restriction to the smooth ambient open followed by the lowest-degree section map. -/
theorem cycleComponentSupportedClassNormalizationIso_transport_apply
    (a : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          ((2 * p : ℕ) : ℤ)) :
    cycleComponentSupportedClassNormalizationIso X x hx
        ((rationalSupportAddEquivSupportedInjectiveHomology X
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).symm a) =
      (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).hom.hom.app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
        ((cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom
          (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
            (2 * (p : ℤ)) a)) := by
  have h := cycleComponentSupportedClassNormalizationIso_apply X x hx
    ((rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * p)).symm a)
  rw [AddEquiv.apply_symm_apply] at h
  exact h

end AlgebraicGeometry.ComplexPoint
