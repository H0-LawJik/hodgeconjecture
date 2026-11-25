/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyInjectiveModel
public import LefschetzPort.AlgebraicGeometry.SupportedExtForgetComparison
public import LefschetzPort.Supplement.AnalyticExt

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **The bridge to the cycle class of record.** Upstream main's fundamental class
`cycleComponentSheafClass` (built in the `Ext` model of cohomology with support) is, exactly and
with no scalar, the class read off from the ambient injective resolution used by the
divisor–Chern comparison: transport the supported class into the injective model, include the
supported sections, and return to ordinary cohomology.

Port change (to upstream main 2ead713): on the stack's branch the supported class already lived in
the injective model; on main it lives in the `Ext` model, so it is transported across
`rationalSupportAddEquivSupportedInjectiveHomology`. This is the exact identification required by
decision 0004 (no "up to scalar" step). -/
theorem cycleComponentSheafClass_eq_injectiveModel :
    cycleComponentSheafClass X x hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * p)).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
            (ambientRationalInjectiveComplex X)).f ((2 * p : ℕ) : ℤ)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)
            (cycleComponentSupportedInjectiveClass X x hx))) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * p)).injective
  rw [AddEquiv.apply_symm_apply, cycleComponentSheafClass,
    rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport]

end AlgebraicGeometry.ComplexPoint

end
