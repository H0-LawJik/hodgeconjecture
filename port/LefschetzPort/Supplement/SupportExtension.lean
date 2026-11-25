/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtensionVanishing
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedOnOpen
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization
import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Port supplement: unique extension across the singular locus, in the injective model

On the upstream stack's branch, `HodgeConjecture/Definitions/AlgebraicGeometry/Cycle/Component/
SupportExtension.lean` proved, in the injective model of cohomology with support, that the
supported cohomology of the singular boundary vanishes in degrees `2p` and `2p + 1`, and hence
that restriction to `X(ℂ) ∖ Z_sing(ℂ)` is an isomorphism in degree `2p`. Upstream main refactored
that file to the `Ext` model and made the injective-model vanishing private.

This supplement derives the injective-model vanishing from main's public `Ext`-model lemma
`cycleComponentSingularBoundaryRelH_isZero_of_lt`, transported exactly across main's comparison
equivalence `rationalSupportAddEquivSupportedInjectiveHomology`, and restates the branch's
restriction isomorphism with upstream's proof.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- Injective-model form of main's singular-boundary vanishing below degree `2(p + 1)`. -/
theorem cycleComponentSingularBoundaryInjectiveHomology_isZero_of_lt (n : ℕ)
    (hn : (n : ℤ) < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology (n : ℤ)) := by
  have h := cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx n hn
  let e := rationalSupportAddEquivSupportedInjectiveHomology X
    (cycleComponentSingularAnalyticClosedFiltration X x 0) n
  haveI : Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (cycleComponentSingularAnalyticClosedFiltration X x 0)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :=
    AddCommGrpCat.subsingleton_of_isZero h
  haveI := e.symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

include hx in
/-- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`, injective model. -/
theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology (2 * (p : ℤ))) := by
  have h := cycleComponentSingularBoundaryInjectiveHomology_isZero_of_lt X x hx (2 * p)
    (by push_cast; omega)
  simpa using h

include hx in
/-- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`, injective model. -/
theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology (2 * (p : ℤ) + 1)) := by
  have h := cycleComponentSingularBoundaryInjectiveHomology_isZero_of_lt X x hx (2 * p + 1)
    (by push_cast; omega)
  simpa using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hx in
/-- Restriction `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}_{Z(ℂ)}(X(ℂ) ∖ Z_sing(ℂ); ℚ)` is an isomorphism,
in the injective model (upstream's statement and proof). -/
theorem cycleComponentSupportSectionRestriction_homology_isIso :
    IsIso (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
      (2 * (p : ℤ))) := by
  let T := TopCat.of (ComplexPoint X)
  let h := cycleComponentSupportComplement_le_smoothAmbientOpen X x
  let K := ambientRationalInjectiveComplex X
  let S := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex T h ⊤ K
  let := TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing T h ⊤ K
    (2 * (p : ℤ))
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree X x hx)
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ X x hx)
  have he : HomologicalComplex.homologyMap S.g (2 * (p : ℤ)) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso T h K).hom (2 * (p : ℤ)) =
    HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 * (p : ℤ)))
      (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g T h K)
  rw [← he]
  infer_instance

end AlgebraicGeometry.ComplexPoint
