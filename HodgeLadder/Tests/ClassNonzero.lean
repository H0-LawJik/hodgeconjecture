module

public import HodgeLadder.Tests.ForgetSupport
public import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing
public import Other.AlgebraicGeometry.Cycle.FundamentalClass

/-!
# Nonvanishing of a divisor class from acyclicity of its complement

Let `x` be a point of coheight one of a smooth projective complex variety `X`, with analytic support
`Z`. If `H^1(X(ℂ) ∖ Z; ℚ) = 0`, then the class of `x` in `H^2(X; ℚ)` is nonzero. Upstream proves
the supported class nonzero (`cycleComponentSmoothSupportCoclassSection_ne_zero`, through the
normalization isomorphism), and forgetting the support is injective in degree two when the
complement has no `H^1` (`forget-support-exact`). Part of rung `projective-line-class-nonzero`.

## Main results

* `HodgeLadder.Tests.cycleComponentSheafClass_ne_zero_of_subsingleton`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Order

namespace HodgeLadder.Tests

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The class of a codimension-one point is nonzero when the complement of its support has no
rational cohomology in degree one. -/
theorem cycleComponentSheafClass_ne_zero_of_subsingleton (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (h : Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 1 (cycleComponentAnalyticClosedSupport X x).compl)) :
    cycleComponentSheafClass X x hx ≠ 0 := by
  intro h0
  rw [cycleComponentSheafClass_eq_forgetSupport] at h0
  have hinj := forgetSupport_injective_of_subsingleton X (cycleComponentAnalyticClosedSupport X x)
    1 h
  have hs : cycleComponentSupportedInjectiveClass X x hx = 0 :=
    hinj (h0.trans (map_zero _).symm)
  apply cycleComponentSmoothSupportCoclassSection_ne_zero X x hx
  rw [← cycleComponentSupportedInjectiveClass_normalization X x hx, hs]
  exact AddEquiv.map_zero _

end HodgeLadder.Tests
