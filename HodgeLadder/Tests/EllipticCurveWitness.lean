module

public import HodgeLadder.Tests.EllipticCurveSmooth
public import HodgeLadder.Tests.EllipticCurveIntegral
public import HodgeLadder.Tests.EllipticCurveCM
public import HodgeLadder.Tests.CodimensionZero
public import HodgeLadder.Lefschetz.OneOne
public import HodgeConjecture.Statement

/-!
# The plane cubic `y²z = x³ − xz²` satisfies the hypotheses of the statements of record

Rung `elliptic-curve-witness`. The curve `ellipticCurve` of `plane-cubic-subscheme`, an object of
`Over (Spec ↧ℂ)`, is integral (`elliptic-curve-integral`), smooth of relative dimension one
(`elliptic-curve-smooth`) and projective (`plane-cubic-subscheme`), so upstream's
`HodgeConjecture` and `LefschetzOneOne` specialize to it. Its complex points are Hausdorff
(upstream's instance for projective `X`) and nonempty (the origin `[0 : 0 : 1]`), every open subset
of them is paracompact (upstream's `ComplexPoint.openParacompactSpace`), upstream's dimension of
`E` is `1`, and the relative dimension is unique.

Non-vacuity on upstream definitions: the checked Lefschetz (1,1) theorem applies at `E`, the
codimension-zero equality `Hdg⁰ = algebraicCycleClassSpan 0` holds at `E`, and the class of `E`
itself, `cycleComponentSheafClass` at the generic point, is nonzero (upstream's `Other` library).
The point `(i, 1 − i)` of `elliptic-curve-integral` is the point `ellipticCurvePointI` of
`elliptic-curve-cm`, by `rfl`.

No sign or normalization convention enters this file.

## Main results

* `HodgeLadder.Tests.ellipticCurve_witness`, `ellipticCurve_t2Space`,
  `ellipticCurve_openParacompactSpace`, `dim_ellipticCurve`,
  `relativeDimension_ellipticCurve_eq`, `ellipticCurve_complexPoint_nonempty`
* `HodgeLadder.Tests.hodgeConjecture_ellipticCurve`, `lefschetzOneOne_ellipticCurve`,
  `hodge_eq_span_zero_ellipticCurve`, `ellipticCurve_fundamentalClass_ne_zero`
* `HodgeLadder.Tests.ellipticCurveChartMeet_eq_pointI`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace

namespace HodgeLadder.Tests

/-- **Rung `elliptic-curve-witness`.** The plane cubic `E : y²z = x³ − xz²` satisfies the scheme
hypotheses of the statements of record: integral, smooth of relative dimension one (hence smooth),
and projective. -/
theorem ellipticCurve_witness :
    IsIntegral ellipticCurve.left ∧ SmoothOfRelativeDimension 1 ellipticCurve.hom ∧
      Smooth ellipticCurve.hom ∧ IsProjective ellipticCurve.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The complex points of `E` are Hausdorff (upstream's `IsProjective.complexPoint_t2Space`). -/
theorem ellipticCurve_t2Space : T2Space (ComplexPoint ellipticCurve) := inferInstance

/-- Every open subset of the complex points of `E` is paracompact (upstream's
`ComplexPoint.openParacompactSpace`). -/
theorem ellipticCurve_openParacompactSpace :
    ∀ U : Opens (ComplexPoint ellipticCurve), ParacompactSpace U :=
  ComplexPoint.openParacompactSpace ellipticCurve

/-- Upstream's dimension of `E` is `1` (upstream's `SmoothOfRelativeDimension.dim_eq`). -/
theorem dim_ellipticCurve : TopologicalSpace.dim ellipticCurve.left = 1 :=
  SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) 1

/-- The relative dimension of `E` over `ℂ` is unique: any `d` with `SmoothOfRelativeDimension d`
is `1`. -/
theorem relativeDimension_ellipticCurve_eq (d : ℕ)
    [SmoothOfRelativeDimension d ellipticCurve.hom] : d = 1 :=
  (SmoothOfRelativeDimension.dim_eq (f := ellipticCurve.hom) d).symm.trans dim_ellipticCurve

/-- `E` has a complex point (the origin `[0 : 0 : 1]`, `nonempty_complexPoint_ellipticCurve`). -/
theorem ellipticCurve_complexPoint_nonempty : Nonempty (ComplexPoint ellipticCurve) :=
  inferInstance

/-- Upstream's `HodgeConjecture` specializes to `E`: its instance arguments elaborate at
`ellipticCurve`. -/
theorem hodgeConjecture_ellipticCurve (h : HodgeConjecture) (p : ℕ) :
    Hdg^p(ellipticCurve; ℚ) ≤ algebraicCycleClassSpan ellipticCurve p :=
  h ellipticCurve p

/-- The checked Lefschetz (1,1) theorem (`lefschetz-1-1`) at `E`: every rational Hodge class of
degree two on `E` is a rational combination of classes of points. -/
theorem lefschetzOneOne_ellipticCurve :
    Hdg^1(ellipticCurve; ℚ) ≤ algebraicCycleClassSpan ellipticCurve 1 :=
  HodgeLadder.lefschetzOneOne_holds ellipticCurve

/-- The codimension-zero equality (`nonvacuity-tests`) at `E`. -/
theorem hodge_eq_span_zero_ellipticCurve :
    Hdg^0(ellipticCurve; ℚ) = algebraicCycleClassSpan ellipticCurve 0 :=
  hodge_eq_span_zero ellipticCurve

/-- The class of `E` itself, upstream's `cycleComponentSheafClass` at the generic point, is
nonzero (upstream's `cycleComponentSheafClass_genericPoint_ne_zero`). -/
theorem ellipticCurve_fundamentalClass_ne_zero :
    cycleComponentSheafClass ellipticCurve (genericPoint ellipticCurve.left)
      (coheight_genericPoint_eq_zero ellipticCurve) ≠ 0 :=
  cycleComponentSheafClass_genericPoint_ne_zero ellipticCurve

/-- The point `(i, 1 − i)` that `elliptic-curve-integral` uses to join the charts is the point
`ellipticCurvePointI` of `elliptic-curve-cm`. -/
theorem ellipticCurveChartMeet_eq_pointI : ellipticCurveChartMeet = ellipticCurvePointI := rfl

end HodgeLadder.Tests
