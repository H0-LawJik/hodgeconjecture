module

public import HodgeLadder.Tests.EllipticCurvePoints
public import HodgeLadder.Tests.EllipticCurveWitness
public import LefschetzPort.AlgebraicGeometry.RegularFunctionsHolomorphic

/-!
# The chart coordinates of the plane cubic as holomorphic functions

Rung `elliptic-coordinate-functions` (sub-rung S4 of `elliptic-curve-holomorphic-form`,
`docs/sketches/elliptic-curve-holomorphic-form.md`). For the cubic `E : y²z = x³ − xz²` of
`plane-cubic-subscheme`, the affine coordinates of the two charts are sections of upstream's sheaf
of holomorphic functions `holomorphicFunctionSheaf` on `E(ℂ)`, for the charted-space structure of
`ComplexPoint` in dimension `dim E = 1`:

* `ellipticX`, `ellipticY` on the open `z ≠ 0` (`ellipticAffineOpen`), the coordinates `x`, `y`;
* `ellipticU`, `ellipticW` on the open `y ≠ 0` (`ellipticInfinityOpen`), the coordinates
  `u = x / y`, `w = z / y`.

Each is the image of a coordinate of the chart ring `ℂ[Y₀, Y₁] ⧸ (dehomogenize i F)` under the
port's `regularFunctionsToHolomorphic`, which evaluates regular functions at complex points.
The values agree with the chart homeomorphisms of `elliptic-curve-points`
(`ellipticX_apply`, ...; at `[x : y : 1]`, `ellipticX` is `x`: `ellipticX_affinePoint`), the chart
relations hold in the rings of holomorphic functions (`ellipticY_sq : y² = x³ − x`,
`ellipticW_eq : w = u³ − u w²`), and on the overlap `z ≠ 0, y ≠ 0` the restrictions satisfy
`u · y = x` and `w · y = 1` (`ellipticU_mul_ellipticY`, `ellipticW_mul_ellipticY`), pointwise
`u = x / y`, `w = 1 / y` (`ellipticU_eq_div`, `ellipticW_eq_inv`).

## Route

The value lemma `ellipticChartHolomorphic_apply` unwinds the four steps of `chartHomeomorph`:
upstream's `evaluate_openEquiv` (the open subscheme), `evaluate_map` along `chartOverIso`, and
`affineSpecEquiv_apply` (evaluation on `Spec` of the chart ring), then `quotAlgHomHomeomorph`
(`HodgeLadder.General.QuotAlgHom`). The relations are ring identities in the chart ring, carried by
the ring homomorphism; the overlap identities follow pointwise from
`ellipticInfinityHomeomorph_of_mem`.

## Tests

Values at the named points: `x = y = 0` at the origin, `(x, y) = (±1, 0)` at the two-torsion
points, `(i, 1 − i)` at `ellipticCurveChartMeet`, `u = w = 0` at `[0 : 1 : 0]` and
`((−1 + i) / 2, (1 + i) / 2)` at `ellipticCurveChartMeet`. Non-vacuity: none of `x`, `y`, `u`, `w`
is constant (`ellipticX_not_constant`, ...; `x` takes the values `1` and `−1` at the two-torsion
points). The pair `(x, y)` separates the points of `z ≠ 0`, and two points with the same `x` have
`y` equal or opposite (`eq_of_ellipticX_eq_of_ellipticY_eq`,
`ellipticY_eq_or_eq_neg_of_ellipticX_eq`). No sign or normalization convention enters beyond the coordinates themselves
(`u = x / y`, `w = z / y`, as in `docs/conventions.md`, row "Plane cubic E and its charts").

## Main definitions

* `HodgeLadder.Tests.ellipticChartSection`, `ellipticChartHolomorphic`, `EllipticHolomorphic`
* `HodgeLadder.Tests.ellipticX`, `ellipticY`, `ellipticU`, `ellipticW`
* `HodgeLadder.Tests.ellipticOverlapOpen`, `ellipticResAffine`, `ellipticResInfinity`

## Main results

* `HodgeLadder.Tests.ellipticChartHolomorphic_apply`, `ellipticX_apply`, `ellipticY_apply`,
  `ellipticU_apply`, `ellipticW_apply`, `ellipticX_affinePoint`, `ellipticY_affinePoint`,
  `ellipticU_infinityPoint`, `ellipticW_infinityPoint`
* `HodgeLadder.Tests.ellipticY_sq`, `ellipticW_eq`, `ellipticY_sq_apply`
* `HodgeLadder.Tests.eq_of_ellipticX_eq_of_ellipticY_eq`, `ellipticY_eq_or_eq_neg_of_ellipticX_eq`
* `HodgeLadder.Tests.ellipticU_eq_div`, `ellipticW_eq_inv`, `ellipticU_mul_ellipticY`,
  `ellipticW_mul_ellipticY`, `ellipticX_mul_ellipticW`, `isUnit_ellipticResAffine_ellipticY`
* `HodgeLadder.Tests.ellipticX_eq_regularToHolomorphicSheaf`,
  `ellipticHolomorphic_eq_openHolomorphicFunctions`, `holomorphicFunctionSheaf_map_eq`
* `HodgeLadder.Tests.ellipticXY_origin`, `ellipticX_twoTorsion`, `ellipticY_twoTorsion`,
  `ellipticXY_chartMeet`, `ellipticUW_infinity`, `ellipticUW_chartMeet`
* `HodgeLadder.Tests.ellipticX_not_constant`, `ellipticY_not_constant`, `ellipticU_not_constant`,
  `ellipticW_not_constant`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.Point HodgeLadder.QuotAlgHom
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

section Chart

/-- An element of the chart ring `ℂ[Y₀, Y₁] ⧸ (dehomogenize i F)` as a regular function on the
open subscheme `Xᵢ ≠ 0` of `E`: global sections of `Spec` of the chart ring, pulled back along
the chart isomorphism `Hypersurface.chartIso`, as sections of `E` over the open. -/
def ellipticChartSection (i : Fin 3) :
    Hypersurface.ChartRing cubicForm i →+* Γ(ellipticCurve.left, chartOpenScheme i) :=
  ((Scheme.ΓSpecIso (.of (Hypersurface.ChartRing cubicForm i))).inv ≫
    (Hypersurface.chartIso cubicForm cubicForm_mem i).hom.appTop ≫
      (chartOpenScheme i).topIso.hom).hom

/-- The analytic open over the chart `Xᵢ ≠ 0` is `chartOpen i`, by definition. -/
theorem analyticOpen_chartOpenScheme (i : Fin 3) :
    analyticOpen ellipticCurve (chartOpenScheme i) = chartOpen i := rfl

/-- Holomorphic functions on an open of `E(ℂ)`, for upstream's charts in dimension `dim E`: the
sections of upstream's `holomorphicFunctionSheaf ellipticCurve (dim E)` over the open. -/
abbrev EllipticHolomorphic (U : TopologicalSpace.Opens (ComplexPoint ellipticCurve)) :=
  C^ω⟮𝓘(ℂ, Fin (TopologicalSpace.dim ellipticCurve.left) → ℂ), U; ℂ⟯

/-- The chart ring of `Xᵢ ≠ 0` maps to holomorphic functions on `chartOpen i`: the port's
`regularFunctionsToHolomorphic` after `ellipticChartSection`. -/
def ellipticChartHolomorphic (i : Fin 3) :
    Hypersurface.ChartRing cubicForm i →+* EllipticHolomorphic (chartOpen i) :=
  (regularFunctionsToHolomorphic ellipticCurve _ (chartOpenScheme i)).comp (ellipticChartSection i)

/-- Evaluation of the chart ring at the coordinates of a complex algebra homomorphism `φ` is
`φ`. -/
theorem chartEval_quotAlgHomCoord (i : Fin 3)
    (φ : Hypersurface.ChartRing cubicForm i →ₐ[ℂ] ℂ) (r : Hypersurface.ChartRing cubicForm i) :
    chartEval i (quotAlgHomCoord _ φ).1 (quotAlgHomCoord _ φ).2 r = φ r := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  conv_rhs => rw [← (quotAlgHomHomeomorph _).left_inv φ]
  rfl

/-- **The value of a chart function.** At a point `z` of the chart `Xᵢ ≠ 0`, the holomorphic
function of `r` is `r` evaluated at the affine coordinates `chartHomeomorph i z` of `z`. -/
theorem ellipticChartHolomorphic_apply (i : Fin 3) (r : Hypersurface.ChartRing cubicForm i)
    (z : chartOpen i) :
    ellipticChartHolomorphic i r z =
      chartEval i (chartHomeomorph i z).1 (chartHomeomorph i z).2 r := by
  set U := chartOpenScheme i
  set X := ellipticCurve
  let z' := (openEquiv X U).symm ⟨z.1, z.2⟩
  have hz : map (openInclusion X U) z' = z.1 :=
    congrArg Subtype.val ((openEquiv X U).apply_symm_apply ⟨z.1, z.2⟩)
  set t := (Hypersurface.chartIso cubicForm cubicForm_mem i).hom.appTop
    ((Scheme.ΓSpecIso (.of (Hypersurface.ChartRing cubicForm i))).inv r)
  have h1 : ellipticChartHolomorphic i r z = Point.evaluate U (U.topIso.hom t) z.1 :=
    rfl
  have h2 := evaluate_openEquiv X U t z'
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h2
  have h3 := evaluate_eq (Y := X) U.ι_image_top t (map (openInclusion X U) z')
  have h4 := evaluate_map (chartOverIso i).hom ⊤
    ((Scheme.ΓSpecIso (.of (Hypersurface.ChartRing cubicForm i))).inv r) z'
  have h5 := affineSpecEquiv_apply (Hypersurface.ChartRing cubicForm i)
    (map (chartOverIso i).hom z') r
  rw [h1, chartHomeomorph]
  calc Point.evaluate U (U.topIso.hom t) z.1
      = Point.evaluate U (U.topIso.hom t) (map (openInclusion X U) z') := by rw [hz]
    _ = Point.evaluate (U.ι ''ᵁ ⊤) t (map (openInclusion X U) z') := h3.symm
    _ = Point.evaluate ⊤ t z' := h2
    _ = _ := h4.symm
    _ = _ := h5.symm
    _ = _ := (chartEval_quotAlgHomCoord i _ r).symm

end Chart

section Coordinates

/-- **The coordinate `x`** on the chart `z ≠ 0` of `E(ℂ)`, a holomorphic function: the image of
`X 0` in `ℂ[x, y] ⧸ (y² − x³ + x)`. -/
def ellipticX : EllipticHolomorphic ellipticAffineOpen :=
  ellipticChartHolomorphic 2 (Ideal.Quotient.mk _ (X 0))

/-- **The coordinate `y`** on the chart `z ≠ 0` of `E(ℂ)`, a holomorphic function: the image of
`X 1` in `ℂ[x, y] ⧸ (y² − x³ + x)`. -/
def ellipticY : EllipticHolomorphic ellipticAffineOpen :=
  ellipticChartHolomorphic 2 (Ideal.Quotient.mk _ (X 1))

/-- **The coordinate `u = x / y`** on the chart `y ≠ 0` of `E(ℂ)`, a holomorphic function: the
image of `X 0` in `ℂ[u, w] ⧸ (w − u³ + u w²)`. -/
def ellipticU : EllipticHolomorphic ellipticInfinityOpen :=
  ellipticChartHolomorphic 1 (Ideal.Quotient.mk _ (X 0))

/-- **The coordinate `w = z / y`** on the chart `y ≠ 0` of `E(ℂ)`, a holomorphic function: the
image of `X 1` in `ℂ[u, w] ⧸ (w − u³ + u w²)`. -/
def ellipticW : EllipticHolomorphic ellipticInfinityOpen :=
  ellipticChartHolomorphic 1 (Ideal.Quotient.mk _ (X 1))

/-- **Pin to upstream's sheaf.** `ellipticX` is the section of the regular function `x` under the
port's sheaf map `regularToHolomorphicSheaf` from the structure sheaf of `E` to the direct image of
upstream's `holomorphicFunctionSheaf`. -/
theorem ellipticX_eq_regularToHolomorphicSheaf :
    ellipticX = (regularToHolomorphicSheaf ellipticCurve _).hom.app (op (chartOpenScheme 2))
      (ellipticChartSection 2 (Ideal.Quotient.mk _ (X 0))) := rfl

/-- **Pin to upstream's ring.** Holomorphic functions on an open of `E(ℂ)` are, by definition,
upstream's `OpenHolomorphicFunctions` in dimension `dim E`, the coefficient ring of
`HolomorphicForm` and `holomorphicDeRhamSheaf`. -/
theorem ellipticHolomorphic_eq_openHolomorphicFunctions
    (U : TopologicalSpace.Opens (ComplexPoint ellipticCurve)) :
    EllipticHolomorphic U =
      OpenHolomorphicFunctions ellipticCurve (TopologicalSpace.dim ellipticCurve.left) (op U) :=
  rfl

/-- Restriction in upstream's `holomorphicFunctionSheaf` is Mathlib's
`ContMDiffMap.restrictRingHom`, by definition. -/
theorem holomorphicFunctionSheaf_map_eq
    {U V : TopologicalSpace.Opens (ComplexPoint ellipticCurve)} (h : V ≤ U)
    (f : EllipticHolomorphic U) :
    (holomorphicFunctionSheaf ellipticCurve (TopologicalSpace.dim ellipticCurve.left)).presheaf.map
      (homOfLE h).op f = ContMDiffMap.restrictRingHom _ _ ℂ h f := rfl

/-- **The value of `x`**: the first coordinate of the chart homeomorphism `z ≠ 0`. -/
theorem ellipticX_apply (z : ellipticAffineOpen) :
    ellipticX z = (ellipticAffineHomeomorph z : ℂ × ℂ).1 := by
  rw [ellipticX, ellipticChartHolomorphic_apply]
  simp [chartEval]
  rfl

/-- **The value of `y`**: the second coordinate of the chart homeomorphism `z ≠ 0`. -/
theorem ellipticY_apply (z : ellipticAffineOpen) :
    ellipticY z = (ellipticAffineHomeomorph z : ℂ × ℂ).2 := by
  rw [ellipticY, ellipticChartHolomorphic_apply]
  simp [chartEval]
  rfl

/-- **The value of `u`**: the first coordinate of the chart homeomorphism `y ≠ 0`. -/
theorem ellipticU_apply (z : ellipticInfinityOpen) :
    ellipticU z = (ellipticInfinityHomeomorph z : ℂ × ℂ).1 := by
  rw [ellipticU, ellipticChartHolomorphic_apply]
  simp [chartEval]
  rfl

/-- **The value of `w`**: the second coordinate of the chart homeomorphism `y ≠ 0`. -/
theorem ellipticW_apply (z : ellipticInfinityOpen) :
    ellipticW z = (ellipticInfinityHomeomorph z : ℂ × ℂ).2 := by
  rw [ellipticW, ellipticChartHolomorphic_apply]
  simp [chartEval]
  rfl

/-- **Pin.** At `[x : y : 1]`, the function `ellipticX` takes the value `x`. -/
theorem ellipticX_affinePoint (p : affineCurve) :
    ellipticX ⟨affinePoint p, affinePoint_mem p⟩ = p.1.1 := by
  rw [ellipticX_apply, ellipticAffineHomeomorph_affinePoint]

/-- At `[x : y : 1]`, the function `ellipticY` takes the value `y`. -/
theorem ellipticY_affinePoint (p : affineCurve) :
    ellipticY ⟨affinePoint p, affinePoint_mem p⟩ = p.1.2 := by
  rw [ellipticY_apply, ellipticAffineHomeomorph_affinePoint]

/-- At `[u : 1 : w]`, the function `ellipticU` takes the value `u`. -/
theorem ellipticU_infinityPoint (q : infinityCurve) :
    ellipticU ⟨infinityPoint q, infinityPoint_mem q⟩ = q.1.1 := by
  rw [ellipticU_apply, ellipticInfinityHomeomorph_infinityPoint]

/-- At `[u : 1 : w]`, the function `ellipticW` takes the value `w`. -/
theorem ellipticW_infinityPoint (q : infinityCurve) :
    ellipticW ⟨infinityPoint q, infinityPoint_mem q⟩ = q.1.2 := by
  rw [ellipticW_apply, ellipticInfinityHomeomorph_infinityPoint]

end Coordinates

section Relations

/-- The relation `y² = x³ − x` in the chart ring of `z ≠ 0`. -/
theorem chartRing_two_relation :
    (Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 2) (X 1)) ^ 2 =
      (Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 2) (X 0)) ^ 3 -
        Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 2) (X 0) := by
  rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span (Set.mem_singleton_iff.mpr ?_)
  rw [dehomogenize_two_cubicForm]
  ring

/-- The relation `w = u³ − u w²` in the chart ring of `y ≠ 0`. -/
theorem chartRing_one_relation :
    Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (X 1) =
      (Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (X 0)) ^ 3 -
        Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (X 0) *
          (Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (X 1)) ^ 2 := by
  rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_mul, ← map_sub, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span (Set.mem_singleton_iff.mpr ?_)
  rw [dehomogenize_one_cubicForm]
  ring

/-- **The chart relation `y² = x³ − x`**, in the ring of holomorphic functions on `z ≠ 0`. -/
theorem ellipticY_sq : ellipticY ^ 2 = ellipticX ^ 3 - ellipticX := by
  have h := congrArg (ellipticChartHolomorphic 2) chartRing_two_relation
  simp only [map_sub, map_pow] at h
  exact h

/-- **The chart relation `w = u³ − u w²`**, in the ring of holomorphic functions on `y ≠ 0`. -/
theorem ellipticW_eq : ellipticW = ellipticU ^ 3 - ellipticU * ellipticW ^ 2 := by
  have h := congrArg (ellipticChartHolomorphic 1) chartRing_one_relation
  simp only [map_sub, map_pow, map_mul] at h
  exact h

/-- The chart relation pointwise: `y(z)² = x(z)³ − x(z)`. -/
theorem ellipticY_sq_apply (z : ellipticAffineOpen) :
    ellipticY z ^ 2 = ellipticX z ^ 3 - ellipticX z :=
  congrArg (fun f : EllipticHolomorphic ellipticAffineOpen => f z) ellipticY_sq

/-- The pair `(x, y)` separates the points of `z ≠ 0`. -/
theorem eq_of_ellipticX_eq_of_ellipticY_eq {z z' : ellipticAffineOpen}
    (hx : ellipticX z = ellipticX z') (hy : ellipticY z = ellipticY z') : z = z' := by
  apply ellipticAffineHomeomorph.injective
  apply Subtype.ext
  rw [ellipticX_apply, ellipticX_apply] at hx
  rw [ellipticY_apply, ellipticY_apply] at hy
  exact Prod.ext hx hy

/-- The fibres of `x`: two points with the same `x` have `y` equal or opposite. -/
theorem ellipticY_eq_or_eq_neg_of_ellipticX_eq {z z' : ellipticAffineOpen}
    (hx : ellipticX z = ellipticX z') :
    ellipticY z = ellipticY z' ∨ ellipticY z = -ellipticY z' := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, ellipticY_sq_apply, ellipticY_sq_apply, hx]

end Relations

section Overlap

/-- The overlap `z ≠ 0, y ≠ 0` of the two charts of `E(ℂ)`. -/
abbrev ellipticOverlapOpen : TopologicalSpace.Opens (ComplexPoint ellipticCurve) :=
  ellipticAffineOpen ⊓ ellipticInfinityOpen

/-- Restriction of holomorphic functions from `z ≠ 0` to the overlap (upstream's restriction, by
`holomorphicFunctionSheaf_map_eq`). -/
abbrev ellipticResAffine :
    EllipticHolomorphic ellipticAffineOpen →+* EllipticHolomorphic ellipticOverlapOpen :=
  ContMDiffMap.restrictRingHom _ _ ℂ inf_le_left

/-- Restriction of holomorphic functions from `y ≠ 0` to the overlap. -/
abbrev ellipticResInfinity :
    EllipticHolomorphic ellipticInfinityOpen →+* EllipticHolomorphic ellipticOverlapOpen :=
  ContMDiffMap.restrictRingHom _ _ ℂ inf_le_right

/-- On the overlap, `y` vanishes nowhere. -/
theorem ellipticY_ne_zero_of_mem (z : ellipticOverlapOpen) :
    ellipticResAffine ellipticY z ≠ 0 := by
  change ellipticY ⟨z.1, z.2.1⟩ ≠ 0
  rw [ellipticY_apply]
  exact (mem_ellipticInfinityOpen_iff ⟨z.1, z.2.1⟩).mp z.2.2

/-- **The overlap identity `u = x / y`**, pointwise. -/
theorem ellipticU_eq_div (z : ellipticOverlapOpen) :
    ellipticResInfinity ellipticU z =
      ellipticResAffine ellipticX z / ellipticResAffine ellipticY z := by
  change ellipticU ⟨z.1, z.2.2⟩ = ellipticX ⟨z.1, z.2.1⟩ / ellipticY ⟨z.1, z.2.1⟩
  rw [ellipticU_apply, ellipticX_apply, ellipticY_apply]
  exact congrArg Prod.fst (ellipticInfinityHomeomorph_of_mem ⟨z.1, z.2.1⟩ z.2.2)

/-- **The overlap identity `w = 1 / y`**, pointwise. -/
theorem ellipticW_eq_inv (z : ellipticOverlapOpen) :
    ellipticResInfinity ellipticW z = 1 / ellipticResAffine ellipticY z := by
  change ellipticW ⟨z.1, z.2.2⟩ = 1 / ellipticY ⟨z.1, z.2.1⟩
  rw [ellipticW_apply, ellipticY_apply]
  exact congrArg Prod.snd (ellipticInfinityHomeomorph_of_mem ⟨z.1, z.2.1⟩ z.2.2)

/-- **The overlap identity `u · y = x`** in the ring of holomorphic functions on the overlap. -/
theorem ellipticU_mul_ellipticY :
    ellipticResInfinity ellipticU * ellipticResAffine ellipticY = ellipticResAffine ellipticX := by
  ext z
  change ellipticResInfinity ellipticU z * ellipticResAffine ellipticY z =
    ellipticResAffine ellipticX z
  rw [ellipticU_eq_div, div_mul_cancel₀ _ (ellipticY_ne_zero_of_mem z)]

/-- **The overlap identity `w · y = 1`** in the ring of holomorphic functions on the overlap. -/
theorem ellipticW_mul_ellipticY :
    ellipticResInfinity ellipticW * ellipticResAffine ellipticY = 1 := by
  ext z
  change ellipticResInfinity ellipticW z * ellipticResAffine ellipticY z = 1
  rw [ellipticW_eq_inv, one_div, inv_mul_cancel₀ (ellipticY_ne_zero_of_mem z)]

/-- On the overlap, `y` is a unit of the ring of holomorphic functions, with inverse `w`. -/
theorem isUnit_ellipticResAffine_ellipticY : IsUnit (ellipticResAffine ellipticY) :=
  IsUnit.of_mul_eq_one_right _ ellipticW_mul_ellipticY

/-- The inverse transition: `x · w = u` on the overlap. -/
theorem ellipticX_mul_ellipticW :
    ellipticResAffine ellipticX * ellipticResInfinity ellipticW =
      ellipticResInfinity ellipticU := by
  rw [← ellipticU_mul_ellipticY, mul_assoc, mul_comm (ellipticResAffine ellipticY),
    ellipticW_mul_ellipticY, mul_one]

end Overlap

section Tests

/-- **Test.** At the origin `[0 : 0 : 1]`, `x = y = 0`. -/
theorem ellipticXY_origin :
    ellipticX ⟨ellipticCurveOrigin, ellipticCurveOrigin_mem⟩ = 0 ∧
      ellipticY ⟨ellipticCurveOrigin, ellipticCurveOrigin_mem⟩ = 0 := by
  rw [ellipticX_apply, ellipticY_apply, ellipticAffineHomeomorph_origin]
  exact ⟨rfl, rfl⟩

/-- **Test.** At the two-torsion points `[±1 : 0 : 1]`, `x = ±1`. -/
theorem ellipticX_twoTorsion :
    ellipticX ⟨ellipticCurveTwoTorsionPos, ellipticCurveTwoTorsionPos_mem⟩ = 1 ∧
      ellipticX ⟨ellipticCurveTwoTorsionNeg, ellipticCurveTwoTorsionNeg_mem⟩ = -1 := by
  rw [ellipticX_apply, ellipticX_apply, ellipticAffineHomeomorph_twoTorsionPos,
    ellipticAffineHomeomorph_twoTorsionNeg]
  exact ⟨rfl, rfl⟩

/-- **Test.** At the two-torsion points `[±1 : 0 : 1]`, `y = 0`. -/
theorem ellipticY_twoTorsion :
    ellipticY ⟨ellipticCurveTwoTorsionPos, ellipticCurveTwoTorsionPos_mem⟩ = 0 ∧
      ellipticY ⟨ellipticCurveTwoTorsionNeg, ellipticCurveTwoTorsionNeg_mem⟩ = 0 := by
  rw [ellipticY_apply, ellipticY_apply, ellipticAffineHomeomorph_twoTorsionPos,
    ellipticAffineHomeomorph_twoTorsionNeg]
  exact ⟨rfl, rfl⟩

/-- **Test.** At `[i : 1 − i : 1]`, `(x, y) = (i, 1 − i)`. -/
theorem ellipticXY_chartMeet :
    ellipticX ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem⟩ = Complex.I ∧
      ellipticY ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem⟩ = 1 - Complex.I := by
  rw [ellipticX_apply, ellipticY_apply, ellipticAffineHomeomorph_chartMeet]
  exact ⟨rfl, rfl⟩

/-- **Test.** At the point at infinity `[0 : 1 : 0]`, `u = w = 0`. -/
theorem ellipticUW_infinity :
    ellipticU ⟨ellipticCurveInfinity, ellipticCurveInfinity_mem⟩ = 0 ∧
      ellipticW ⟨ellipticCurveInfinity, ellipticCurveInfinity_mem⟩ = 0 := by
  rw [ellipticU_apply, ellipticW_apply, ellipticInfinityHomeomorph_infinity]
  exact ⟨rfl, rfl⟩

/-- **Test of the overlap.** At `[i : 1 − i : 1]`, `(u, w) = ((−1 + i) / 2, (1 + i) / 2)`. -/
theorem ellipticUW_chartMeet :
    ellipticU ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩ =
        (-1 + Complex.I) / 2 ∧
      ellipticW ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩ =
        (1 + Complex.I) / 2 := by
  rw [ellipticU_apply, ellipticW_apply, ellipticInfinityHomeomorph_chartMeet]
  exact ⟨rfl, rfl⟩

/-- **Non-vacuity.** `x` is not constant: it takes the values `1` and `−1` at the two-torsion
points. -/
theorem ellipticX_not_constant : ¬ ∃ c : ℂ, ∀ z, ellipticX z = c := by
  rintro ⟨c, hc⟩
  have h := ellipticX_twoTorsion
  rw [hc, hc] at h
  have : (1 : ℂ) = -1 := h.1.symm.trans h.2
  norm_num at this

/-- **Non-vacuity.** `y` is not constant: `0` at the origin, `1 − i` at `[i : 1 − i : 1]`. -/
theorem ellipticY_not_constant : ¬ ∃ c : ℂ, ∀ z, ellipticY z = c := by
  rintro ⟨c, hc⟩
  have h0 := ellipticXY_origin.2
  have h1 := ellipticXY_chartMeet.2
  rw [hc] at h0 h1
  exact one_sub_I_ne_zero (h1.symm.trans h0)

/-- **Non-vacuity.** `u` is not constant: `0` at `[0 : 1 : 0]`, `(−1 + i) / 2` at
`[i : 1 − i : 1]`. -/
theorem ellipticU_not_constant : ¬ ∃ c : ℂ, ∀ z, ellipticU z = c := by
  rintro ⟨c, hc⟩
  have h0 := ellipticUW_infinity.1
  have h1 := ellipticUW_chartMeet.1
  rw [hc] at h0 h1
  have : ((-1 + Complex.I) / 2 : ℂ) = 0 := h1.symm.trans h0
  have := congrArg Complex.re this
  norm_num at this

/-- **Non-vacuity.** `w` is not constant: `0` at `[0 : 1 : 0]`, `(1 + i) / 2` at
`[i : 1 − i : 1]`. -/
theorem ellipticW_not_constant : ¬ ∃ c : ℂ, ∀ z, ellipticW z = c := by
  rintro ⟨c, hc⟩
  have h0 := ellipticUW_infinity.2
  have h1 := ellipticUW_chartMeet.2
  rw [hc] at h0 h1
  have : ((1 + Complex.I) / 2 : ℂ) = 0 := h1.symm.trans h0
  have := congrArg Complex.re this
  norm_num at this

end Tests

end HodgeLadder.Tests
