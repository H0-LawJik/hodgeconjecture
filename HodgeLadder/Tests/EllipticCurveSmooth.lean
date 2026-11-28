module

public import HodgeLadder.General.HypersurfaceSmooth
public import HodgeLadder.Tests.EllipticCurve

/-!
# The plane cubic `y²z = x³ − xz²` is smooth of relative dimension one

Rung `elliptic-curve-smooth`. The curve `ellipticCurve` of `plane-cubic-subscheme` is covered by
the charts `z ≠ 0`, `Spec ℂ[x, y] ⧸ (f)` with `f = y² − x³ + x`, and `y ≠ 0`,
`Spec ℂ[u, w] ⧸ (h)` with `h = w − u³ + u w²` (`ellipticCurve_chart_cover`). On each chart the
classes of the two partial derivatives generate the unit ideal, by explicit combinations checked
by `linear_combination`:

* `z ≠ 0`: `∂ₓf = 1 − 3x²`, `∂_y f = 2y`, and
  `(4 − 6x²) ∂ₓf − 9xy ∂_y f = 4 − 18x f`, with `4` a unit;
* `y ≠ 0`: `∂ᵤh = w² − 3u²`, `∂_w h = 1 + 2uw`, and `u² ∂ᵤh + (1 + uw) ∂_w h = 1 + 3u h`.

`HodgeLadder.HypersurfaceSmooth.smoothOfRelativeDimension_spec` makes each chart smooth of relative
dimension `2 − 1 = 1` over `Spec ℂ`, and smoothness of relative dimension one is local on the
source. The general Jacobian criterion at a point (rung `jacobian-smooth-point`) is not used.
No sign convention enters this file. The curve's linear term is recorded in `docs/conventions.md`,
row "Plane cubic E and its charts"; smoothness holds for either sign, and the two combinations
below are specific to y² = x³ − x.

Test of the hypothesis: for the cuspidal cubic `y² = x³` the partial derivatives `−3x²` and `2y`
both vanish at the origin, so they do not generate the unit ideal (`cusp_span_pderiv_ne_top`).
Test of the conclusion: on the localization of the chart `z ≠ 0` away from `2y`, nonzero because
`(i, 1 − i)` lies on the curve, `Ω` has rank one (`rank_kaehlerDifferential_affineChartAway`).

## Main definitions

* `HodgeLadder.Tests.affineChartAway`

## Main results

* `HodgeLadder.Tests.span_pderiv_affineEquation`, `span_pderiv_infinityEquation`
* `HodgeLadder.Tests.smoothOfRelativeDimension_affineChart`,
  `smoothOfRelativeDimension_infinityChart`
* instances `SmoothOfRelativeDimension 1 ellipticCurve.hom`, `Smooth ellipticCurve.hom`
* `HodgeLadder.Tests.cusp_span_pderiv_ne_top`
* `HodgeLadder.Tests.rank_kaehlerDifferential_affineChartAway`: `Ω` has rank one on the nonzero
  localization `affineChartAway` of the chart `z ≠ 0` away from `2y`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace HodgeLadder.Tests

/-- `∂ₓ(y² − x³ + x) = 1 − 3x²`. -/
theorem pderiv_zero_affineEquation : pderiv 0 affineEquation = 1 - 3 * X 0 ^ 2 := by
  simp [affineEquation, pderiv_X]; ring

/-- `∂_y(y² − x³ + x) = 2y`. -/
theorem pderiv_one_affineEquation : pderiv 1 affineEquation = 2 * X 1 := by
  simp [affineEquation, pderiv_X]

/-- `∂ᵤ(w − u³ + u w²) = w² − 3u²`. -/
theorem pderiv_zero_infinityEquation : pderiv 0 infinityEquation = X 1 ^ 2 - 3 * X 0 ^ 2 := by
  simp [infinityEquation, pderiv_X]; ring

/-- `∂_w(w − u³ + u w²) = 1 + 2uw`. -/
theorem pderiv_one_infinityEquation : pderiv 1 infinityEquation = 1 + 2 * X 0 * X 1 := by
  simp [infinityEquation, pderiv_X]; ring

/-- On the chart `z ≠ 0` the partial derivatives of `y² − x³ + x` generate the unit ideal of
`ℂ[x, y] ⧸ (y² − x³ + x)`: `(4 − 6x²) ∂ₓf − 9xy ∂_y f = 4 − 18x f`. -/
theorem span_pderiv_affineEquation :
    Ideal.span (Set.range fun i : Fin 2 =>
      Ideal.Quotient.mk (Ideal.span {affineEquation}) (pderiv i affineEquation)) = ⊤ := by
  set mk := Ideal.Quotient.mk (Ideal.span {affineEquation})
  have hf : mk (X 1) ^ 2 - mk (X 0) ^ 3 + mk (X 0) = 0 := by
    have : mk (X 1 ^ 2 - X 0 ^ 3 + X 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rwa [map_add, map_sub, map_pow, map_pow] at this
  have h4 : (4 : MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation}) ∈
      Ideal.span (Set.range fun i : Fin 2 => mk (pderiv i affineEquation)) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨![4 - 6 * mk (X 0) ^ 2, -9 * mk (X 0) * mk (X 1)], ?_⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      pderiv_zero_affineEquation, pderiv_one_affineEquation, map_sub, map_mul, map_one, map_pow,
      map_ofNat]
    linear_combination (-18 * mk (X 0)) * hf
  refine Ideal.eq_top_of_isUnit_mem _ h4 ?_
  have : IsUnit (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation}) 4) :=
    (IsUnit.mk0 (4 : ℂ) (by norm_num)).map _
  rwa [map_ofNat] at this

/-- On the chart `y ≠ 0` the partial derivatives of `w − u³ + u w²` generate the unit ideal of
`ℂ[u, w] ⧸ (w − u³ + u w²)`: `u² ∂ᵤh + (1 + uw) ∂_w h = 1 + 3u h`. -/
theorem span_pderiv_infinityEquation :
    Ideal.span (Set.range fun i : Fin 2 =>
      Ideal.Quotient.mk (Ideal.span {infinityEquation}) (pderiv i infinityEquation)) = ⊤ := by
  set mk := Ideal.Quotient.mk (Ideal.span {infinityEquation})
  have hf : mk (X 1) - mk (X 0) ^ 3 + mk (X 0) * mk (X 1) ^ 2 = 0 := by
    have : mk (X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rwa [map_add, map_sub, map_mul, map_pow, map_pow] at this
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
  refine ⟨![mk (X 0) ^ 2, 1 + mk (X 0) * mk (X 1)], ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    pderiv_zero_infinityEquation, pderiv_one_infinityEquation, map_sub, map_mul, map_one, map_pow,
    map_ofNat, map_add]
  linear_combination (3 * mk (X 0)) * hf

/-- The chart `Spec ℂ[x, y] ⧸ (y² − x³ + x)` is smooth of relative dimension one over `Spec ℂ`. -/
theorem smoothOfRelativeDimension_affineChart :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation})))) :=
  HypersurfaceSmooth.smoothOfRelativeDimension_spec affineEquation span_pderiv_affineEquation

/-- The chart `Spec ℂ[u, w] ⧸ (w − u³ + u w²)` is smooth of relative dimension one over
`Spec ℂ`. -/
theorem smoothOfRelativeDimension_infinityChart :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation})))) :=
  HypersurfaceSmooth.smoothOfRelativeDimension_spec infinityEquation span_pderiv_infinityEquation

/-- **The plane cubic `E` is smooth of relative dimension one over `Spec ℂ`**, from its two
charts. -/
instance smoothOfRelativeDimension_ellipticCurve :
    SmoothOfRelativeDimension 1 ellipticCurve.hom := by
  have hP : HasRingHomProperty (@SmoothOfRelativeDimension.{0} 1)
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)) := inferInstance
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ hP
  rw [ellipticCurve_hom]
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun b : Bool => cond b (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2)
      (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1)) ?_ ?_
  · rw [iSup_bool_eq]
    exact ellipticCurve_chart_cover
  · rintro (_ | _)
    · dsimp only [cond]
      have h : SmoothOfRelativeDimension 1 (ellipticCurveChartInfinity.inv ≫ Scheme.Opens.ι _ ≫
          ellipticCurveι ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 2 ℂ) := by
        rw [← Category.assoc (Scheme.Opens.ι _), ← Category.assoc, ellipticCurveChartInfinity_inv_ι,
          Category.assoc, AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
        exact smoothOfRelativeDimension_infinityChart
      rw [← ellipticCurveChartInfinity.hom_inv_id_assoc (Scheme.Opens.ι _ ≫ _)]
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (ellipticCurveChartInfinity.hom ≫ _))
    · dsimp only [cond]
      have h : SmoothOfRelativeDimension 1 (ellipticCurveChartAffine.inv ≫ Scheme.Opens.ι _ ≫
          ellipticCurveι ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 2 ℂ) := by
        rw [← Category.assoc (Scheme.Opens.ι _), ← Category.assoc, ellipticCurveChartAffine_inv_ι,
          Category.assoc, AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
        exact smoothOfRelativeDimension_affineChart
      rw [← ellipticCurveChartAffine.hom_inv_id_assoc (Scheme.Opens.ι _ ≫ _)]
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (ellipticCurveChartAffine.hom ≫ _))

/-- `E` is smooth over `Spec ℂ`. -/
instance smooth_ellipticCurve : Smooth ellipticCurve.hom := SmoothOfRelativeDimension.smooth 1 _

/-- **Test of the hypothesis.** For the cuspidal cubic `y² = x³` the classes of the partial
derivatives `−3x²` and `2y` do not generate the unit ideal of `ℂ[x, y] ⧸ (y² − x³)`: both vanish
under evaluation at the origin, which is a ring map to `ℂ`. -/
theorem cusp_span_pderiv_ne_top :
    Ideal.span (Set.range fun i : Fin 2 =>
      Ideal.Quotient.mk (Ideal.span {(X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) ℂ)})
        (pderiv i (X 1 ^ 2 - X 0 ^ 3))) ≠ ⊤ := by
  intro h
  let φ :
      MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {(X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) ℂ)} →+* ℂ :=
    Ideal.Quotient.lift _ (eval 0) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp
  have hle : Ideal.span (Set.range fun i : Fin 2 =>
      Ideal.Quotient.mk (Ideal.span {(X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) ℂ)})
        (pderiv i (X 1 ^ 2 - X 0 ^ 3))) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [φ, pderiv_X]
  rw [h, top_le_iff] at hle
  exact RingHom.ker_ne_top φ hle

/-- The localization of the affine chart away from `∂_y f = 2y`. -/
abbrev affineChartAway := Localization.Away
  (Ideal.Quotient.mk (Ideal.span {affineEquation}) (pderiv 1 affineEquation))

/-- `(x, y) = (i, 1 − i)` lies on `y² = x³ − x`. -/
theorem affineEquation_eval_I : eval ![Complex.I, 1 - Complex.I] affineEquation = 0 := by
  simp [affineEquation]; ring_nf; simp [Complex.I_sq]

/-- The localization `affineChartAway` is nonzero: evaluation at `(i, 1 − i)` sends `2y` to
`2 − 2i ≠ 0` and so extends to a ring map to `ℂ`. -/
instance : Nontrivial affineChartAway := by
  let ev : MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation} →+* ℂ :=
    Ideal.Quotient.lift _ (eval ![Complex.I, 1 - Complex.I]) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [affineEquation_eval_I]
  have hu : IsUnit (ev (Ideal.Quotient.mk _ (pderiv 1 affineEquation))) := by
    rw [pderiv_one_affineEquation]
    refine isUnit_iff_ne_zero.mpr ?_
    simp [ev]
    intro h
    have := congrArg Complex.re h
    simp at this
  exact (IsLocalization.Away.lift _ hu : affineChartAway →+* ℂ).domain_nontrivial

/-- **Test.** The relative dimension one is the rank of `Ω` on a nonzero chart localization. -/
theorem rank_kaehlerDifferential_affineChartAway :
    Module.rank affineChartAway Ω[affineChartAway⁄ℂ] = 1 := by
  have := HypersurfaceSmooth.isStandardSmoothOfRelativeDimension_away affineEquation (1 : Fin 2)
  simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := affineChartAway) (Fintype.card (Fin 2) - 1)

end HodgeLadder.Tests
