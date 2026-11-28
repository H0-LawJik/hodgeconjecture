module

public import HodgeLadder.General.Hypersurface
public import HodgeLadder.Tests.ProjectivePlane

/-!
# The plane cubic `y²z = x³ − xz²`

Rung `plane-cubic-subscheme`. The cubic `E = V₊(y²z − x³ + xz²) ⊂ ℙ²` over `ℂ`, in the homogeneous
coordinates `x = X 0`, `y = X 1`, `z = X 2`, is `Proj (ℂ[x, y, z] ⧸ (y²z − x³ + xz²))` with the
closed immersion `ellipticCurveι` into Oka's `ℙₒ(2; ℂ)` (`HodgeLadder.General.Hypersurface`).

* `ellipticCurve : Over (Spec ↧ℂ)`, with structure morphism `ellipticCurveι ≫ toSpec 2 ℂ`.
* Projective in upstream's sense: `ellipticCurveι ≫ (okaIsoSpace 2).hom` is a closed immersion
  into `ℙ(Fin (2 + 1); Spec ℂ)` over `Spec ℂ` (`isProjective_ellipticCurve`).
* Charts. Over `z ≠ 0`, `Spec ℂ[x, y] ⧸ (y² − x³ + x)` (`ellipticCurveChartAffine`); over
  `y ≠ 0`, with `u = x / y` and `w = z / y`, `Spec ℂ[u, w] ⧸ (w − u³ + u w²)`
  (`ellipticCurveChartInfinity`). Each lies over the standard chart of `ℙ²` through the quotient
  map, and the two cover `E` (`ellipticCurve_chart_cover`: `y = z = 0` forces `x³ = 0`).
* Tests. The complex points `[0 : 0 : 1]` and `[0 : 1 : 0]` (`ellipticCurveOrigin`,
  `ellipticCurveInfinity`) lie on `E`, read through the standard charts of `ℙ²`; the two-torsion
  points `(±1, 0)` lie on `E` and pin the sign of the linear term; the complement
  of the chart `z ≠ 0` in `E` is the single point `[0 : 1 : 0]` (`compl_chartAffine`).

The construction runs through `Proj` of a graded quotient, so a graded endomorphism of
`ℂ[x, y, z]` preserving `(y²z − x³ + xz²)` induces an endomorphism of `E` by `Proj.map`; this is
the route for `elliptic-curve-cm` (`[x : y : z] ↦ [−x : iy : z]`). No sign convention enters this
file; the sign of the linear term fixes the curve and is recorded in `docs/conventions.md`, row
"Plane cubic E and its charts".

## Main definitions

* `HodgeLadder.Tests.cubicForm`, `ellipticCurveScheme`, `ellipticCurveι`, `ellipticCurve`,
  `ellipticCurveToPlane`
* `HodgeLadder.Tests.affineEquation`, `infinityEquation`, `ellipticCurveChartAffine`,
  `ellipticCurveChartInfinity`
* `HodgeLadder.Tests.chartEval`, `chartComplexPoint`, `ellipticCurveOrigin`,
  `ellipticCurveInfinity`, `ellipticCurveTwoTorsionPos`, `ellipticCurveTwoTorsionNeg`

## Main results

* instances `IsProjective ellipticCurve.hom`, `IsClosedImmersion ellipticCurveToPlane.left`,
  `Nonempty (ComplexPoint ellipticCurve)`, `Nonempty ellipticCurve.left`
* `HodgeLadder.Tests.dehomogenize_two_cubicForm`, `dehomogenize_one_cubicForm`,
  `ellipticCurveChartAffine_inv_ι`, `ellipticCurveChartInfinity_inv_ι`, `ellipticCurve_chart_cover`
* `HodgeLadder.Tests.ellipticCurveOrigin_ι`, `ellipticCurveInfinity_ι`, `compl_chartAffine`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AlgebraicGeometry.ProjectiveSpace

namespace HodgeLadder.Tests

/-- The cubic form `y²z − x³ + xz²` in the homogeneous coordinates `x = X 0`, `y = X 1`,
`z = X 2` of the plane. -/
def cubicForm : MvPolynomial (Fin 3) ℂ := X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2

/-- The cubic form is homogeneous of degree three. -/
theorem cubicForm_mem : cubicForm ∈ homogeneousSubmodule (Fin (2 + 1)) ℂ 3 := by
  rw [mem_homogeneousSubmodule]
  exact ((((isHomogeneous_X ℂ 1).pow 2).mul (isHomogeneous_X ℂ 2)).sub
    ((isHomogeneous_X ℂ 0).pow 3)).add ((isHomogeneous_X ℂ 0).mul ((isHomogeneous_X ℂ 2).pow 2))

/-- The scheme `E = V₊(y²z − x³ + xz²) = Proj (ℂ[x, y, z] ⧸ (y²z − x³ + xz²))`. -/
abbrev ellipticCurveScheme : Scheme := Hypersurface.scheme cubicForm cubicForm_mem

/-- The closed immersion `E ⟶ ℙₒ(2; ℂ)`. -/
abbrev ellipticCurveι : ellipticCurveScheme ⟶ ℙₒ(2; ℂ) :=
  Hypersurface.ι cubicForm cubicForm_mem

/-- **The plane cubic** `E : y²z = x³ − xz²` as a scheme over `Spec ℂ`. -/
abbrev ellipticCurve : Over (Spec ↧ℂ) :=
  Over.mk (ellipticCurveι ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 2 ℂ)

/-- The structure morphism of `E` is the closed immersion followed by `ℙ² ⟶ Spec ℂ`. -/
theorem ellipticCurve_hom :
    ellipticCurve.hom = ellipticCurveι ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 2 ℂ := rfl

/-- The embedding of `E` in the plane `projectivePlane` of `p2-witness`, over `Spec ℂ`. -/
def ellipticCurveToPlane : ellipticCurve ⟶ projectivePlane :=
  Over.homMk (ellipticCurveι ≫ (okaIsoSpace 2).hom) (by
    change (ellipticCurveι ≫ (okaIsoSpace 2).hom) ≫ (projectiveSpace 2).hom = _
    rw [Category.assoc, okaIsoSpace_hom_toBase]
    rfl)

/-- The embedding of `E` into `ℙ²` is a closed immersion. -/
instance isClosedImmersion_ellipticCurveToPlane : IsClosedImmersion ellipticCurveToPlane.left :=
  inferInstanceAs (IsClosedImmersion (ellipticCurveι ≫ (okaIsoSpace 2).hom))

/-- **`E` is projective** in upstream's sense: the closed immersion into `ℙ(Fin (2 + 1); Spec ℂ)`
over `Spec ℂ`. -/
instance isProjective_ellipticCurve : IsProjective ellipticCurve.hom :=
  ⟨⟨{ ambientDimension := 2
      immersion := ellipticCurveι ≫ (okaIsoSpace 2).hom
      immersion_toBase := by
        rw [Category.assoc,
          show ProjectiveSpace.toBase (Fin (2 + 1)) (Spec ↧ℂ) = (projectiveSpace 2).hom from rfl,
          okaIsoSpace_hom_toBase]
        rfl }⟩⟩

/-! ### The two charts -/

/-- Dehomogenization at `z`: `x ↦ X 0`. -/
theorem dehomogenize_two_X_zero : dehomogenize ℂ (2 : Fin 3) (X 0) = X 0 :=
  dehomogenize_X_succAbove (n := 2) 2 0

/-- Dehomogenization at `z`: `y ↦ X 1`. -/
theorem dehomogenize_two_X_one : dehomogenize ℂ (2 : Fin 3) (X 1) = X 1 :=
  dehomogenize_X_succAbove (n := 2) 2 1

/-- Dehomogenization at `z`: `z ↦ 1`. -/
theorem dehomogenize_two_X_two : dehomogenize ℂ (2 : Fin 3) (X 2) = 1 :=
  dehomogenize_X_self (n := 2) 2

/-- Dehomogenization at `y`: `x ↦ X 0` (the coordinate `u = x / y`). -/
theorem dehomogenize_one_X_zero : dehomogenize ℂ (1 : Fin 3) (X 0) = X 0 :=
  dehomogenize_X_succAbove (n := 2) 1 0

/-- Dehomogenization at `y`: `y ↦ 1`. -/
theorem dehomogenize_one_X_one : dehomogenize ℂ (1 : Fin 3) (X 1) = 1 :=
  dehomogenize_X_self (n := 2) 1

/-- Dehomogenization at `y`: `z ↦ X 1` (the coordinate `w = z / y`). -/
theorem dehomogenize_one_X_two : dehomogenize ℂ (1 : Fin 3) (X 2) = X 1 :=
  dehomogenize_X_succAbove (n := 2) 1 1

/-- In the chart `z ≠ 0`, with `x = X 0`, `y = X 1`, the cubic is `y² − x³ + x`. -/
theorem dehomogenize_two_cubicForm :
    dehomogenize ℂ (2 : Fin 3) cubicForm = X 1 ^ 2 - X 0 ^ 3 + X 0 := by
  simp only [cubicForm, map_add, map_sub, map_mul, map_pow, dehomogenize_two_X_zero,
    dehomogenize_two_X_one, dehomogenize_two_X_two]
  ring

/-- In the chart `y ≠ 0`, with `u = X 0 = x / y`, `w = X 1 = z / y`, the cubic is
`w − u³ + u w²`. -/
theorem dehomogenize_one_cubicForm :
    dehomogenize ℂ (1 : Fin 3) cubicForm = X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2 := by
  simp only [cubicForm, map_add, map_sub, map_mul, map_pow, dehomogenize_one_X_zero,
    dehomogenize_one_X_one, dehomogenize_one_X_two]
  ring

/-- The affine equation `y² − x³ + x` of the chart `z ≠ 0`. -/
def affineEquation : MvPolynomial (Fin 2) ℂ := X 1 ^ 2 - X 0 ^ 3 + X 0

/-- The equation `w − u³ + u w²` of the chart `y ≠ 0` at infinity. -/
def infinityEquation : MvPolynomial (Fin 2) ℂ := X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2

/-- The ideal of the chart `z ≠ 0` is `(y² − x³ + x)`. -/
theorem chartIdeal_two : Hypersurface.chartIdeal cubicForm 2 = Ideal.span {affineEquation} := by
  rw [affineEquation, ← dehomogenize_two_cubicForm]

/-- The ideal of the chart `y ≠ 0` is `(w − u³ + u w²)`. -/
theorem chartIdeal_one : Hypersurface.chartIdeal cubicForm 1 = Ideal.span {infinityEquation} := by
  rw [infinityEquation, ← dehomogenize_one_cubicForm]

/-- **The chart `z ≠ 0`** of `E` is `Spec ℂ[x, y] ⧸ (y² − x³ + x)`. -/
def ellipticCurveChartAffine :
    (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2).toScheme ≅
      Spec (.of (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation})) :=
  Hypersurface.chartIso cubicForm cubicForm_mem 2 ≪≫
    Scheme.Spec.mapIso (Ideal.quotEquivOfEq chartIdeal_two).toCommRingCatIso.symm.op

/-- **The chart `y ≠ 0`** of `E` is `Spec ℂ[u, w] ⧸ (w − u³ + u w²)`. -/
def ellipticCurveChartInfinity :
    (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1).toScheme ≅
      Spec (.of (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation})) :=
  Hypersurface.chartIso cubicForm cubicForm_mem 1 ≪≫
    Scheme.Spec.mapIso (Ideal.quotEquivOfEq chartIdeal_one).toCommRingCatIso.symm.op

/-- The chart `z ≠ 0` of `E` lies over the chart `z ≠ 0` of `ℙ²` through the quotient map
`ℂ[x, y] → ℂ[x, y] ⧸ (y² − x³ + x)`. -/
theorem ellipticCurveChartAffine_inv_ι :
    ellipticCurveChartAffine.inv ≫
        (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2).ι ≫ ellipticCurveι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {affineEquation}))) ≫
        AlgebraicGeometry.ProjectiveSpace.chart 2 := by
  rw [ellipticCurveChartAffine, Iso.trans_inv, Category.assoc, Hypersurface.chartIso_inv_ι]
  rw [← Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (Ideal.quotEquivOfEq chartIdeal_two).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The chart `y ≠ 0` of `E` lies over the chart `y ≠ 0` of `ℙ²` through the quotient map
`ℂ[u, w] → ℂ[u, w] ⧸ (w − u³ + u w²)`. -/
theorem ellipticCurveChartInfinity_inv_ι :
    ellipticCurveChartInfinity.inv ≫
        (ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1).ι ≫ ellipticCurveι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {infinityEquation}))) ≫
        AlgebraicGeometry.ProjectiveSpace.chart 1 := by
  rw [ellipticCurveChartInfinity, Iso.trans_inv, Category.assoc, Hypersurface.chartIso_inv_ι]
  rw [← Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (Ideal.quotEquivOfEq chartIdeal_one).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-! ### The two charts cover `E` -/

/-- The relation `x³ = y² z + x z²` in the homogeneous coordinate ring of `E`. -/
theorem π_X_zero_pow_three :
    Hypersurface.π cubicForm cubicForm_mem (X 0) ^ 3 =
      Hypersurface.π cubicForm cubicForm_mem (X 1) ^ 2 *
          Hypersurface.π cubicForm cubicForm_mem (X 2) +
        Hypersurface.π cubicForm cubicForm_mem (X 0) *
          Hypersurface.π cubicForm cubicForm_mem (X 2) ^ 2 := by
  have h : Hypersurface.π cubicForm cubicForm_mem (X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [map_add, map_sub, map_mul, map_mul, map_pow, map_pow, map_pow] at h
  linear_combination -h

/-- **The charts `z ≠ 0` and `y ≠ 0` cover `E`**: on the cubic, `y = z = 0` forces `x = 0`. -/
theorem ellipticCurve_chart_cover :
    ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 ⊔
      ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1 = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  have hx : ellipticCurveι x ∈ ⨆ j, AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j := by
    rw [AlgebraicGeometry.ProjectiveSpace.iSup_U]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  by_contra h
  rw [TopologicalSpace.Opens.mem_sup, not_or] at h
  obtain ⟨h2, h1⟩ := h
  change ¬ x ∈ Proj.basicOpen _ _ at h2 h1
  rw [Proj.mem_basicOpen, not_not] at h2 h1
  have h0 : Hypersurface.π cubicForm cubicForm_mem (X 0) ∈ x.asHomogeneousIdeal := by
    refine x.isPrime.mem_of_pow_mem 3 ?_
    rw [π_X_zero_pow_three]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _
      (Ideal.pow_mem_of_mem _ h2 2 two_pos))
  change x ∈ Proj.basicOpen _ _ at hj
  rw [Proj.mem_basicOpen] at hj
  fin_cases j
  · exact hj h0
  · exact hj h1
  · exact hj h2

/-! ### Complex points -/

/-- Evaluation of the chart ring `ℂ[Y₀, Y₁] ⧸ (dehomogenize i F)` at a zero `v` of the
dehomogenized cubic. -/
def chartEval (i : Fin 3) (v : Fin 2 → ℂ) (hv : eval v (dehomogenize ℂ i cubicForm) = 0) :
    Hypersurface.ChartRing cubicForm i →+* ℂ :=
  Ideal.Quotient.lift _ (eval v) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, hv, zero_mul]

/-- The complex point of `E` in the chart `Xᵢ ≠ 0` with affine coordinates `v`. -/
def chartComplexPoint (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) : ComplexPoint ellipticCurve :=
  Over.homMk (Hypersurface.chartPoint cubicForm cubicForm_mem i (chartEval i v hv)) (by
    change Hypersurface.chartPoint cubicForm cubicForm_mem i (chartEval i v hv) ≫
      ellipticCurveι ≫ _ = 𝟙 (Spec ↧ℂ)
    rw [← Category.assoc, Hypersurface.chartPoint_ι, Category.assoc,
      AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext r
    simp [chartEval])

/-- The chart point of `E`, in `ℙ²`: the point of the standard chart `Xᵢ ≠ 0` of `ℙₒ(2; ℂ)` with
affine coordinates `v`. -/
theorem chartComplexPoint_ι (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) :
    (chartComplexPoint i v hv).left ≫ ellipticCurveι =
      Spec.map (CommRingCat.ofHom (eval v)) ≫ AlgebraicGeometry.ProjectiveSpace.chart i := by
  change Hypersurface.chartPoint cubicForm cubicForm_mem i (chartEval i v hv) ≫ _ = _
  rw [Hypersurface.chartPoint_ι]
  rfl

/-- The affine origin `(x, y) = (0, 0)`, the point `[0 : 0 : 1]` of `E`. -/
def ellipticCurveOrigin : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![0, 0] (by rw [dehomogenize_two_cubicForm]; simp)

/-- The point at infinity `[0 : 1 : 0]` of `E`: the origin `(u, w) = (0, 0)` of the chart
`y ≠ 0`. -/
def ellipticCurveInfinity : ComplexPoint ellipticCurve :=
  chartComplexPoint 1 ![0, 0] (by rw [dehomogenize_one_cubicForm]; simp)

/-- The two-torsion point `(x, y) = (1, 0)`, `[1 : 0 : 1]`; it lies on `y² = x³ − x` and not on
`y² = x³ + x`, so it pins the sign of the linear term. -/
def ellipticCurveTwoTorsionPos : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![1, 0] (by rw [dehomogenize_two_cubicForm]; simp)

/-- The two-torsion point `(x, y) = (−1, 0)`, `[−1 : 0 : 1]`. -/
def ellipticCurveTwoTorsionNeg : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![-1, 0] (by rw [dehomogenize_two_cubicForm]; simp; norm_num)

/-- `[0 : 0 : 1]` lies on `E`: the origin of the chart `z ≠ 0` of `ℙ²` factors through `E`. -/
theorem ellipticCurveOrigin_ι :
    ellipticCurveOrigin.left ≫ ellipticCurveι =
      Spec.map (CommRingCat.ofHom (eval ![0, 0])) ≫ AlgebraicGeometry.ProjectiveSpace.chart 2 :=
  chartComplexPoint_ι _ _ _

/-- `[0 : 1 : 0]` lies on `E`: the origin of the chart `y ≠ 0` of `ℙ²` factors through `E`. -/
theorem ellipticCurveInfinity_ι :
    ellipticCurveInfinity.left ≫ ellipticCurveι =
      Spec.map (CommRingCat.ofHom (eval ![0, 0])) ≫ AlgebraicGeometry.ProjectiveSpace.chart 1 :=
  chartComplexPoint_ι _ _ _

/-- `E` has a complex point. -/
instance nonempty_complexPoint_ellipticCurve : Nonempty (ComplexPoint ellipticCurve) :=
  ⟨ellipticCurveOrigin⟩

/-- The scheme `E` is nonempty. -/
instance nonempty_ellipticCurve : Nonempty ellipticCurve.left :=
  have : Nonempty (Spec ↧ℂ) := inferInstance
  ⟨ellipticCurveOrigin.left.base (Classical.arbitrary (Spec ↧ℂ))⟩

/-! ### The chart `z ≠ 0` misses exactly the point at infinity -/

/-- The point at infinity lies outside the chart `z ≠ 0`. -/
theorem ellipticCurveInfinity_not_mem (p : Spec ↧ℂ) :
    ellipticCurveInfinity.left p ∉
      ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 := by
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ellipticCurveInfinity_ι,
    Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
    AlgebraicGeometry.ProjectiveSpace.chart_preimage_U, dehomogenize_one_X_two]
  intro h
  exact h (show eval ![0, 0] (X 1 : MvPolynomial (Fin 2) ℂ) ∈ p.asIdeal by simp)

/-- In the chart ring `ℂ[u, w] ⧸ (w − u³ + u w²)`, a prime containing `w` contains `p - p(0, 0)`
for every `p`. -/
theorem sub_eval_mem_of_mem (q : Ideal (Hypersurface.ChartRing cubicForm 1)) [q.IsPrime]
    (hw : Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (X 1) ∈ q)
    (p : MvPolynomial (Fin 2) ℂ) :
    Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) p -
      Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1) (C (eval ![0, 0] p)) ∈ q := by
  set mk := Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1)
  have hrel : mk (X 0) ^ 3 = mk (X 1) + mk (X 0) * mk (X 1) ^ 2 := by
    have h : mk (dehomogenize ℂ (1 : Fin 3) cubicForm) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [dehomogenize_one_cubicForm, map_add, map_sub, map_mul, map_pow, map_pow] at h
    linear_combination -h
  have hu : mk (X 0) ∈ q := by
    refine Ideal.IsPrime.mem_of_pow_mem inferInstance 3 ?_
    rw [hrel]
    exact q.add_mem hw (q.mul_mem_left _ (q.pow_mem_of_mem hw 2 two_pos))
  have hX : ∀ k : Fin 2, mk (X k) ∈ q := by
    intro k; fin_cases k
    · exact hu
    · exact hw
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, map_add, C_add, map_add]
    convert q.add_mem h₁ h₂ using 1
    ring
  | mul_X p k hp =>
    simp only [map_mul, eval_X]
    have : (![0, 0] : Fin 2 → ℂ) k = 0 := by fin_cases k <;> rfl
    rw [this, C_0, map_zero, mul_zero, sub_zero]
    exact q.mul_mem_left _ (hX k)

/-- **The chart `z ≠ 0` misses exactly the point at infinity**: its complement in `E` is the single
point `[0 : 1 : 0]`. -/
theorem compl_chartAffine :
    ((ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 : ellipticCurveScheme.Opens) :
      Set ellipticCurveScheme)ᶜ = Set.range ellipticCurveInfinity.left := by
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · have h1 : x ∈ ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1 := by
      have hx' : x ∈ (⊤ : ellipticCurveScheme.Opens) := trivial
      rw [← ellipticCurve_chart_cover, TopologicalSpace.Opens.mem_sup] at hx'
      exact hx'.resolve_left hx
    set W := ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1
    set e := Hypersurface.chartIso cubicForm cubicForm_mem 1
    set mk := Ideal.Quotient.mk (Hypersurface.chartIdeal cubicForm 1)
    let z : (Hypersurface.ι cubicForm cubicForm_mem ⁻¹ᵁ
      AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1).toScheme := ⟨x, h1⟩
    obtain ⟨y, hy0⟩ : ∃ y, y = e.hom z := ⟨_, rfl⟩
    have hy : x = (e.inv ≫ W.ι) y := by
      have key : e.inv (e.hom z) = z := (Scheme.homeoOfIso e).symm_apply_apply z
      rw [Scheme.Hom.comp_apply, hy0, key]
      rfl
    have hyp : y.asIdeal.IsPrime := y.isPrime
    have hw : mk (X 1) ∈ y.asIdeal := by
      have h2 : (e.inv ≫ W.ι) y ∉ ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 :=
        hy ▸ hx
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc,
        Hypersurface.chartIso_inv_ι, Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
        AlgebraicGeometry.ProjectiveSpace.chart_preimage_U, dehomogenize_one_X_two] at h2
      by_contra h3
      exact h2 h3
    have hv : eval ![0, 0] (dehomogenize ℂ (1 : Fin 3) cubicForm) = 0 := by
      rw [dehomogenize_one_cubicForm]; simp
    set φ := chartEval 1 ![0, 0] hv
    have hφ : Function.Surjective φ := fun r => ⟨mk (C r), by simp [φ, chartEval, mk]⟩
    have hle : RingHom.ker φ ≤ y.asIdeal := by
      intro s hs
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
      have h0 : eval ![0, 0] p = 0 := hs
      have := sub_eval_mem_of_mem y.asIdeal hw p
      rwa [h0, C_0, map_zero, sub_zero] at this
    have hker : RingHom.ker φ = y.asIdeal :=
      (RingHom.ker_isMaximal_of_surjective φ hφ).eq_of_le y.isPrime.ne_top hle
    have : Nonempty (Spec ↧ℂ) := inferInstance
    set pt := Classical.arbitrary (Spec ↧ℂ)
    refine ⟨pt, ?_⟩
    have hpt : y = Spec.map (CommRingCat.ofHom φ) pt := by
      apply PrimeSpectrum.ext
      change y.asIdeal = Ideal.comap φ pt.asIdeal
      have : pt.asIdeal.IsPrime := pt.isPrime
      rw [Ideal.eq_bot_of_prime pt.asIdeal, ← RingHom.ker_eq_comap_bot, hker]
    rw [hy, hpt, ← Scheme.Hom.comp_apply]
    rfl
  · rintro ⟨p, rfl⟩
    exact ellipticCurveInfinity_not_mem p

end HodgeLadder.Tests
