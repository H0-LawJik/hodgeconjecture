module

public import HodgeLadder.General.QuotAlgHom
public import HodgeLadder.Tests.EllipticCurveCM
public import HodgeLadder.Tests.EllipticCurveIntegral
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
public import Other.AlgebraicGeometry.ComplexPoint.ClosedImmersion
public import Mathlib.Topology.Algebra.MvPolynomial
public import LefschetzPort.Oka.AlgebraicGeometry.ProjectiveSpace.Points

/-!
# Complex points of the plane cubic in its two charts

Rung `elliptic-curve-points` (T1 plan node C0, `docs/notes/2026-11-27-t1-plan.md`). For the
cubic `E : y²z = x³ − xz²` of `plane-cubic-subscheme`, the complex points of `E` (upstream's
`ComplexPoint`, analytic topology) in the charts `z ≠ 0` and `y ≠ 0` are the two plane curves

* `affineCurve = {(x, y) ∈ ℂ² : y² = x³ − x}` (`ellipticAffineHomeomorph`), and
* `infinityCurve = {(u, w) ∈ ℂ² : w = u³ − u w²}`, `u = x / y`, `w = z / y`
  (`ellipticInfinityHomeomorph`),

with the subspace topology of `ℂ × ℂ`. The two opens cover `E(ℂ)`
(`ellipticAffineOpen_sup_ellipticInfinityOpen`), the complement of the first is the point at
infinity `[0 : 1 : 0]` (`compl_ellipticAffineOpen`), and on the overlap the coordinates are related
by `(x, y) ↦ (x / y, 1 / y)` (`mem_ellipticInfinityOpen_iff`, `ellipticInfinityHomeomorph_of_mem`)
and its inverse `(u, w) ↦ (u / w, 1 / w)` (`ellipticAffineHomeomorph_of_mem`).

## Route

Each chart homeomorphism is a composite of four upstream or local homeomorphisms: the open set
`overOpen U` of `E(ℂ)` is the complex points of the open subscheme `U` (`openHomeomorph`); `U` is
`Spec ℂ[Y₀, Y₁] ⧸ (dehomogenize i F)` over `Spec ℂ` (`chartOverIso`, from `Hypersurface.chartIso`
and `isoMapHomeomorph`); complex points of an affine scheme are the complex algebra homomorphisms
with the topology of pointwise convergence (`affineSpecHomeomorph`); and algebra homomorphisms out
of `ℂ[Y] ⧸ (f)` are the zeros of `f` (`quotAlgHomHomeomorph`, general). The inverse sends `v` to
`chartComplexPoint i v` of `plane-cubic-subscheme` by `rfl` (`chartHomeomorph_symm_apply`).

The transition is read in `ℙ²`: the chart points of the dehomogenizations of `V ∈ ℂ³` at `i` and
at `j` have the same image in `ℙ²` (the port's `chart_base_evalPoint_eq`); the embedding of `E` is
injective on points, and a complex point of a scheme locally of finite type over `ℂ` is determined
by its underlying point (upstream's `underlying_injective_of_locallyOfFiniteType`)
(`chartComplexPoint_dehomogenizeVec_eq`).

## Conventions

Homogeneous coordinates `x = X 0`, `y = X 1`, `z = X 2`; the affine coordinates of the chart
`z ≠ 0` are `(x / z, y / z)`, those of the chart `y ≠ 0` are `(x / y, z / y)`, in the order of
`Fin.succAbove`. No sign or orientation enters; conventions row "Plane cubic E and its charts" in
`docs/conventions.md`.

## Main definitions

* `HodgeLadder.QuotAlgHom.zeroSet`, `quotAlgHomHomeomorph` (`HodgeLadder.General.QuotAlgHom`):
  zeros of `f` and algebra homomorphisms out of `ℂ[Y] ⧸ (f)`.
* `HodgeLadder.Tests.chartOpen`, `chartOverIso`, `chartHomeomorph`: the chart `Xᵢ ≠ 0` of `E(ℂ)`.
* `HodgeLadder.Tests.affineCurve`, `infinityCurve`, `ellipticAffineOpen`, `ellipticInfinityOpen`,
  `ellipticAffineHomeomorph`, `ellipticInfinityHomeomorph`, `affinePoint`, `infinityPoint`.

## Main results

* `HodgeLadder.Tests.chartHomeomorph_symm_apply`, `ellipticAffineHomeomorph_symm_apply`,
  `ellipticInfinityHomeomorph_symm_apply`: the pins.
* `HodgeLadder.Tests.ellipticAffineOpen_sup_ellipticInfinityOpen`: the cover.
* `HodgeLadder.Tests.chartComplexPoint_dehomogenizeVec_eq`, `affinePoint_eq_infinityPoint`,
  `infinityPoint_eq_affinePoint`, `mem_ellipticInfinityOpen_iff`,
  `ellipticInfinityHomeomorph_of_mem`, `mem_ellipticAffineOpen_iff`,
  `ellipticAffineHomeomorph_of_mem`: the transition.
* `HodgeLadder.Tests.compl_ellipticAffineOpen`.
* `HodgeLadder.Tests.isOpenEmbedding_affinePoint`, `isOpenEmbedding_infinityPoint`: the inverse
  charts as open embeddings into `E(ℂ)`.
* Tests: the origin, the two-torsion points `(±1, 0)` and `(i, 1 − i)` have the expected
  coordinates in the chart `z ≠ 0`, and `[0 : 1 : 0]` has coordinates `(0, 0)` in the chart
  `y ≠ 0`; `(i, 1 − i)` has coordinates `((−1 + i) / 2, (1 + i) / 2)` there
  (`ellipticInfinityHomeomorph_chartMeet`).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.Point HodgeLadder.QuotAlgHom

namespace HodgeLadder.Tests

section Charts

/-- The chart `Xᵢ ≠ 0` of `E`, as an open subscheme. -/
abbrev chartOpenScheme (i : Fin 3) : ellipticCurveScheme.Opens :=
  ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ i

/-- The chart isomorphism of `E` lies over `Spec ℂ`. -/
theorem chartIso_hom_structureMap (i : Fin 3) :
    (Hypersurface.chartIso cubicForm cubicForm_mem i).hom ≫
        affineSpecStructureMap (Hypersurface.ChartRing cubicForm i) =
      (chartOpenScheme i).ι ≫ ellipticCurve.hom := by
  rw [← cancel_epi (Hypersurface.chartIso cubicForm cubicForm_mem i).inv, Iso.inv_hom_id_assoc,
    ellipticCurve_hom, reassoc_of% (Hypersurface.chartIso_inv_ι cubicForm cubicForm_mem i),
    AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
  rfl

/-- The chart `Xᵢ ≠ 0` of `E` is `Spec ℂ[Y₀, Y₁] ⧸ (dehomogenize i F)` over `Spec ℂ`. -/
def chartOverIso (i : Fin 3) :
    openScheme ellipticCurve (chartOpenScheme i) ≅
      Over.mk (affineSpecStructureMap (Hypersurface.ChartRing cubicForm i)) :=
  Over.isoMk (Hypersurface.chartIso cubicForm cubicForm_mem i) (chartIso_hom_structureMap i)

/-- The open set of complex points of `E` in the chart `Xᵢ ≠ 0`. -/
def chartOpen (i : Fin 3) : TopologicalSpace.Opens (ComplexPoint ellipticCurve) :=
  ⟨overOpen (chartOpenScheme i), isOpen_overOpen _⟩

/-- **The chart homeomorphism**: the complex points of `E` in the chart `Xᵢ ≠ 0` are the zeros of
the dehomogenized cubic in `ℂ²`. -/
def chartHomeomorph (i : Fin 3) : chartOpen i ≃ₜ zeroSet (dehomogenize ℂ i cubicForm) :=
  (openHomeomorph ellipticCurve (chartOpenScheme i)).symm.trans <|
    (isoMapHomeomorph (chartOverIso i)).trans <|
      (affineSpecHomeomorph (Hypersurface.ChartRing cubicForm i)).trans
        (quotAlgHomHomeomorph _)

/-- The inverse chart homeomorphism sends `v` to the chart point with affine coordinates `v`. -/
theorem chartHomeomorph_symm_apply (i : Fin 3) (v : zeroSet (dehomogenize ℂ i cubicForm)) :
    ((chartHomeomorph i).symm v : ComplexPoint ellipticCurve) = chartComplexPoint i v.1 v.2 := by
  apply Over.OverMorphism.ext
  rfl

/-- A chart point lies in its chart. -/
theorem chartComplexPoint_mem_chartOpen (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) : chartComplexPoint i v hv ∈ chartOpen i := by
  have h := ((chartHomeomorph i).symm ⟨v, hv⟩).2
  rwa [chartHomeomorph_symm_apply] at h

/-- The chart homeomorphism reads off the affine coordinates of a chart point. -/
theorem chartHomeomorph_chartComplexPoint (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) :
    chartHomeomorph i ⟨chartComplexPoint i v hv, chartComplexPoint_mem_chartOpen i v hv⟩ =
      ⟨v, hv⟩ := by
  apply (chartHomeomorph i).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (chartHomeomorph_symm_apply i ⟨v, hv⟩).symm

/-- Every complex point in the chart `Xᵢ ≠ 0` is the chart point of its coordinates. -/
theorem eq_chartComplexPoint (i : Fin 3) (z : chartOpen i) :
    (z : ComplexPoint ellipticCurve) =
      chartComplexPoint i (chartHomeomorph i z).1 (chartHomeomorph i z).2 := by
  rw [← chartHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

/-- **The charts `z ≠ 0` and `y ≠ 0` cover `E(ℂ)`.** -/
theorem chartOpen_two_sup_one : chartOpen 2 ⊔ chartOpen 1 = ⊤ := by
  refine top_le_iff.mp fun z _ => ?_
  have h : z.underlying ∈ (⊤ : ellipticCurveScheme.Opens) := trivial
  rw [← ellipticCurve_chart_cover, TopologicalSpace.Opens.mem_sup] at h
  exact TopologicalSpace.Opens.mem_sup.mpr h

/-- A chart point of `E`, in `ℙ²`, at the point of `Spec ℂ`: Oka's chart applied to the point of
evaluation at `v`. -/
theorem ι_chartComplexPoint_apply (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) (p : Spec ↧ℂ) :
    ellipticCurveι ((chartComplexPoint i v hv).left p) =
      (AlgebraicGeometry.ProjectiveSpace.chart i).base
        (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v) := by
  rw [← Scheme.Hom.comp_apply, chartComplexPoint_ι, Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  have : p.asIdeal.IsPrime := p.isPrime
  change Ideal.comap (eval v) p.asIdeal = RingHom.ker (eval₂Hom _ v)
  rw [Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
  rfl

/-- The image in `ℙ²` of the underlying point of a chart point is Oka's chart applied to the point
of evaluation at `v`. -/
theorem ι_underlying_chartComplexPoint (i : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) :
    ellipticCurveι (chartComplexPoint i v hv).underlying =
      (AlgebraicGeometry.ProjectiveSpace.chart i).base
        (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v) :=
  ι_chartComplexPoint_apply i v hv _

/-- A chart point lies in the chart `Xⱼ ≠ 0` exactly when `Xⱼ`, dehomogenized at `i`, does not
vanish at its coordinates. -/
theorem chartComplexPoint_mem_chartOpen_iff (i j : Fin 3) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) :
    chartComplexPoint i v hv ∈ chartOpen j ↔ eval v (dehomogenize ℂ i (X j)) ≠ 0 := by
  change ellipticCurveι (chartComplexPoint i v hv).underlying ∈
    AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j ↔ _
  rw [ι_underlying_chartComplexPoint]
  change AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v ∈
    AlgebraicGeometry.ProjectiveSpace.chart i ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j ↔ _
  rw [AlgebraicGeometry.ProjectiveSpace.chart_preimage_U]
  change dehomogenize ℂ i (X j) ∉ (show PrimeSpectrum (MvPolynomial (Fin 2) ℂ) from
    AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v).asIdeal ↔ _
  rw [AlgebraicGeometry.ProjectiveSpace.mem_evalPoint_asIdeal_iff]
  rfl

/-- **The chart transition** in homogeneous coordinates: for a point `V` of the cubic with
`Vᵢ ≠ 0` and `Vⱼ ≠ 0`, the chart points of its dehomogenizations at `i` and at `j` agree. -/
theorem chartComplexPoint_dehomogenizeVec_eq (i j : Fin 3) (V : Fin 3 → ℂ) (hi : V i ≠ 0)
    (hj : V j ≠ 0)
    (hvi : eval (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec i V)
      (dehomogenize ℂ i cubicForm) = 0)
    (hvj : eval (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec j V)
      (dehomogenize ℂ j cubicForm) = 0) :
    chartComplexPoint i _ hvi = chartComplexPoint j _ hvj := by
  apply underlying_injective_of_locallyOfFiniteType
  apply ellipticCurveι.isClosedEmbedding.injective
  rw [ι_underlying_chartComplexPoint, ι_underlying_chartComplexPoint]
  exact AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_eq (RingHom.id ℂ) i j V hi hj

end Charts

section Curve

/-- The affine curve `{(x, y) ∈ ℂ² : y² = x³ − x}` of the chart `z ≠ 0`. -/
def affineCurve : Set (ℂ × ℂ) := {p | p.2 ^ 2 = p.1 ^ 3 - p.1}

/-- The curve `{(u, w) ∈ ℂ² : w = u³ − u w²}` of the chart `y ≠ 0`, with `u = x / y`,
`w = z / y`. -/
def infinityCurve : Set (ℂ × ℂ) := {p | p.2 = p.1 ^ 3 - p.1 * p.2 ^ 2}

/-- The equation of the chart `z ≠ 0` at `v`. -/
theorem eval_dehomogenize_two_cubicForm (v : Fin 2 → ℂ) :
    eval v (dehomogenize ℂ 2 cubicForm) = v 1 ^ 2 - v 0 ^ 3 + v 0 := by
  rw [dehomogenize_two_cubicForm]; simp

/-- The equation of the chart `y ≠ 0` at `v`. -/
theorem eval_dehomogenize_one_cubicForm (v : Fin 2 → ℂ) :
    eval v (dehomogenize ℂ 1 cubicForm) = v 1 - v 0 ^ 3 + v 0 * v 1 ^ 2 := by
  rw [dehomogenize_one_cubicForm]; simp

/-- A zero of the equation of the chart `z ≠ 0` is a point of `y² = x³ − x`. -/
theorem eval_dehomogenize_two_eq_zero_iff (v : Fin 2 → ℂ) :
    eval v (dehomogenize ℂ 2 cubicForm) = 0 ↔ (v 0, v 1) ∈ affineCurve := by
  rw [eval_dehomogenize_two_cubicForm]
  change _ ↔ v 1 ^ 2 = v 0 ^ 3 - v 0
  constructor <;> intro h <;> linear_combination h

/-- A zero of the equation of the chart `y ≠ 0` is a point of `w = u³ − u w²`. -/
theorem eval_dehomogenize_one_eq_zero_iff (v : Fin 2 → ℂ) :
    eval v (dehomogenize ℂ 1 cubicForm) = 0 ↔ (v 0, v 1) ∈ infinityCurve := by
  rw [eval_dehomogenize_one_cubicForm]
  change _ ↔ v 1 = v 0 ^ 3 - v 0 * v 1 ^ 2
  constructor <;> intro h <;> linear_combination h

/-- The zero set of the chart `z ≠ 0` in `Fin 2 → ℂ` is the affine curve in `ℂ × ℂ`. -/
def zeroSetTwoHomeomorph : zeroSet (dehomogenize ℂ 2 cubicForm) ≃ₜ affineCurve :=
  Homeomorph.finTwoArrow.subtype fun v => eval_dehomogenize_two_eq_zero_iff v

/-- The zero set of the chart `y ≠ 0` in `Fin 2 → ℂ` is the curve `w = u³ − u w²` in
`ℂ × ℂ`. -/
def zeroSetOneHomeomorph : zeroSet (dehomogenize ℂ 1 cubicForm) ≃ₜ infinityCurve :=
  Homeomorph.finTwoArrow.subtype fun v => eval_dehomogenize_one_eq_zero_iff v

/-- The open set `z ≠ 0` of `E(ℂ)`. -/
abbrev ellipticAffineOpen : TopologicalSpace.Opens (ComplexPoint ellipticCurve) := chartOpen 2

/-- The open set `y ≠ 0` of `E(ℂ)`. -/
abbrev ellipticInfinityOpen : TopologicalSpace.Opens (ComplexPoint ellipticCurve) := chartOpen 1

/-- **The chart `z ≠ 0` of `E(ℂ)`**: homeomorphic to `{(x, y) ∈ ℂ² : y² = x³ − x}`. -/
def ellipticAffineHomeomorph : ellipticAffineOpen ≃ₜ affineCurve :=
  (chartHomeomorph 2).trans zeroSetTwoHomeomorph

/-- **The chart `y ≠ 0` of `E(ℂ)`**: homeomorphic to `{(u, w) ∈ ℂ² : w = u³ − u w²}`. -/
def ellipticInfinityHomeomorph : ellipticInfinityOpen ≃ₜ infinityCurve :=
  (chartHomeomorph 1).trans zeroSetOneHomeomorph

/-- **The two charts cover `E(ℂ)`.** -/
theorem ellipticAffineOpen_sup_ellipticInfinityOpen :
    ellipticAffineOpen ⊔ ellipticInfinityOpen = ⊤ :=
  chartOpen_two_sup_one

/-- The complex point `[x : y : 1]` of `E` for `(x, y)` on `y² = x³ − x`. -/
def affinePoint (p : affineCurve) : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![p.1.1, p.1.2] ((eval_dehomogenize_two_eq_zero_iff _).mpr p.2)

/-- The complex point `[u : 1 : w]` of `E` for `(u, w)` on `w = u³ − u w²`. -/
def infinityPoint (q : infinityCurve) : ComplexPoint ellipticCurve :=
  chartComplexPoint 1 ![q.1.1, q.1.2] ((eval_dehomogenize_one_eq_zero_iff _).mpr q.2)

/-- The inverse of the chart `z ≠ 0` is `(x, y) ↦ [x : y : 1]`. -/
theorem ellipticAffineHomeomorph_symm_apply (p : affineCurve) :
    (ellipticAffineHomeomorph.symm p : ComplexPoint ellipticCurve) = affinePoint p :=
  chartHomeomorph_symm_apply 2 _

/-- The inverse of the chart `y ≠ 0` is `(u, w) ↦ [u : 1 : w]`. -/
theorem ellipticInfinityHomeomorph_symm_apply (q : infinityCurve) :
    (ellipticInfinityHomeomorph.symm q : ComplexPoint ellipticCurve) = infinityPoint q :=
  chartHomeomorph_symm_apply 1 _

/-- `(x, y) ↦ [x : y : 1]` is an open embedding of the affine curve into `E(ℂ)`. -/
theorem isOpenEmbedding_affinePoint : Topology.IsOpenEmbedding affinePoint := by
  have h : affinePoint = (Subtype.val : ellipticAffineOpen → ComplexPoint ellipticCurve) ∘
      ellipticAffineHomeomorph.symm :=
    funext fun p => (ellipticAffineHomeomorph_symm_apply p).symm
  rw [h]
  exact ellipticAffineOpen.isOpen.isOpenEmbedding_subtypeVal.comp
    ellipticAffineHomeomorph.symm.isOpenEmbedding

/-- `(u, w) ↦ [u : 1 : w]` is an open embedding of the curve at infinity into `E(ℂ)`. -/
theorem isOpenEmbedding_infinityPoint : Topology.IsOpenEmbedding infinityPoint := by
  have h : infinityPoint = (Subtype.val : ellipticInfinityOpen → ComplexPoint ellipticCurve) ∘
      ellipticInfinityHomeomorph.symm :=
    funext fun q => (ellipticInfinityHomeomorph_symm_apply q).symm
  rw [h]
  exact ellipticInfinityOpen.isOpen.isOpenEmbedding_subtypeVal.comp
    ellipticInfinityHomeomorph.symm.isOpenEmbedding

/-- `[x : y : 1]` lies in the chart `z ≠ 0`. -/
theorem affinePoint_mem (p : affineCurve) : affinePoint p ∈ ellipticAffineOpen :=
  chartComplexPoint_mem_chartOpen 2 _ _

/-- `[u : 1 : w]` lies in the chart `y ≠ 0`. -/
theorem infinityPoint_mem (q : infinityCurve) : infinityPoint q ∈ ellipticInfinityOpen :=
  chartComplexPoint_mem_chartOpen 1 _ _

/-- The chart `z ≠ 0` reads off `(x, y)` at `[x : y : 1]`. -/
theorem ellipticAffineHomeomorph_affinePoint (p : affineCurve) :
    ellipticAffineHomeomorph ⟨affinePoint p, affinePoint_mem p⟩ = p := by
  apply ellipticAffineHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (ellipticAffineHomeomorph_symm_apply p).symm

/-- The chart `y ≠ 0` reads off `(u, w)` at `[u : 1 : w]`. -/
theorem ellipticInfinityHomeomorph_infinityPoint (q : infinityCurve) :
    ellipticInfinityHomeomorph ⟨infinityPoint q, infinityPoint_mem q⟩ = q := by
  apply ellipticInfinityHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (ellipticInfinityHomeomorph_symm_apply q).symm

/-- Every point of the chart `z ≠ 0` is `[x : y : 1]` for its coordinates `(x, y)`. -/
theorem eq_affinePoint (z : ellipticAffineOpen) :
    (z : ComplexPoint ellipticCurve) = affinePoint (ellipticAffineHomeomorph z) := by
  rw [← ellipticAffineHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

/-- Every point of the chart `y ≠ 0` is `[u : 1 : w]` for its coordinates `(u, w)`. -/
theorem eq_infinityPoint (z : ellipticInfinityOpen) :
    (z : ComplexPoint ellipticCurve) = infinityPoint (ellipticInfinityHomeomorph z) := by
  rw [← ellipticInfinityHomeomorph_symm_apply, Homeomorph.symm_apply_apply]

/-- `[x : y : 1]` lies in the chart `y ≠ 0` exactly when `y ≠ 0`. -/
theorem affinePoint_mem_ellipticInfinityOpen_iff (p : affineCurve) :
    affinePoint p ∈ ellipticInfinityOpen ↔ p.1.2 ≠ 0 := by
  rw [affinePoint, chartComplexPoint_mem_chartOpen_iff, dehomogenize_two_X_one]
  simp

/-- `[u : 1 : w]` lies in the chart `z ≠ 0` exactly when `w ≠ 0`. -/
theorem infinityPoint_mem_ellipticAffineOpen_iff (q : infinityCurve) :
    infinityPoint q ∈ ellipticAffineOpen ↔ q.1.2 ≠ 0 := by
  rw [infinityPoint, chartComplexPoint_mem_chartOpen_iff, dehomogenize_one_X_two]
  simp

/-- `(2 : Fin 3).succAbove 1 = 1`. -/
theorem succAbove_two_one : (2 : Fin 3).succAbove 1 = 1 := rfl

/-- The transition `(x, y) ↦ (x / y, 1 / y)` maps the affine curve off `y = 0` into the curve at
infinity. -/
theorem affineToInfinity_mem (p : affineCurve) (hy : p.1.2 ≠ 0) :
    (p.1.1 / p.1.2, 1 / p.1.2) ∈ infinityCurve := by
  have h : p.1.2 ^ 2 = p.1.1 ^ 3 - p.1.1 := p.2
  change 1 / p.1.2 = (p.1.1 / p.1.2) ^ 3 - p.1.1 / p.1.2 * (1 / p.1.2) ^ 2
  field_simp
  linear_combination h

/-- The transition `(u, w) ↦ (u / w, 1 / w)` maps the curve at infinity off `w = 0` into the
affine curve. -/
theorem infinityToAffine_mem (q : infinityCurve) (hw : q.1.2 ≠ 0) :
    (q.1.1 / q.1.2, 1 / q.1.2) ∈ affineCurve := by
  have h : q.1.2 = q.1.1 ^ 3 - q.1.1 * q.1.2 ^ 2 := q.2
  change (1 / q.1.2) ^ 2 = (q.1.1 / q.1.2) ^ 3 - q.1.1 / q.1.2
  field_simp
  linear_combination h

/-- **The chart transition, as points**: for `y ≠ 0`, `[x : y : 1] = [x / y : 1 : 1 / y]`. -/
theorem affinePoint_eq_infinityPoint (p : affineCurve) (hy : p.1.2 ≠ 0) :
    affinePoint p = infinityPoint ⟨_, affineToInfinity_mem p hy⟩ := by
  set V : Fin 3 → ℂ := ![p.1.1, p.1.2, 1]
  have e2 : AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 2 V = ![p.1.1, p.1.2] := by
    funext m
    fin_cases m <;>
      simp [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec, V, succAbove_two_one]
  have e1 : AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 1 V =
      ![p.1.1 / p.1.2, 1 / p.1.2] := by
    funext m; fin_cases m <;> simp [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec, V]
  have h2 := (eval_dehomogenize_two_eq_zero_iff ![p.1.1, p.1.2]).mpr p.2
  have h1 := (eval_dehomogenize_one_eq_zero_iff ![p.1.1 / p.1.2, 1 / p.1.2]).mpr
    (affineToInfinity_mem p hy)
  exact (chartComplexPoint_congr 2 e2.symm _ (e2 ▸ h2)).trans
    ((chartComplexPoint_dehomogenizeVec_eq 2 1 V (by simp [V]) (by simpa [V] using hy)
      (e2 ▸ h2) (e1 ▸ h1)).trans (chartComplexPoint_congr 1 e1 _ _))

/-- The chart transition the other way: for `w ≠ 0`, `[u : 1 : w] = [u / w : 1 / w : 1]`. -/
theorem infinityPoint_eq_affinePoint (q : infinityCurve) (hw : q.1.2 ≠ 0) :
    infinityPoint q = affinePoint ⟨_, infinityToAffine_mem q hw⟩ := by
  set V : Fin 3 → ℂ := ![q.1.1, 1, q.1.2]
  have e1 : AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 1 V = ![q.1.1, q.1.2] := by
    funext m; fin_cases m <;> simp [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec, V]
  have e2 : AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 2 V =
      ![q.1.1 / q.1.2, 1 / q.1.2] := by
    funext m
    fin_cases m <;>
      simp [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec, V, succAbove_two_one]
  have h1 := (eval_dehomogenize_one_eq_zero_iff ![q.1.1, q.1.2]).mpr q.2
  have h2 := (eval_dehomogenize_two_eq_zero_iff ![q.1.1 / q.1.2, 1 / q.1.2]).mpr
    (infinityToAffine_mem q hw)
  exact (chartComplexPoint_congr 1 e1.symm _ (e1 ▸ h1)).trans
    ((chartComplexPoint_dehomogenizeVec_eq 1 2 V (by simp [V]) (by simpa [V] using hw)
      (e1 ▸ h1) (e2 ▸ h2)).trans (chartComplexPoint_congr 2 e2 _ _))

/-- **The transition map on the overlap.** A point of the chart `z ≠ 0` with coordinates
`(x, y)` lies in the chart `y ≠ 0` exactly when `y ≠ 0`. -/
theorem mem_ellipticInfinityOpen_iff (z : ellipticAffineOpen) :
    (z : ComplexPoint ellipticCurve) ∈ ellipticInfinityOpen ↔
      (ellipticAffineHomeomorph z : ℂ × ℂ).2 ≠ 0 := by
  rw [eq_affinePoint z, affinePoint_mem_ellipticInfinityOpen_iff]

/-- **The transition map on the overlap.** A point of the chart `z ≠ 0` with coordinates
`(x, y)`, `y ≠ 0`, has coordinates `(x / y, 1 / y)` in the chart `y ≠ 0`. -/
theorem ellipticInfinityHomeomorph_of_mem (z : ellipticAffineOpen)
    (hz : (z : ComplexPoint ellipticCurve) ∈ ellipticInfinityOpen) :
    (ellipticInfinityHomeomorph ⟨z, hz⟩ : ℂ × ℂ) =
      ((ellipticAffineHomeomorph z : ℂ × ℂ).1 / (ellipticAffineHomeomorph z : ℂ × ℂ).2,
        1 / (ellipticAffineHomeomorph z : ℂ × ℂ).2) := by
  have hy := (mem_ellipticInfinityOpen_iff z).mp hz
  have h : (⟨z, hz⟩ : ellipticInfinityOpen) =
      ⟨infinityPoint ⟨_, affineToInfinity_mem _ hy⟩, infinityPoint_mem _⟩ :=
    Subtype.ext ((eq_affinePoint z).trans (affinePoint_eq_infinityPoint _ hy))
  rw [h, ellipticInfinityHomeomorph_infinityPoint]

/-- A point of the chart `y ≠ 0` with coordinates `(u, w)` lies in the chart `z ≠ 0` exactly
when `w ≠ 0`. -/
theorem mem_ellipticAffineOpen_iff (z : ellipticInfinityOpen) :
    (z : ComplexPoint ellipticCurve) ∈ ellipticAffineOpen ↔
      (ellipticInfinityHomeomorph z : ℂ × ℂ).2 ≠ 0 := by
  rw [eq_infinityPoint z, infinityPoint_mem_ellipticAffineOpen_iff]

/-- The inverse transition: a point of the chart `y ≠ 0` with coordinates `(u, w)`, `w ≠ 0`, has
coordinates `(u / w, 1 / w)` in the chart `z ≠ 0`. -/
theorem ellipticAffineHomeomorph_of_mem (z : ellipticInfinityOpen)
    (hz : (z : ComplexPoint ellipticCurve) ∈ ellipticAffineOpen) :
    (ellipticAffineHomeomorph ⟨z, hz⟩ : ℂ × ℂ) =
      ((ellipticInfinityHomeomorph z : ℂ × ℂ).1 / (ellipticInfinityHomeomorph z : ℂ × ℂ).2,
        1 / (ellipticInfinityHomeomorph z : ℂ × ℂ).2) := by
  have hw := (mem_ellipticAffineOpen_iff z).mp hz
  have h : (⟨z, hz⟩ : ellipticAffineOpen) =
      ⟨affinePoint ⟨_, infinityToAffine_mem _ hw⟩, affinePoint_mem _⟩ :=
    Subtype.ext ((eq_infinityPoint z).trans (infinityPoint_eq_affinePoint _ hw))
  rw [h, ellipticAffineHomeomorph_affinePoint]

end Curve

section Tests

/-- A chart point of the chart `z ≠ 0` with coordinates `(p.1, p.2)` is `affinePoint p`. -/
theorem chartComplexPoint_two_eq_affinePoint (p : affineCurve) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ 2 cubicForm) = 0) (h0 : v 0 = p.1.1) (h1 : v 1 = p.1.2) :
    chartComplexPoint 2 v hv = affinePoint p :=
  chartComplexPoint_congr 2 (by funext m; fin_cases m <;> simp [h0, h1]) _ _

/-- A chart point of the chart `y ≠ 0` with coordinates `(q.1, q.2)` is `infinityPoint q`. -/
theorem chartComplexPoint_one_eq_infinityPoint (q : infinityCurve) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ 1 cubicForm) = 0) (h0 : v 0 = q.1.1) (h1 : v 1 = q.1.2) :
    chartComplexPoint 1 v hv = infinityPoint q :=
  chartComplexPoint_congr 1 (by funext m; fin_cases m <;> simp [h0, h1]) _ _

/-- The chart `z ≠ 0` at a point equal to `affinePoint p` reads `p`. -/
theorem ellipticAffineHomeomorph_of_eq {z : ComplexPoint ellipticCurve}
    (hz : z ∈ ellipticAffineOpen) {p : affineCurve} (h : z = affinePoint p) :
    ellipticAffineHomeomorph ⟨z, hz⟩ = p := by
  subst h
  exact ellipticAffineHomeomorph_affinePoint p

/-- The chart `y ≠ 0` at a point equal to `infinityPoint q` reads `q`. -/
theorem ellipticInfinityHomeomorph_of_eq {z : ComplexPoint ellipticCurve}
    (hz : z ∈ ellipticInfinityOpen) {q : infinityCurve} (h : z = infinityPoint q) :
    ellipticInfinityHomeomorph ⟨z, hz⟩ = q := by
  subst h
  exact ellipticInfinityHomeomorph_infinityPoint q

/-- The origin `(0, 0)` is on `y² = x³ − x`. -/
theorem zero_mem_affineCurve : ((0, 0) : ℂ × ℂ) ∈ affineCurve := by simp [affineCurve]

/-- The origin `(0, 0)` is on `w = u³ − u w²`. -/
theorem zero_mem_infinityCurve : ((0, 0) : ℂ × ℂ) ∈ infinityCurve := by simp [infinityCurve]

/-- `(1, 0)` is on `y² = x³ − x`. -/
theorem one_zero_mem_affineCurve : ((1, 0) : ℂ × ℂ) ∈ affineCurve := by simp [affineCurve]

/-- `(−1, 0)` is on `y² = x³ − x`. -/
theorem neg_one_zero_mem_affineCurve : ((-1, 0) : ℂ × ℂ) ∈ affineCurve := by
  simp [affineCurve]; norm_num

/-- `(i, 1 − i)` is on `y² = x³ − x`. -/
theorem chartMeet_mem_affineCurve : ((Complex.I, 1 - Complex.I) : ℂ × ℂ) ∈ affineCurve :=
  (eval_dehomogenize_two_eq_zero_iff ![Complex.I, 1 - Complex.I]).mp eval_chartMeet

/-- The origin `[0 : 0 : 1]` is the affine point `(0, 0)`. -/
theorem ellipticCurveOrigin_eq :
    ellipticCurveOrigin = affinePoint ⟨(0, 0), zero_mem_affineCurve⟩ :=
  chartComplexPoint_two_eq_affinePoint _ _ _ rfl rfl

/-- The point at infinity `[0 : 1 : 0]` is the point `(u, w) = (0, 0)` of the chart `y ≠ 0`. -/
theorem ellipticCurveInfinity_eq :
    ellipticCurveInfinity = infinityPoint ⟨(0, 0), zero_mem_infinityCurve⟩ :=
  chartComplexPoint_one_eq_infinityPoint _ _ _ rfl rfl

/-- The two-torsion point `[1 : 0 : 1]` is the affine point `(1, 0)`. -/
theorem ellipticCurveTwoTorsionPos_eq :
    ellipticCurveTwoTorsionPos = affinePoint ⟨(1, 0), one_zero_mem_affineCurve⟩ :=
  chartComplexPoint_two_eq_affinePoint _ _ _ rfl rfl

/-- The two-torsion point `[−1 : 0 : 1]` is the affine point `(−1, 0)`. -/
theorem ellipticCurveTwoTorsionNeg_eq :
    ellipticCurveTwoTorsionNeg = affinePoint ⟨(-1, 0), neg_one_zero_mem_affineCurve⟩ :=
  chartComplexPoint_two_eq_affinePoint _ _ _ rfl rfl

/-- The point `[i : 1 − i : 1]` is the affine point `(i, 1 − i)`. -/
theorem ellipticCurveChartMeet_eq :
    ellipticCurveChartMeet = affinePoint ⟨_, chartMeet_mem_affineCurve⟩ :=
  chartComplexPoint_two_eq_affinePoint _ _ _ rfl rfl

/-- The origin lies in the chart `z ≠ 0`. -/
theorem ellipticCurveOrigin_mem : ellipticCurveOrigin ∈ ellipticAffineOpen := by
  rw [ellipticCurveOrigin_eq]; exact affinePoint_mem _

/-- The point at infinity lies in the chart `y ≠ 0`. -/
theorem ellipticCurveInfinity_mem : ellipticCurveInfinity ∈ ellipticInfinityOpen := by
  rw [ellipticCurveInfinity_eq]; exact infinityPoint_mem _

/-- `[1 : 0 : 1]` lies in the chart `z ≠ 0`. -/
theorem ellipticCurveTwoTorsionPos_mem : ellipticCurveTwoTorsionPos ∈ ellipticAffineOpen := by
  rw [ellipticCurveTwoTorsionPos_eq]; exact affinePoint_mem _

/-- `[−1 : 0 : 1]` lies in the chart `z ≠ 0`. -/
theorem ellipticCurveTwoTorsionNeg_mem : ellipticCurveTwoTorsionNeg ∈ ellipticAffineOpen := by
  rw [ellipticCurveTwoTorsionNeg_eq]; exact affinePoint_mem _

/-- `[i : 1 − i : 1]` lies in the chart `z ≠ 0`. -/
theorem ellipticCurveChartMeet_mem : ellipticCurveChartMeet ∈ ellipticAffineOpen := by
  rw [ellipticCurveChartMeet_eq]; exact affinePoint_mem _

/-- **Test.** The chart `z ≠ 0` sends the origin to `(0, 0)`. -/
theorem ellipticAffineHomeomorph_origin :
    (ellipticAffineHomeomorph ⟨ellipticCurveOrigin, ellipticCurveOrigin_mem⟩ : ℂ × ℂ) = (0, 0) :=
  congrArg Subtype.val (ellipticAffineHomeomorph_of_eq _ ellipticCurveOrigin_eq)

/-- **Test.** The chart `y ≠ 0` sends the point at infinity to `(0, 0)`. -/
theorem ellipticInfinityHomeomorph_infinity :
    (ellipticInfinityHomeomorph ⟨ellipticCurveInfinity, ellipticCurveInfinity_mem⟩ : ℂ × ℂ) =
      (0, 0) :=
  congrArg Subtype.val (ellipticInfinityHomeomorph_of_eq _ ellipticCurveInfinity_eq)

/-- **Test.** The chart `z ≠ 0` sends `[1 : 0 : 1]` to `(1, 0)`. -/
theorem ellipticAffineHomeomorph_twoTorsionPos :
    (ellipticAffineHomeomorph ⟨ellipticCurveTwoTorsionPos, ellipticCurveTwoTorsionPos_mem⟩ :
      ℂ × ℂ) = (1, 0) :=
  congrArg Subtype.val (ellipticAffineHomeomorph_of_eq _ ellipticCurveTwoTorsionPos_eq)

/-- **Test.** The chart `z ≠ 0` sends `[−1 : 0 : 1]` to `(−1, 0)`. -/
theorem ellipticAffineHomeomorph_twoTorsionNeg :
    (ellipticAffineHomeomorph ⟨ellipticCurveTwoTorsionNeg, ellipticCurveTwoTorsionNeg_mem⟩ :
      ℂ × ℂ) = (-1, 0) :=
  congrArg Subtype.val (ellipticAffineHomeomorph_of_eq _ ellipticCurveTwoTorsionNeg_eq)

/-- **Test.** The chart `z ≠ 0` sends `[i : 1 − i : 1]` to `(i, 1 − i)`. -/
theorem ellipticAffineHomeomorph_chartMeet :
    (ellipticAffineHomeomorph ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem⟩ : ℂ × ℂ) =
      (Complex.I, 1 - Complex.I) :=
  congrArg Subtype.val (ellipticAffineHomeomorph_of_eq _ ellipticCurveChartMeet_eq)

/-- **Test.** The point at infinity lies outside the chart `z ≠ 0`. -/
theorem ellipticCurveInfinity_not_mem_ellipticAffineOpen :
    ellipticCurveInfinity ∉ ellipticAffineOpen := by
  rw [ellipticCurveInfinity_eq, infinityPoint_mem_ellipticAffineOpen_iff]
  simp

/-- **Test.** The origin lies outside the chart `y ≠ 0`. -/
theorem ellipticCurveOrigin_not_mem_ellipticInfinityOpen :
    ellipticCurveOrigin ∉ ellipticInfinityOpen := by
  rw [ellipticCurveOrigin_eq, affinePoint_mem_ellipticInfinityOpen_iff]
  simp

/-- **Test.** The two-torsion points `(±1, 0)` lie outside the chart `y ≠ 0`. -/
theorem ellipticCurveTwoTorsion_not_mem_ellipticInfinityOpen :
    ellipticCurveTwoTorsionPos ∉ ellipticInfinityOpen ∧
      ellipticCurveTwoTorsionNeg ∉ ellipticInfinityOpen := by
  rw [ellipticCurveTwoTorsionPos_eq, ellipticCurveTwoTorsionNeg_eq,
    affinePoint_mem_ellipticInfinityOpen_iff, affinePoint_mem_ellipticInfinityOpen_iff]
  simp

/-- `1 − i ≠ 0`. -/
theorem one_sub_I_ne_zero : (1 - Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- `[i : 1 − i : 1]` lies in the chart `y ≠ 0`. -/
theorem ellipticCurveChartMeet_mem_ellipticInfinityOpen :
    ellipticCurveChartMeet ∈ ellipticInfinityOpen := by
  rw [ellipticCurveChartMeet_eq, affinePoint_mem_ellipticInfinityOpen_iff]
  exact one_sub_I_ne_zero

/-- **Test of the transition.** In the chart `y ≠ 0`, `[i : 1 − i : 1]` has coordinates
`(i / (1 − i), 1 / (1 − i)) = ((−1 + i) / 2, (1 + i) / 2)`. -/
theorem ellipticInfinityHomeomorph_chartMeet :
    (ellipticInfinityHomeomorph ⟨ellipticCurveChartMeet,
        ellipticCurveChartMeet_mem_ellipticInfinityOpen⟩ : ℂ × ℂ) =
      ((-1 + Complex.I) / 2, (1 + Complex.I) / 2) := by
  rw [ellipticInfinityHomeomorph_of_mem ⟨ellipticCurveChartMeet, ellipticCurveChartMeet_mem⟩
    ellipticCurveChartMeet_mem_ellipticInfinityOpen, ellipticAffineHomeomorph_chartMeet]
  have h := one_sub_I_ne_zero
  refine Prod.ext ?_ ?_
  · change Complex.I / (1 - Complex.I) = (-1 + Complex.I) / 2
    rw [div_eq_div_iff h two_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  · change 1 / (1 - Complex.I) = (1 + Complex.I) / 2
    rw [div_eq_div_iff h two_ne_zero]
    ring_nf
    simp [Complex.I_sq]
    norm_num

/-- **The complement of the chart `z ≠ 0` in `E(ℂ)` is the point at infinity `[0 : 1 : 0]`.** -/
theorem compl_ellipticAffineOpen :
    (ellipticAffineOpen : Set (ComplexPoint ellipticCurve))ᶜ = {ellipticCurveInfinity} := by
  ext z
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · intro hz
    have h1 : z ∈ ellipticInfinityOpen := by
      have h : z ∈ (⊤ : TopologicalSpace.Opens (ComplexPoint ellipticCurve)) := trivial
      rw [← ellipticAffineOpen_sup_ellipticInfinityOpen, TopologicalSpace.Opens.mem_sup] at h
      exact h.resolve_left hz
    have hw : (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).2 = 0 := by
      by_contra h
      exact hz ((mem_ellipticAffineOpen_iff ⟨z, h1⟩).mpr h)
    have hq : (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).2 =
        (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).1 ^ 3 -
          (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).1 *
            (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).2 ^ 2 :=
      (ellipticInfinityHomeomorph ⟨z, h1⟩).2
    rw [hw] at hq
    have hu : (ellipticInfinityHomeomorph ⟨z, h1⟩ : ℂ × ℂ).1 = 0 :=
      pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination -hq)
    refine (eq_infinityPoint ⟨z, h1⟩).trans ?_
    rw [ellipticCurveInfinity_eq]
    congr 1
    exact Subtype.ext (Prod.ext hu hw)
  · rintro rfl
    exact ellipticCurveInfinity_not_mem_ellipticAffineOpen

end Tests

end HodgeLadder.Tests
