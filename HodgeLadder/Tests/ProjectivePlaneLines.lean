module

public import HodgeLadder.Tests.ProjectiveChart
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# Two coordinate lines of ℙ² meeting transversally in a point

Rung `p2-lines-transversal`: the inputs of `cycle-class-multiplicative` on ℙ² for the coordinate
lines `L₀ = {x₀ = 0}`, `L₁ = {x₁ = 0}` and the point `[0 : 0 : 1]`, in the exact form of its
hypotheses `hx`, `hw`, `ht`, `hT`, `htr`, `hxreg`, `hwreg` at `a = b = 1`, `d = 2`.

All three scheme points come from the chart `x₂ ≠ 0` of upstream's ℙ², Oka's
`ProjectiveSpace.chart 2 : Spec ℂ[Y₀, Y₁] → ℙₒ(2; ℂ)` followed by `okaIsoSpace 2`, with
`Yₘ = xₘ / x₂` (`projectiveChartImmersion 2 2`, rung `affine-chart-analytic-p2`):

* `planeLine k` (`k = 0, 1`) is the image of the prime `(Y_k)`, the kernel of the restriction
  `planeLineRestrict k : ℂ[Y₀, Y₁] → ℂ[T]`, `Y_k ↦ 0`, the other coordinate `↦ T`;
* `planeOrigin` is the underlying point of `planeOriginPoint`, the inverse of the analytic chart
  `projectiveChart 2 2` at `0`, i.e. the image of the maximal ideal `(Y₀, Y₁)`.

The coordinate order matters for `htr`: `L₀` is coordinate `0` and `L₁` coordinate `1` of
`projectiveChart 2 2` (conventions row "Algebraic affine chart and the standard chart of ℙⁿ").

Route. Coheights: `[0 : 0 : 1] < L_k < ⊤` in the specialization order, and upstream's bound
`coheight ≤ 2` on a smooth surface. Supports: `L_k` lies off the standard open `x_k ≠ 0`, so
`L₀(ℂ) ∩ L₁(ℂ)` lies in the chart `x₂ ≠ 0`, where `L_k(ℂ)` is `{v_k = 0}`. Smooth locus: the
open `x₂ ≠ 0` is affine, `U.fromSpec` differs from the chart by a ring isomorphism
`ℂ[Y₀, Y₁] ≅ Γ(U)` (`isoOfRangeEq`, `Spec.preimage`), and the vanishing ideal of `L_k` on `U`
pulls back to `(Y_k)`.

## Main definitions

* `HodgeLadder.Tests.planeLineRestrict`, `planeLinePrime`, `planeEvalPoint`, `planeChartPoint`
* `HodgeLadder.Tests.planeLine`, `planeOriginPoint`, `planeOrigin`

## Main results

* `HodgeLadder.Tests.coheight_planeLine`, `coheight_planeOrigin` (`hx`, `hw`, `ht`)
* `HodgeLadder.Tests.planeOrigin_support_eq_inter` (`hT`), `planeOrigin_support_eq_singleton`
* `HodgeLadder.Tests.mem_planeLine_support_iff`, `planeLines_transversal` (`htr`)
* `HodgeLadder.Tests.planeOrigin_support_subset_smoothSupportAmbientOpen` (`hxreg`, `hwreg`),
  from `cycleComponent_planeLine_mem_smoothLocus`: on the affine open `x₂ ≠ 0` the chart of
  Mathlib's `subschemeCover` of the reduced closure of `L_k` is `Spec ℂ[T]` over `ℂ`
  (`smooth_quotient_of_comap_eq_planeLinePrime`, `projectiveChartImmersion_two_over`)
* `HodgeLadder.Tests.closure_planeLine_inter`: `closure {L₀} ∩ closure {L₁} = closure {[0 : 0 : 1]}`
  at the level of scheme points, from `planeEvalPoint_zero_le`
* `HodgeLadder.Tests.planeLine_zero_ne_one`
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Normalization

/-! ### The scheme points -/

/-- Restriction of `ℂ[Y₀, Y₁]` to the coordinate line `Y_k = 0`: `Y_k ↦ 0`, and the other
coordinate `Y_{1-k} ↦ T`. -/
def planeLineRestrict (k : Fin 2) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval (fun m => if m = k then 0 else MvPolynomial.X 0)

/-- The restriction to a coordinate line is surjective. -/
theorem planeLineRestrict_surjective (k : Fin 2) :
    Function.Surjective (planeLineRestrict k) := by
  have hX : MvPolynomial.X 0 ∈ Set.range (planeLineRestrict k) :=
    ⟨MvPolynomial.X k.rev, by
      rw [planeLineRestrict, MvPolynomial.aeval_X]
      fin_cases k <;> rfl⟩
  intro f
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [planeLineRestrict]⟩
  | add p q hp hq =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    exact ⟨p' + q', map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨x, hx⟩ := hX
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact ⟨p' * x, by rw [map_mul, hx]⟩

/-- The prime `(Y_k)` of `ℂ[Y₀, Y₁]`, the coordinate ring of the chart `x₂ ≠ 0` with
`Yₘ = xₘ / x₂`: the kernel of `planeLineRestrict k`. -/
def planeLinePrime (k : Fin 2) : PrimeSpectrum (MvPolynomial (Fin 2) ℂ) :=
  ⟨RingHom.ker (planeLineRestrict k).toRingHom, RingHom.ker_isPrime _⟩

/-- The point of `Spec ℂ[Y₀, Y₁]` cut out by evaluation at `v`, as a prime (the port's
`ProjectiveSpace.evalPoint (RingHom.id ℂ) v`, typed as a `PrimeSpectrum`). -/
def planeEvalPoint (v : Fin 2 → ℂ) : PrimeSpectrum (MvPolynomial (Fin 2) ℂ) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) v), RingHom.ker_isPrime _⟩

/-- A point of the chart `x₂ ≠ 0` of upstream's ℙ², from a prime of `ℂ[Y₀, Y₁]`. -/
def planeChartPoint (q : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) : projectivePlane.left :=
  (projectiveChartImmersion 2 2).base q

/-- The coordinate line `L_k = {x_k = 0}` of ℙ², `k = 0, 1`, as the scheme point of its generic
point. -/
def planeLine (k : Fin 2) : projectivePlane.left := planeChartPoint (planeLinePrime k)

/-- The complex point `[0 : 0 : 1]` of ℙ², the inverse of the chart `x₂ ≠ 0` at the origin. -/
def planeOriginPoint : ComplexPoint projectivePlane := (projectiveChart 2 2).symm 0

/-- The scheme point `[0 : 0 : 1]` of ℙ². -/
def planeOrigin : projectivePlane.left := planeOriginPoint.underlying

/-! ### Primes of `ℂ[Y₀, Y₁]` and the chart -/

/-- `Y_m ∈ (Y_k)` exactly when `m = k`. -/
theorem X_mem_planeLinePrime_iff (k m : Fin 2) :
    (MvPolynomial.X m : MvPolynomial (Fin 2) ℂ) ∈ (planeLinePrime k).asIdeal ↔ m = k := by
  change planeLineRestrict k (MvPolynomial.X m) = 0 ↔ _
  rw [planeLineRestrict, MvPolynomial.aeval_X]
  by_cases h : m = k
  · simp [h]
  · simp [h, MvPolynomial.X_ne_zero]

/-- Membership in the prime of evaluation at `v`. -/
theorem mem_planeEvalPoint_iff (v : Fin 2 → ℂ) (f : MvPolynomial (Fin 2) ℂ) :
    f ∈ (planeEvalPoint v).asIdeal ↔ MvPolynomial.eval v f = 0 :=
  RingHom.mem_ker

/-- The point `v` lies on the line `Y_k = 0` of `Spec ℂ[Y₀, Y₁]` exactly when `v_k = 0`. -/
theorem planeLinePrime_le_planeEvalPoint_iff (k : Fin 2) (v : Fin 2 → ℂ) :
    (planeLinePrime k).asIdeal ≤ (planeEvalPoint v).asIdeal ↔ v k = 0 := by
  constructor
  · intro h
    have hX := h ((X_mem_planeLinePrime_iff k k).mpr rfl)
    rw [mem_planeEvalPoint_iff] at hX
    simpa using hX
  · intro hv f hf
    rw [mem_planeEvalPoint_iff]
    have hcomp : (MvPolynomial.aeval (fun _ : Fin 1 => v k.rev)).comp (planeLineRestrict k) =
        MvPolynomial.aeval v := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, planeLineRestrict, MvPolynomial.aeval_X]
      by_cases h : i = k
      · subst h
        simp [hv]
      · have : i = k.rev := by fin_cases i <;> fin_cases k <;> simp_all
        rw [this] at h ⊢
        simp [h]
    have hf' : planeLineRestrict k f = 0 := hf
    have := congrArg (fun φ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ => φ f) hcomp
    simp only [AlgHom.comp_apply, hf', map_zero] at this
    exact this.symm

/-- The chart `x₂ ≠ 0` reflects and preserves specialization: an open embedding. -/
theorem planeChartPoint_specializes_iff (q q' : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) :
    planeChartPoint q ⤳ planeChartPoint q' ↔ q.asIdeal ≤ q'.asIdeal :=
  ((projectiveChartImmersion 2 2).isOpenEmbedding.isInducing.specializes_iff (x := q)
    (y := q')).trans (PrimeSpectrum.le_iff_specializes q q').symm

/-- A point of the chart `x₂ ≠ 0` lies in the standard open `x_j ≠ 0` exactly when the
dehomogenization of `x_j` is not in its prime. -/
theorem planeChartPoint_mem_U_iff (q : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) (j : Fin 3) :
    planeChartPoint q ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j ↔
      MvPolynomial.dehomogenize ℂ 2 (MvPolynomial.X j) ∉ q.asIdeal := by
  change (okaIsoSpace 2).hom.base ((AlgebraicGeometry.ProjectiveSpace.chart 2).base q) ∈ _ ↔ _
  rw [Scheme.Hom.apply_mem_image_iff]
  change q ∈ AlgebraicGeometry.ProjectiveSpace.chart (n := 2) (R := ℂ) 2 ⁻¹ᵁ
    AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j ↔ _
  rw [AlgebraicGeometry.ProjectiveSpace.chart_preimage_U]
  rfl

/-- On the chart `x₂ ≠ 0`, `x_k / x₂ = Y_k` for `k = 0, 1`. -/
theorem dehomogenize_two_X_castSucc (k : Fin 2) :
    MvPolynomial.dehomogenize ℂ (2 : Fin 3) (MvPolynomial.X k.castSucc) = MvPolynomial.X k := by
  have : k.castSucc = (2 : Fin 3).succAbove k := by fin_cases k <;> rfl
  rw [this, MvPolynomial.dehomogenize_X_succAbove]

/-- The inverse of the analytic chart `x₂ ≠ 0` at `v` has underlying point the chart image of the
prime of evaluation at `v`. -/
theorem projectiveChart_two_symm_underlying (v : Fin 2 → ℂ) :
    ((projectiveChart 2 2).symm v).underlying = planeChartPoint (planeEvalPoint v) := by
  rw [projectiveChart_symm_underlying]
  rfl

/-- `[0 : 0 : 1]` is the chart image of the maximal ideal `(Y₀, Y₁)`. -/
theorem planeOrigin_eq : planeOrigin = planeChartPoint (planeEvalPoint 0) :=
  projectiveChart_two_symm_underlying 0

/-- A complex point lies in the source of the chart `x₂ ≠ 0` exactly when its underlying point
lies in the standard open `x₂ ≠ 0`. -/
theorem mem_projectiveChart_two_source_iff (z : ComplexPoint projectivePlane) :
    z ∈ (projectiveChart 2 2).source ↔
      z.underlying ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 := by
  rw [← projectiveChartOpen_eq, projectiveChart, affineChart_source]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Point.underlying_map]
    exact q.underlying.property
  · intro h
    exact ⟨(openEquiv _ _).symm ⟨z, h⟩,
      congrArg Subtype.val ((openEquiv _ _).apply_symm_apply _)⟩

/-- `[0 : 0 : 1]` lies in the source of the chart `x₂ ≠ 0`. -/
theorem planeOriginPoint_mem_source : planeOriginPoint ∈ (projectiveChart 2 2).source :=
  (projectiveChart 2 2).map_target (by rw [projectiveChart, affineChart_target]; trivial)

/-- The chart `x₂ ≠ 0` sends `[0 : 0 : 1]` to the origin. -/
theorem projectiveChart_planeOriginPoint : projectiveChart 2 2 planeOriginPoint = 0 :=
  (projectiveChart 2 2).right_inv (by rw [projectiveChart, affineChart_target]; trivial)

/-- The three standard opens cover upstream's ℙ². -/
theorem exists_mem_U (y : projectivePlane.left) :
    ∃ j : Fin 3, y ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j := by
  have hcov : (okaIsoSpace 2).inv.base y ∈ (⨆ j, AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j) :=
    (AlgebraicGeometry.ProjectiveSpace.iSup_U 2 ℂ) ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  refine ⟨j, ?_⟩
  have := (Scheme.Hom.apply_mem_image_iff (okaIsoSpace 2).hom).mpr hj
  simpa using this

/-! ### Position of the lines -/

/-- `L_k` lies off the standard open `x_k ≠ 0`. -/
theorem planeLine_not_mem_U (k : Fin 2) :
    planeLine k ∉ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ k.castSucc := by
  rw [planeLine, planeChartPoint_mem_U_iff, dehomogenize_two_X_castSucc, not_not]
  exact (X_mem_planeLinePrime_iff k k).mpr rfl

/-- The closure of `L_k` lies off the standard open `x_k ≠ 0`. -/
theorem closure_planeLine_subset (k : Fin 2) :
    closure {planeLine k} ⊆
      ((okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ k.castSucc : Set _)ᶜ :=
  closure_minimal (Set.singleton_subset_iff.mpr (planeLine_not_mem_U k))
    ((Opens.isOpen _).isClosed_compl)

/-- The generic point of ℙ² lies in every standard open. -/
theorem top_mem_U (j : Fin 3) :
    (⊤ : projectivePlane.left) ∈
      (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j := by
  have hz : planeChartPoint (planeEvalPoint (fun _ => 1)) ∈
      (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ j := by
    rw [planeChartPoint_mem_U_iff, mem_planeEvalPoint_iff]
    obtain rfl | ⟨m, rfl⟩ := Fin.eq_self_or_eq_succAbove 2 j
    · simp
    · simp
  exact ((Scheme.le_iff_specializes).mp le_top).mem_open (Opens.isOpen _) hz

/-- `L_k` is not the generic point of ℙ². -/
theorem planeLine_lt_top (k : Fin 2) : planeLine k < ⊤ := by
  refine lt_of_le_not_ge le_top fun h => ?_
  have h1 : (⊤ : projectivePlane.left) ∈ closure {planeLine k} :=
    specializes_iff_mem_closure.mp ((Scheme.le_iff_specializes).mp h)
  exact closure_planeLine_subset k h1 (top_mem_U k.castSucc)

/-- `[0 : 0 : 1]` is a proper specialization of `L_k`. -/
theorem planeOrigin_lt_planeLine (k : Fin 2) : planeOrigin < planeLine k := by
  rw [planeOrigin_eq, planeLine]
  refine lt_of_le_not_ge ?_ ?_
  · rw [Scheme.le_iff_specializes, planeChartPoint_specializes_iff,
      planeLinePrime_le_planeEvalPoint_iff]
    rfl
  · rw [Scheme.le_iff_specializes, planeChartPoint_specializes_iff]
    intro h
    fin_cases k
    · have := (X_mem_planeLinePrime_iff 0 1).mp
        (h ((mem_planeEvalPoint_iff _ _).mpr (by simp)))
      exact absurd this (by decide)
    · have := (X_mem_planeLinePrime_iff 1 0).mp
        (h ((mem_planeEvalPoint_iff _ _).mpr (by simp)))
      exact absurd this (by decide)

/-- The two lines are different scheme points. -/
theorem planeLine_zero_ne_one : planeLine 0 ≠ planeLine 1 := by
  intro h
  have h' := (projectiveChartImmersion 2 2).isOpenEmbedding.injective h
  have hP : planeLinePrime 0 = planeLinePrime 1 := h'
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ∈ (planeLinePrime 1).asIdeal :=
    hP ▸ (X_mem_planeLinePrime_iff 0 0).mpr rfl
  exact absurd ((X_mem_planeLinePrime_iff 1 0).mp h0) (by decide)

/-! ### Coheights: hypotheses `hx`, `hw`, `ht` -/

/-- The coordinate lines have coheight one. -/
theorem coheight_planeLine (k : Fin 2) : Order.coheight (planeLine k) = (1 : ℕ) := by
  have h1 := Order.coheight_add_one_le (planeLine_lt_top k)
  have h2 := Order.coheight_add_one_le (planeOrigin_lt_planeLine k)
  have h3 : Order.coheight planeOrigin ≤ (2 : ℕ) :=
    SmoothOfRelativeDimension.coheight_le_complex (f := projectivePlane.hom) (d := 2) planeOrigin
  rw [Order.coheight_top, zero_add] at h1
  have h4 := h2.trans h3
  generalize Order.coheight (planeLine k) = c at h1 h4 ⊢
  induction c using ENat.recTopCoe with
  | top => simp at h4
  | coe n =>
    norm_cast at h1 h4 ⊢
    omega

/-- The point `[0 : 0 : 1]` has coheight two. -/
theorem coheight_planeOrigin : Order.coheight planeOrigin = (2 : ℕ) := by
  have h2 := Order.coheight_add_one_le (planeOrigin_lt_planeLine 0)
  have h3 : Order.coheight planeOrigin ≤ (2 : ℕ) :=
    SmoothOfRelativeDimension.coheight_le_complex (f := projectivePlane.hom) (d := 2) planeOrigin
  rw [coheight_planeLine 0] at h2
  refine le_antisymm h3 ?_
  have h22 : ((2 : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + 1 := by norm_num
  rw [h22]
  exact h2

/-! ### Supports: hypotheses `hT` and `htr` -/

/-- In the chart `x₂ ≠ 0`, the line `L_k(ℂ)` is the coordinate hyperplane `{v_k = 0}`. -/
theorem mem_planeLine_support_iff (k : Fin 2) (z : ComplexPoint projectivePlane)
    (hz : z ∈ (projectiveChart 2 2).source) :
    z ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine k) ↔
      projectiveChart 2 2 z k = 0 := by
  have hz' : (projectiveChart 2 2).symm (projectiveChart 2 2 z) = z :=
    (projectiveChart 2 2).left_inv hz
  change z.underlying ∈ closure {planeLine k} ↔ _
  conv_lhs => rw [← hz']
  rw [projectiveChart_two_symm_underlying, ← specializes_iff_mem_closure, planeLine,
    planeChartPoint_specializes_iff, planeLinePrime_le_planeEvalPoint_iff]

/-- `L₀(ℂ) ∩ L₁(ℂ)` is the single complex point `[0 : 0 : 1]`. -/
theorem mem_planeLine_inter_iff (y : ComplexPoint projectivePlane) :
    (y ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0) ∧
      y ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 1)) ↔
      y = planeOriginPoint := by
  constructor
  · rintro ⟨h0, h1⟩
    have h0' : y.underlying ∉
        (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 0 :=
      closure_planeLine_subset 0 h0
    have h1' : y.underlying ∉
        (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1 :=
      closure_planeLine_subset 1 h1
    obtain ⟨j, hj⟩ := exists_mem_U y.underlying
    have hy : y ∈ (projectiveChart 2 2).source := by
      rw [mem_projectiveChart_two_source_iff]
      fin_cases j
      · exact absurd hj h0'
      · exact absurd hj h1'
      · exact hj
    have e0 := (mem_planeLine_support_iff 0 y hy).mp h0
    have e1 := (mem_planeLine_support_iff 1 y hy).mp h1
    have hv : projectiveChart 2 2 y = 0 := by
      funext m
      fin_cases m
      · exact e0
      · exact e1
    rw [← (projectiveChart 2 2).left_inv hy, hv]
    rfl
  · rintro rfl
    exact ⟨(mem_planeLine_support_iff 0 _ planeOriginPoint_mem_source).mpr
        (by rw [projectiveChart_planeOriginPoint]; rfl),
      (mem_planeLine_support_iff 1 _ planeOriginPoint_mem_source).mpr
        (by rw [projectiveChart_planeOriginPoint]; rfl)⟩

/-- `L₀(ℂ) ∩ L₁(ℂ)` is the support of `[0 : 0 : 1]`: hypothesis `hT` of
`cycle-class-multiplicative`. -/
theorem planeOrigin_support_eq_inter :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) =
      (cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0) :
          Set (ComplexPoint projectivePlane)) ∩
        cycleComponentAnalyticClosedSupport projectivePlane (planeLine 1) := by
  ext y
  refine ⟨fun hy => ⟨?_, ?_⟩, fun hy => ?_⟩
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 0).le) hy
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 1).le) hy
  · rw [(mem_planeLine_inter_iff y).mp hy]
    exact subset_closure rfl

/-- The support of `[0 : 0 : 1]` is the single complex point `[0 : 0 : 1]`. -/
theorem planeOrigin_support_eq_singleton :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) = {planeOriginPoint} := by
  rw [planeOrigin_support_eq_inter]
  ext y
  exact mem_planeLine_inter_iff y

/-- A prime of `ℂ[Y₀, Y₁]` containing `Y₀` and `Y₁` contains the maximal ideal `(Y₀, Y₁)`. -/
theorem planeEvalPoint_zero_le (q : PrimeSpectrum (MvPolynomial (Fin 2) ℂ))
    (h0 : (planeLinePrime 0).asIdeal ≤ q.asIdeal) (h1 : (planeLinePrime 1).asIdeal ≤ q.asIdeal) :
    (planeEvalPoint 0).asIdeal ≤ q.asIdeal := by
  intro f hf
  rw [mem_planeEvalPoint_iff] at hf
  have hspan : f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := by ext i; exact hcon i trivial
    subst hm0
    rw [MvPolynomial.mem_support_iff] at hm
    apply hm
    have := hf
    rw [MvPolynomial.eval_zero] at this
    simpa [MvPolynomial.constantCoeff] using this
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, -, rfl⟩
  fin_cases i
  · exact h0 ((X_mem_planeLinePrime_iff 0 0).mpr rfl)
  · exact h1 ((X_mem_planeLinePrime_iff 1 1).mpr rfl)

/-- At the level of scheme points, `L₀ ∩ L₁` is the closure of `[0 : 0 : 1]`: the point is the only
component of the intersection. -/
theorem closure_planeLine_inter :
    closure {planeLine 0} ∩ closure {planeLine 1} =
      closure ({planeOrigin} : Set projectivePlane.left) := by
  ext y
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun hy => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := exists_mem_U y
    have hy2 : y ∈ (okaIsoSpace 2).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2 := by
      fin_cases j
      · exact absurd hj (closure_planeLine_subset 0 h0)
      · exact absurd hj (closure_planeLine_subset 1 h1)
      · exact hj
    rw [← projectiveChartOpen_eq] at hy2
    obtain ⟨q, rfl⟩ := hy2
    have h0' := (planeChartPoint_specializes_iff (planeLinePrime 0) q).mp
      (specializes_iff_mem_closure.mpr h0)
    have h1' := (planeChartPoint_specializes_iff (planeLinePrime 1) q).mp
      (specializes_iff_mem_closure.mpr h1)
    rw [planeOrigin_eq]
    exact specializes_iff_mem_closure.mp
      ((planeChartPoint_specializes_iff (planeEvalPoint 0) q).mpr
        (planeEvalPoint_zero_le q h0' h1'))
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 0).le) hy
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp (planeOrigin_lt_planeLine 1).le) hy

/-- The chart `x₂ ≠ 0` is adapted to both lines at every point of their intersection, `L₀` as
coordinate `0` and `L₁` as coordinate `1`: hypothesis `htr` of `cycle-class-multiplicative` with
`a = b = 1`, `d = 2`. -/
theorem planeLines_transversal :
    ∀ y ∈ (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint projectivePlane),
        y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 0) ↔
            ∀ i : Fin 1, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport projectivePlane (planeLine 1) ↔
            ∀ j : Fin 1, φ z ⟨1 + j, by omega⟩ = 0) := by
  intro y hy
  rw [planeOrigin_support_eq_singleton] at hy
  rw [Set.mem_singleton_iff.mp hy]
  refine ⟨projectiveChart 2 2, projectivePlane_chart_mem_maximalAtlas 2,
    planeOriginPoint_mem_source, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_planeLine_support_iff 0 z hz]
    exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩
  · rw [mem_planeLine_support_iff 1 z hz]
    exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩

/-! ### Smooth locus: hypotheses `hxreg`, `hwreg` -/

/-- The chart `x₂ ≠ 0` lies over `Spec ℂ` through the constants `MvPolynomial.C`. -/
theorem projectiveChartImmersion_two_over :
    projectiveChartImmersion 2 2 ≫ projectivePlane.hom =
      Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
  change (AlgebraicGeometry.ProjectiveSpace.chart 2 ≫ (okaIsoSpace 2).hom) ≫ _ = _
  rw [Category.assoc, okaIsoSpace_hom_toBase, AlgebraicGeometry.ProjectiveSpace.chart_toSpec]

/-- Ring-level step: if `φ : ℂ[Y₀, Y₁] → Γ` is bijective and `J` pulls back to `(Y_k)`, then
`ℂ → Γ ⧸ J` (through `MvPolynomial.C` and `φ`) is smooth, since `Γ ⧸ J ≅ ℂ[T]` compatibly with
the constants. -/
theorem smooth_quotient_of_comap_eq_planeLinePrime {Γ : Type} [CommRing Γ]
    (φ : MvPolynomial (Fin 2) ℂ →+* Γ) (hφ : Function.Bijective φ) (J : Ideal Γ) (k : Fin 2)
    (hJ : J.comap φ = (planeLinePrime k).asIdeal) :
    ((Ideal.Quotient.mk J).comp (φ.comp MvPolynomial.C)).Smooth := by
  set θ : MvPolynomial (Fin 2) ℂ →+* Γ ⧸ J := (Ideal.Quotient.mk J).comp φ with hθ
  have hθs : Function.Surjective θ := Ideal.Quotient.mk_surjective.comp hφ.2
  have hker : RingHom.ker θ = RingHom.ker (planeLineRestrict k).toRingHom := by
    rw [hθ, ← RingHom.comap_ker, Ideal.mk_ker]
    exact hJ
  let ψ : MvPolynomial (Fin 1) ℂ ≃+* Γ ⧸ J :=
    ((RingHom.quotientKerEquivOfSurjective (planeLineRestrict_surjective k)).symm.trans
      (Ideal.quotEquivOfEq hker.symm)).trans (RingHom.quotientKerEquivOfSurjective hθs)
  have hψ : ∀ a, ψ (planeLineRestrict k a) = θ a := by
    intro a
    have h1 : (RingHom.quotientKerEquivOfSurjective (planeLineRestrict_surjective k)).symm
        (planeLineRestrict k a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [ψ, RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk]
    rfl
  have hcomp : (Ideal.Quotient.mk J).comp (φ.comp MvPolynomial.C) =
      ψ.toRingHom.comp (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 1) ℂ) := by
    ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hC : (MvPolynomial.C c : MvPolynomial (Fin 1) ℂ) =
        planeLineRestrict k (MvPolynomial.C c) := by simp [planeLineRestrict]
    rw [hC, hψ, hθ]
    rfl
  rw [hcomp]
  exact RingHom.Smooth.comp (RingHom.smooth_algebraMap.mpr inferInstance)
    (RingHom.Smooth.of_bijective ψ.bijective)

/-- Every point of the reduced closure of `L_k` over `[0 : 0 : 1]` lies in its smooth locus over
`ℂ`. Route: on the affine open `x₂ ≠ 0`, the vanishing-ideal subscheme `cycleComponent` is
`Spec (Γ(U) / I(U))` (Mathlib's `subschemeCover`), with `I(U)` the prime `(Y_k)` transported along
`Γ(U) ≅ ℂ[Y₀, Y₁]`, so that chart is `Spec ℂ[T]`, smooth over `ℂ`. -/
theorem cycleComponent_planeLine_mem_smoothLocus (k : Fin 2)
    (z : cycleComponent projectivePlane.left (planeLine k))
    (hz : cycleComponentι projectivePlane.left (planeLine k) z = planeOrigin) :
    z ∈ (cycleComponentι projectivePlane.left (planeLine k) ≫ projectivePlane.hom).smoothLocus := by
  have hUa : IsAffineOpen (projectiveChartImmersion 2 2).opensRange :=
    isAffineOpen_opensRange _
  let U : projectivePlane.left.affineOpens := ⟨(projectiveChartImmersion 2 2).opensRange, hUa⟩
  let I := Scheme.IdealSheafData.vanishingIdeal (X := projectivePlane.left)
    ⟨closure {planeLine k}, isClosed_closure⟩
  change z ∈ (I.subschemeι ≫ projectivePlane.hom).smoothLocus
  have hzU : z ∈ I.subschemeι ⁻¹ᵁ U.1 := by
    change cycleComponentι projectivePlane.left (planeLine k) z ∈ (projectiveChartImmersion 2 2).opensRange
    rw [hz, planeOrigin_eq]
    exact ⟨_, rfl⟩
  rw [← Scheme.IdealSheafData.opensRange_subschemeCover_map] at hzU
  obtain ⟨w, rfl⟩ := hzU
  let j := I.subschemeCover.f U
  have : IsOpenImmersion j :=
    (inferInstance : IsOpenImmersion (I.subschemeCover.f (show I.subschemeCover.I₀ from U)))
  change j w ∈ _
  rw [← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq]
  suffices hs : Smooth (j ≫ I.subschemeι ≫ projectivePlane.hom) by
    rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have hrange : Set.range (projectiveChartImmersion 2 2) = Set.range hUa.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]; rfl
  let g := IsOpenImmersion.isoOfRangeEq (projectiveChartImmersion 2 2) hUa.fromSpec hrange
  let φ := Spec.preimage g.inv
  have hφ : Spec.map φ = g.inv := Spec.map_preimage _
  have hfrom : hUa.fromSpec = Spec.map φ ≫ projectiveChartImmersion 2 2 := by
    rw [hφ, IsOpenImmersion.isoOfRangeEq_inv_fac]
  have hcomp : j ≫ I.subschemeι ≫ projectivePlane.hom =
      Spec.map (CommRingCat.ofHom MvPolynomial.C ≫ φ ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) := by
    rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι,
      Scheme.IdealSheafData.glueDataObjι_ι, hfrom]
    rw [Spec.map_comp, Spec.map_comp, ← projectiveChartImmersion_two_over]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ t)
        (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm)
  rw [hcomp]
  refine (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr ?_
  have hbij : Function.Bijective φ.hom := by
    rw [← isIso_SpecMap_iff, hφ]
    infer_instance
  let x0 := g.hom.base (show Spec (.of (MvPolynomial (Fin 2) ℂ)) from planeLinePrime k)
  have hpre : hUa.fromSpec ⁻¹' closure {planeLine k} = closure {x0} := by
    ext y
    rw [Set.mem_preimage, ← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
    have hy : y = g.hom.base (g.inv.base y) := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hfac : hUa.fromSpec.base (g.hom.base (g.inv.base y)) =
        (projectiveChartImmersion 2 2).base (g.inv.base y) := by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.isoOfRangeEq_hom_fac]
    conv_lhs => rw [hy, hfac]
    conv_rhs => rw [hy]
    exact ((projectiveChartImmersion 2 2).isOpenEmbedding.isInducing.specializes_iff
      (x := planeLinePrime k) (y := g.inv.base y)).trans
      (g.hom.isOpenEmbedding.isInducing.specializes_iff).symm
  have hI : I.ideal U = x0.asIdeal := by
    simp only [I, Scheme.IdealSheafData.vanishingIdeal_ideal]
    change PrimeSpectrum.vanishingIdeal (hUa.fromSpec ⁻¹' closure {planeLine k}) = _
    refine (congrArg PrimeSpectrum.vanishingIdeal hpre).trans ?_
    exact (PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _)
  have hx0 : (Spec.map φ).base x0 = planeLinePrime k := by
    rw [hφ]
    change (g.hom ≫ g.inv).base _ = _
    simp
    rfl
  have hJ : (I.ideal U).comap φ.hom = (planeLinePrime k).asIdeal := by
    rw [hI, ← hx0]
    rfl
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  exact smooth_quotient_of_comap_eq_planeLinePrime φ.hom hbij (I.ideal U) k hJ

/-- `[0 : 0 : 1]` lies off the singular locus of each line: hypotheses `hxreg` (`k = 0`) and
`hwreg` (`k = 1`) of `cycle-class-multiplicative`. -/
theorem planeOrigin_support_subset_smoothSupportAmbientOpen (k : Fin 2) :
    (cycleComponentAnalyticClosedSupport projectivePlane planeOrigin :
        Set (ComplexPoint projectivePlane)) ⊆
      cycleComponentSmoothSupportAmbientOpen projectivePlane (planeLine k) := by
  intro y hy
  rw [planeOrigin_support_eq_singleton, Set.mem_singleton_iff] at hy
  subst hy
  rintro ⟨z, hz, hzy⟩
  exact hz (cycleComponent_planeLine_mem_smoothLocus k z hzy)

end HodgeLadder.Tests
