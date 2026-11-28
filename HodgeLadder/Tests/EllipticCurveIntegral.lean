module

public import HodgeLadder.Tests.EllipticCurve
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# The plane cubic `y²z = x³ − xz²` is integral

Rung `elliptic-curve-integral`. The curve `ellipticCurve` of `plane-cubic-subscheme` is integral:
it is reduced and irreducible (`isIntegral_of_irreducibleSpace_of_isReduced`).

* Algebra. Both chart rings are domains. Under `ℂ[x, y] ≅ ℂ[x][y]` (Mathlib's
  `Polynomial.Bivariate.equivMvPolynomial`) the affine equation `y² − x³ + x` is `y² − (x³ − x)`,
  monic of degree two in `y`; under `ℂ[u, w] ≅ ℂ[w][u]` the equation `w − u³ + u w²` at
  infinity is `−(u³ − w² u − w)`, monic of degree three in `u` up to the unit `−1`. A monic
  polynomial of degree two or three over a domain with no root is irreducible
  (`Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`). The root checks run at
  `0`: `r² = x³ − x` forces `x ∣ r` and then `x s² = x² − 1`, false at `x = 0`;
  `r³ = w² r + w` forces `w ∣ r` and then `w² s³ = w² s + 1`, false at `w = 0`. In the UFD
  `ℂ[X₀, X₁]` irreducible elements are prime, so both quotients are domains.
* Reduced. The two charts `z ≠ 0` and `y ≠ 0` cover `E` (`ellipticCurve_chart_cover`) and are
  spectra of domains, so `IsReduced.of_openCover` applies.
* Irreducible. Both charts are irreducible subsets, and the point `(x, y) = (i, 1 − i)`
  (`(1 − i)² = −2i = i³ − i`) lies in both, so `irreducibleSpace_of_cover` of `p2-witness`
  applies with the chart `z ≠ 0` as the dense open.

No sign convention enters the truth of this file: integrality holds for y² = x³ ± x, and the
root checks at `0` are the same for either sign. The sign enters one proof step: the meeting point
`(i, 1 − i)` lies on y² = x³ − x and off y² = x³ + x, so `eval_chartMeet` fails to build if the
linear term of `cubicForm` changes sign. The curve is recorded in `docs/conventions.md`, row
"Plane cubic E and its charts".

## Main definitions

* `HodgeLadder.Tests.bivariateEquiv`, `bivariateEquivSwap`
* `HodgeLadder.Tests.ellipticAffineChart`, `ellipticInfinityChart`, `ellipticCurveChartMeet`

## Main results

* `HodgeLadder.Tests.irreducible_affineEquation`, `irreducible_infinityEquation`
* instances `IsDomain (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation})`,
  `IsDomain (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation})`
* instances `IsReduced ellipticCurveScheme`, `IrreducibleSpace ellipticCurveScheme`,
  `IsIntegral ellipticCurveScheme`, `IsIntegral ellipticCurve.left`
* `HodgeLadder.Tests.dense_ellipticAffineChart`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLadder.Tests

section Bivariate

open MvPolynomial

/-- The ring isomorphism `ℂ[x, y] ≅ ℂ[x][y]`, `x = X 0 ↦ C X`, `y = X 1 ↦ Polynomial.X`: Mathlib's
`Polynomial.Bivariate.equivMvPolynomial`, inverted. -/
def bivariateEquivSwap : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Polynomial (Polynomial ℂ) :=
  (Polynomial.Bivariate.equivMvPolynomial ℂ).symm

/-- `bivariateEquivSwap` sends `x = X 0` to the inner variable. -/
theorem bivariateEquivSwap_X_zero : bivariateEquivSwap (X 0) = Polynomial.C Polynomial.X := by
  simp [bivariateEquivSwap]

/-- `bivariateEquivSwap` sends `y = X 1` to the outer variable. -/
theorem bivariateEquivSwap_X_one : bivariateEquivSwap (X 1) = Polynomial.X := by
  simp [bivariateEquivSwap]

/-- The ring isomorphism `ℂ[u, w] ≅ ℂ[w][u]`, `u = X 0 ↦ Polynomial.X`, `w = X 1 ↦ C X`: swap
the variables, then `bivariateEquivSwap`. -/
def bivariateEquiv : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Polynomial (Polynomial ℂ) :=
  (renameEquiv ℂ (Equiv.swap 0 1)).trans bivariateEquivSwap

/-- `bivariateEquiv` sends `u = X 0` to the outer variable. -/
theorem bivariateEquiv_X_zero : bivariateEquiv (X 0) = Polynomial.X := by
  simp [bivariateEquiv, bivariateEquivSwap]

/-- `bivariateEquiv` sends `w = X 1` to the inner variable. -/
theorem bivariateEquiv_X_one : bivariateEquiv (X 1) = Polynomial.C Polynomial.X := by
  simp [bivariateEquiv, bivariateEquivSwap]

end Bivariate

section Roots

open Polynomial

/-- `y² = x³ − x` has no solution `y ∈ ℂ[x]`: at `x = 0`, `y = x s`, and then `x s² = x² − 1`
fails at `x = 0`. -/
theorem sq_ne_X_pow_three_sub_X (r : ℂ[X]) : r ^ 2 ≠ X ^ 3 - X := by
  intro h
  have h0 : r.eval 0 = 0 := by
    have := congrArg (eval 0) h
    simpa using this
  obtain ⟨s, rfl⟩ : X ∣ r := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, h0]
  have h1 : X * (X * s ^ 2 - X ^ 2 + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact X_ne_zero h2
  · have := congrArg (eval 0) h2
    simp at this

/-- `u³ = w² u + w` has no solution `u ∈ ℂ[w]`: at `w = 0`, `u = w s`, and then
`w² s³ = w² s + 1` fails at `w = 0`. -/
theorem pow_three_sub_X_sq_mul_sub_X_ne_zero (r : ℂ[X]) : r ^ 3 - X ^ 2 * r - X ≠ 0 := by
  intro h
  have h0 : r.eval 0 = 0 := by
    have := congrArg (eval 0) h
    simpa using this
  obtain ⟨s, rfl⟩ : X ∣ r := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, h0]
  have h1 : X * (X ^ 2 * s ^ 3 - X ^ 2 * s - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact X_ne_zero h2
  · have := congrArg (eval 0) h2
    simp at this

/-- `y² − (x³ − x)` is irreducible in `ℂ[x][y]`: it is monic of degree two with no root. -/
theorem irreducible_affinePoly : Irreducible (X ^ 2 - C (X ^ 3 - X) : ℂ[X][X]) := by
  have hm : (X ^ 2 - C (X ^ 3 - X) : ℂ[X][X]).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hd : (X ^ 2 - C (X ^ 3 - X) : ℂ[X][X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hm.ne_zero, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  exact sq_ne_X_pow_three_sub_X r hr

/-- `u³ − w² u − w` is irreducible in `ℂ[w][u]`: it is monic of degree three with no root. -/
theorem irreducible_infinityPoly :
    Irreducible (X ^ 3 - C (X ^ 2) * X - C X : ℂ[X][X]) := by
  have hm : (X ^ 3 - C (X ^ 2) * X - C X : ℂ[X][X]).Monic := by monicity!
  have hd : (X ^ 3 - C (X ^ 2) * X - C X : ℂ[X][X]).natDegree = 3 := by compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hm.ne_zero, IsRoot] at hr
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hr
  exact pow_three_sub_X_sq_mul_sub_X_ne_zero r hr

end Roots

section Domain

open MvPolynomial

/-- The affine equation `y² − x³ + x` in `ℂ[x][y]` is `y² − (x³ − x)`. -/
theorem bivariateEquivSwap_affineEquation :
    bivariateEquivSwap affineEquation =
      Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3 - Polynomial.X) := by
  rw [affineEquation, map_add, map_sub, map_pow, map_pow, bivariateEquivSwap_X_zero,
    bivariateEquivSwap_X_one, Polynomial.C_sub, Polynomial.C_pow]
  ring

/-- The equation `w − u³ + u w²` in `ℂ[w][u]` is `−(u³ − w² u − w)`. -/
theorem bivariateEquiv_infinityEquation :
    bivariateEquiv infinityEquation =
      -(Polynomial.X ^ 3 - Polynomial.C (Polynomial.X ^ 2) * Polynomial.X -
        Polynomial.C Polynomial.X) := by
  rw [infinityEquation, map_add, map_sub, map_mul, map_pow, map_pow, bivariateEquiv_X_zero,
    bivariateEquiv_X_one, Polynomial.C_pow]
  ring

/-- `y² − x³ + x` is irreducible in `ℂ[x, y]`. -/
theorem irreducible_affineEquation : Irreducible affineEquation := by
  rw [← MulEquiv.irreducible_iff bivariateEquivSwap.toMulEquiv]
  change Irreducible (bivariateEquivSwap affineEquation)
  rw [bivariateEquivSwap_affineEquation]
  exact irreducible_affinePoly

/-- `w − u³ + u w²` is irreducible in `ℂ[u, w]`. -/
theorem irreducible_infinityEquation : Irreducible infinityEquation := by
  rw [← MulEquiv.irreducible_iff bivariateEquiv.toMulEquiv]
  change Irreducible (bivariateEquiv infinityEquation)
  rw [bivariateEquiv_infinityEquation]
  have h : Irreducible (-(Polynomial.X ^ 3 - Polynomial.C (Polynomial.X ^ 2) * Polynomial.X -
      Polynomial.C Polynomial.X : Polynomial (Polynomial ℂ))) := by
    have := (irreducible_isUnit_mul (isUnit_one (M := Polynomial (Polynomial ℂ))).neg).mpr
      irreducible_infinityPoly
    rwa [_root_.neg_one_mul] at this
  exact h

/-- `(y² − x³ + x)` is a prime ideal of the UFD `ℂ[x, y]`. -/
theorem isPrime_span_affineEquation : (Ideal.span {affineEquation}).IsPrime :=
  (Ideal.span_singleton_prime irreducible_affineEquation.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_affineEquation)

/-- `(w − u³ + u w²)` is a prime ideal of the UFD `ℂ[u, w]`. -/
theorem isPrime_span_infinityEquation : (Ideal.span {infinityEquation}).IsPrime :=
  (Ideal.span_singleton_prime irreducible_infinityEquation.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_infinityEquation)

/-- **The ring `ℂ[x, y] ⧸ (y² − x³ + x)` of the chart `z ≠ 0` is a domain.** -/
instance isDomain_affineChartRing :
    IsDomain (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation}) :=
  have := isPrime_span_affineEquation
  Ideal.Quotient.isDomain _

/-- The ring `ℂ[u, w] ⧸ (w − u³ + u w²)` of the chart `y ≠ 0` is a domain. -/
instance isDomain_infinityChartRing :
    IsDomain (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation}) :=
  have := isPrime_span_infinityEquation
  Ideal.Quotient.isDomain _

end Domain

section Scheme

open MvPolynomial

/-- The chart `z ≠ 0` of `E`. -/
abbrev ellipticAffineChart : ellipticCurveScheme.Opens :=
  ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 2

/-- The chart `y ≠ 0` of `E`. -/
abbrev ellipticInfinityChart : ellipticCurveScheme.Opens :=
  ellipticCurveι ⁻¹ᵁ AlgebraicGeometry.ProjectiveSpace.U 2 ℂ 1

/-- The chart `z ≠ 0` is nonempty: it is the spectrum of a domain. -/
instance nonempty_ellipticAffineChart : Nonempty ellipticAffineChart.toScheme :=
  ⟨ellipticCurveChartAffine.inv (Classical.arbitrary _)⟩

/-- The chart `y ≠ 0` is nonempty: it is the spectrum of a domain. -/
instance nonempty_ellipticInfinityChart : Nonempty ellipticInfinityChart.toScheme :=
  ⟨ellipticCurveChartInfinity.inv (Classical.arbitrary _)⟩

/-- The chart `z ≠ 0` is integral, through `ellipticCurveChartAffine`. -/
instance isIntegral_ellipticAffineChart : IsIntegral ellipticAffineChart.toScheme :=
  isIntegral_of_isOpenImmersion ellipticCurveChartAffine.hom

/-- The chart `y ≠ 0` is integral, through `ellipticCurveChartInfinity`. -/
instance isIntegral_ellipticInfinityChart : IsIntegral ellipticInfinityChart.toScheme :=
  isIntegral_of_isOpenImmersion ellipticCurveChartInfinity.hom

/-- **`E` is reduced**: its two charts are reduced and cover it. -/
instance isReduced_ellipticCurveScheme : IsReduced ellipticCurveScheme := by
  have hU : TopologicalSpace.IsOpenCover
      (fun b : Bool => if b then ellipticAffineChart else ellipticInfinityChart) := by
    rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]
    exact ellipticCurve_chart_cover
  let 𝒰 := ellipticCurveScheme.openCoverOfIsOpenCover _ hU
  have : ∀ i, IsReduced (𝒰.X i) := by
    intro i; cases i
    · exact inferInstanceAs (IsReduced ellipticInfinityChart.toScheme)
    · exact inferInstanceAs (IsReduced ellipticAffineChart.toScheme)
  exact IsReduced.of_openCover (𝒰 := 𝒰)

/-- `(x, y) = (i, 1 − i)` solves `y² = x³ − x`: `(1 − i)² = −2i = i³ − i`. -/
theorem eval_chartMeet :
    eval ![Complex.I, 1 - Complex.I] (dehomogenize ℂ (2 : Fin 3) cubicForm) = 0 := by
  rw [dehomogenize_two_cubicForm]
  simp
  ring_nf
  simp [Complex.I_sq]

/-- The point `(x, y) = (i, 1 − i)` of the chart `z ≠ 0`, `[i : 1 − i : 1]`; it has `y ≠ 0`, so it
lies in both charts. The same point is `ellipticCurvePointI` of `elliptic-curve-cm`, kept here
under its own name so this file does not depend on that rung. -/
def ellipticCurveChartMeet : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![Complex.I, 1 - Complex.I] eval_chartMeet

/-- The point `(i, 1 − i)` lies in the chart `z ≠ 0`. -/
theorem ellipticCurveChartMeet_mem_affineChart (p : Spec ↧ℂ) :
    ellipticCurveChartMeet.left p ∈ ellipticAffineChart := by
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ellipticCurveChartMeet,
    chartComplexPoint_ι,
    Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
    AlgebraicGeometry.ProjectiveSpace.chart_preimage_U, dehomogenize_two_X_two]
  have : p.asIdeal.IsPrime := p.isPrime
  intro h
  have h' : eval ![Complex.I, 1 - Complex.I] (1 : MvPolynomial (Fin 2) ℂ) ∈ p.asIdeal := h
  rw [Ideal.eq_bot_of_prime p.asIdeal, map_one] at h'
  exact one_ne_zero h'

/-- The point `(i, 1 − i)` lies in the chart `y ≠ 0`. -/
theorem ellipticCurveChartMeet_mem_infinityChart (p : Spec ↧ℂ) :
    ellipticCurveChartMeet.left p ∈ ellipticInfinityChart := by
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ellipticCurveChartMeet,
    chartComplexPoint_ι,
    Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
    AlgebraicGeometry.ProjectiveSpace.chart_preimage_U, dehomogenize_two_X_one]
  have : p.asIdeal.IsPrime := p.isPrime
  intro h
  have h' : eval ![Complex.I, 1 - Complex.I] (X 1 : MvPolynomial (Fin 2) ℂ) ∈ p.asIdeal := h
  rw [Ideal.eq_bot_of_prime p.asIdeal, eval_X] at h'
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Ideal.mem_bot, sub_eq_zero] at h'
  have := congrArg Complex.re h'
  simp at this

/-- **`E` is irreducible**: the two irreducible charts cover `E`, and each meets the chart
`z ≠ 0` (at `(i, 1 − i)`). -/
instance irreducibleSpace_ellipticCurveScheme : IrreducibleSpace ellipticCurveScheme := by
  have : Nonempty (Spec ↧ℂ) := inferInstance
  set pt := Classical.arbitrary (Spec ↧ℂ)
  refine irreducibleSpace_of_cover (U := (ellipticAffineChart : Set ellipticCurveScheme))
    (V := fun b : Bool =>
      ((if b then ellipticAffineChart else ellipticInfinityChart : ellipticCurveScheme.Opens) :
        Set ellipticCurveScheme)) ellipticAffineChart.isOpen
    (isIrreducible_iff_irreducibleSpace.mpr
      (inferInstanceAs (IrreducibleSpace ellipticAffineChart.toScheme))) ?_ ?_ ?_
  · intro b; cases b
    · exact isIrreducible_iff_irreducibleSpace.mpr
        (inferInstanceAs (IrreducibleSpace ellipticInfinityChart.toScheme))
    · exact isIrreducible_iff_irreducibleSpace.mpr
        (inferInstanceAs (IrreducibleSpace ellipticAffineChart.toScheme))
  · have h := ellipticCurve_chart_cover
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hx : x ∈ (⊤ : ellipticCurveScheme.Opens) := trivial
    rw [← h, TopologicalSpace.Opens.mem_sup] at hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  · intro b
    refine ⟨ellipticCurveChartMeet.left pt, ellipticCurveChartMeet_mem_affineChart pt, ?_⟩
    cases b
    · exact ellipticCurveChartMeet_mem_infinityChart pt
    · exact ellipticCurveChartMeet_mem_affineChart pt

/-- The chart `z ≠ 0` is dense in `E`. -/
theorem dense_ellipticAffineChart : Dense (ellipticAffineChart : Set ellipticCurveScheme) :=
  ellipticAffineChart.isOpen.dense
    ⟨_, ellipticCurveChartMeet_mem_affineChart (Classical.arbitrary (Spec ↧ℂ))⟩

/-- **Rung `elliptic-curve-integral`.** The plane cubic `E : y²z = x³ − xz²` is integral. -/
instance isIntegral_ellipticCurveScheme : IsIntegral ellipticCurveScheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Rung `elliptic-curve-integral`**, on the object of `Over (Spec ↧ℂ)`. -/
instance isIntegral_ellipticCurve : IsIntegral ellipticCurve.left :=
  isIntegral_ellipticCurveScheme

end Scheme

end HodgeLadder.Tests
