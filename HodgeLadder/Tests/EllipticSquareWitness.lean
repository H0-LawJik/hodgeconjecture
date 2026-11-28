module

public import HodgeLadder.General.GeometricallyIntegralCover
public import HodgeLadder.Tests.EllipticCurveWitness
public import HodgeLadder.General.ComplexPointProd
public import HodgeLadder.Segre.General

/-!
# `E × E` satisfies the hypotheses of the statements of record

Rung `elliptic-square-witness` (plan node E7). The surface `ellipticSquare := ellipticCurve ⨯
ellipticCurve`, the categorical product in `Over (Spec ↧ℂ)` used by `complex-points-prod`, is
integral, smooth of relative dimension two and projective in upstream's sense, with upstream's
dimension `2`. It carries the Weil endomorphism `ellipticWeilEndo := prod.map ellipticI
(ellipticI ≫ ellipticI ≫ ellipticI)`, that is `[i] × [i]⁻¹`, whose square is `[−1] × [−1]` and
whose fourth power is the identity.

* Geometric integrality of `E`. The step `p1p1-witness` took from Oka's base change of ℙⁿ. Here
  both chart rings stay domains over every field `K` over `ℂ`: under `K[x, y] ≅ K[x][y]` the
  equations are `y² − (x³ − x)` and `−(u³ − w² u − w)`, monic of degree two and three with no
  root (the root checks at `0` of `elliptic-curve-integral` run over any field), and
  `(ℂ[x, y] ⧸ (g)) ⊗[ℂ] K ≃ K[x, y] ⧸ (g)` (`isDomain_quotient_tensor`). So both charts are
  geometrically integral over `ℂ` (`geometricallyIntegral_spec`), they meet at `(i, 1 − i)`,
  and `geometricallyIntegral_of_cover` gives `GeometricallyIntegral ellipticCurve.hom`.
* Integrality of `E × E`. Mathlib's instance for a geometrically integral, flat, universally
  open factor over an integral locally noetherian one (flatness and universal openness from
  smoothness), carried to `ellipticSquare.left` by `Over.prodLeftIsoPullback`.
* Smoothness: `smoothOfRelativeDimension_prod` at `1 + 1` and `smooth_prod`. Projectivity:
  `isProjective_prod` of `segre-general`. Hausdorff complex points: upstream's instance for
  projective `X`.

No sign or normalization convention enters the truth of this file: integrality holds for
`y² = x³ ± x`, and the relations of `ellipticWeilEndo` are those of `elliptic-curve-cm`
(`ellipticI_comp_self`, `ellipticI_pow_four`, `ellipticNeg_comp_self`) read factorwise, true with
`−i` in place of `i`. One choice here is load-bearing downstream: the cube on the second factor.
With `[i]^*(dx/y) = i · dx/y`, `[i] × [i]³` puts one line of `H^{1,0}(E × E)` in each eigenspace
(signature `(1, 1)`), which `weil-elliptic-square` needs; `prod.map ellipticI ellipticI` has
signature `(2, 0)`, where that rung is false (`ellipticWeilEndo_ne_prodMap_ellipticI`;
`docs/conventions.md`, row "Abelian surface E × E and the Weil endomorphism").

## Main definitions

* `HodgeLadder.Tests.ellipticSquare`, `ellipticWeilEndo`, `ellipticWeilIso`
* `HodgeLadder.Tests.affineEquationField`, `infinityEquationField`, `bivariateEquivField`,
  `bivariateEquivSwapField`

## Main results

* instance `HodgeLadder.Tests.geometricallyIntegral_ellipticCurve`;
  `ellipticAffineChart_ι_hom`, `ellipticInfinityChart_ι_hom`, `affineEquationField_complex`,
  `infinityEquationField_complex`
* instances `IsIntegral ellipticSquare.left`, `SmoothOfRelativeDimension 2 ellipticSquare.hom`,
  `Nonempty (ComplexPoint ellipticSquare)`, `IsIso ellipticWeilEndo`
* `HodgeLadder.Tests.ellipticSquare_witness`, `dim_ellipticSquare`, `smooth_ellipticSquare`,
  `isProjective_ellipticSquare`, `ellipticSquare_t2Space`, `ellipticSquare_openParacompactSpace`,
  `relativeDimension_ellipticSquare_eq`
* `HodgeLadder.Tests.ellipticWeilEndo_comp_self`, `ellipticWeilEndo_pow_four`,
  `ellipticWeilEndo_fst`, `ellipticWeilEndo_snd`, `ellipticWeilEndo_ne_id`,
  `ellipticWeilEndo_comp_self_ne_id`, `ellipticWeilEndo_ne_prodMap_ellipticI`,
  `ellipticI_cube_comp_self`
* `HodgeLadder.Tests.hodgeConjecture_ellipticSquare`, `lefschetzOneOne_ellipticSquare`,
  `hodge_eq_span_zero_ellipticSquare`, `ellipticSquare_fundamentalClass_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace HodgeLadder.Tests

section Field

open Polynomial

variable {K : Type} [Field K]

/-- `y² = x³ − x` has no solution `y ∈ K[x]`. -/
theorem sq_ne_X_pow_three_sub_X_field (r : K[X]) : r ^ 2 ≠ X ^ 3 - X := by
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

/-- `u³ = w² u + w` has no solution `u ∈ K[w]`. -/
theorem pow_three_sub_X_sq_mul_sub_X_ne_zero_field (r : K[X]) : r ^ 3 - X ^ 2 * r - X ≠ 0 := by
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

/-- `y² − (x³ − x)` is irreducible in `K[x][y]`: monic of degree two with no root. -/
theorem irreducible_affinePoly_field : Irreducible (X ^ 2 - C (X ^ 3 - X) : K[X][X]) := by
  have hm : (X ^ 2 - C (X ^ 3 - X) : K[X][X]).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hd : (X ^ 2 - C (X ^ 3 - X) : K[X][X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hm.ne_zero, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  exact sq_ne_X_pow_three_sub_X_field r hr

/-- `u³ − w² u − w` is irreducible in `K[w][u]`: monic of degree three with no root. -/
theorem irreducible_infinityPoly_field :
    Irreducible (X ^ 3 - C (X ^ 2) * X - C X : K[X][X]) := by
  have hm : (X ^ 3 - C (X ^ 2) * X - C X : K[X][X]).Monic := by monicity!
  have hd : (X ^ 3 - C (X ^ 2) * X - C X : K[X][X]).natDegree = 3 := by compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hm.ne_zero, IsRoot] at hr
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hr
  exact pow_three_sub_X_sq_mul_sub_X_ne_zero_field r hr

end Field

section Prime

open MvPolynomial

variable (K : Type) [Field K]

/-- `K[x, y] ≅ K[x][y]`, `x ↦ C X`, `y ↦ X` (Mathlib's `Polynomial.Bivariate.equivMvPolynomial`,
inverted). -/
def bivariateEquivSwapField : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (Polynomial.Bivariate.equivMvPolynomial K).symm

/-- `K[u, w] ≅ K[w][u]`, `u ↦ X`, `w ↦ C X`. -/
def bivariateEquivField : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (renameEquiv K (Equiv.swap 0 1)).trans (bivariateEquivSwapField K)

/-- The affine equation `y² − x³ + x`, over `K`. -/
def affineEquationField : MvPolynomial (Fin 2) K := X 1 ^ 2 - X 0 ^ 3 + X 0

/-- The equation `w − u³ + u w²` at infinity, over `K`. -/
def infinityEquationField : MvPolynomial (Fin 2) K := X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2

/-- `y² − x³ + x` is irreducible in `K[x, y]`. -/
theorem irreducible_affineEquationField : Irreducible (affineEquationField K) := by
  rw [← MulEquiv.irreducible_iff (bivariateEquivSwapField K).toMulEquiv]
  change Irreducible (bivariateEquivSwapField K (affineEquationField K))
  have : bivariateEquivSwapField K (affineEquationField K) =
      Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ 3 - Polynomial.X) := by
    simp only [affineEquationField, bivariateEquivSwapField, map_add, map_sub, map_pow,
      ]
    simp
    ring
  rw [this]
  exact irreducible_affinePoly_field

/-- `w − u³ + u w²` is irreducible in `K[u, w]`. -/
theorem irreducible_infinityEquationField : Irreducible (infinityEquationField K) := by
  rw [← MulEquiv.irreducible_iff (bivariateEquivField K).toMulEquiv]
  change Irreducible (bivariateEquivField K (infinityEquationField K))
  have : bivariateEquivField K (infinityEquationField K) =
      -(Polynomial.X ^ 3 - Polynomial.C (Polynomial.X ^ 2) * Polynomial.X -
        Polynomial.C Polynomial.X) := by
    simp only [infinityEquationField, bivariateEquivField, bivariateEquivSwapField, map_add,
      map_sub, map_mul, map_pow]
    simp
    ring
  rw [this]
  have := (irreducible_isUnit_mul (isUnit_one (M := Polynomial (Polynomial K))).neg).mpr
    irreducible_infinityPoly_field
  rwa [_root_.neg_one_mul] at this

/-- The affine equation over `ℂ` maps to the one over `K`. -/
theorem map_affineEquation [Algebra ℂ K] :
    map (algebraMap ℂ K) affineEquation = affineEquationField K := by
  simp [affineEquation, affineEquationField]

/-- The equation at infinity over `ℂ` maps to the one over `K`. -/
theorem map_infinityEquation [Algebra ℂ K] :
    map (algebraMap ℂ K) infinityEquation = infinityEquationField K := by
  simp [infinityEquation, infinityEquationField]

/-- The field-general affine equation at `K = ℂ` is that of `elliptic-curve-integral`. -/
theorem affineEquationField_complex : affineEquationField ℂ = affineEquation := rfl

/-- The field-general equation at infinity at `K = ℂ` is that of `elliptic-curve-integral`. -/
theorem infinityEquationField_complex : infinityEquationField ℂ = infinityEquation := rfl

/-- `(y² − x³ + x)` stays prime in `K[x, y]` for every field `K` over `ℂ`. -/
theorem isPrime_span_map_affineEquation [Algebra ℂ K] :
    (Ideal.span {map (algebraMap ℂ K) affineEquation}).IsPrime := by
  rw [map_affineEquation]
  exact (Ideal.span_singleton_prime (irreducible_affineEquationField K).ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_affineEquationField K))

/-- `(w − u³ + u w²)` stays prime in `K[u, w]` for every field `K` over `ℂ`. -/
theorem isPrime_span_map_infinityEquation [Algebra ℂ K] :
    (Ideal.span {map (algebraMap ℂ K) infinityEquation}).IsPrime := by
  rw [map_infinityEquation]
  exact (Ideal.span_singleton_prime (irreducible_infinityEquationField K).ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_infinityEquationField K))

end Prime

section Scheme

open MvPolynomial HodgeLadder.GeometricallyIntegralCover

/-- The chart ring `ℂ[x, y] ⧸ (y² − x³ + x)` is geometrically a domain. -/
theorem geometricallyIntegral_affineChartSpec :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation})))) :=
  geometricallyIntegral_spec _ _ fun K _ _ =>
    isDomain_quotient_tensor _ (isPrime_span_map_affineEquation K)

/-- The chart ring `ℂ[u, w] ⧸ (w − u³ + u w²)` is geometrically a domain. -/
theorem geometricallyIntegral_infinityChartSpec :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation})))) :=
  geometricallyIntegral_spec _ _ fun K _ _ =>
    isDomain_quotient_tensor _ (isPrime_span_map_infinityEquation K)

/-- The chart `z ≠ 0` of `E` lies over `Spec ℂ` through `algebraMap`. -/
theorem ellipticAffineChart_ι_hom :
    ellipticAffineChart.ι ≫ ellipticCurve.hom = ellipticCurveChartAffine.hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {affineEquation}))) := by
  rw [← Iso.inv_comp_eq, ellipticCurve_hom, ← Category.assoc, ← Category.assoc,
    Category.assoc ellipticCurveChartAffine.inv, ellipticCurveChartAffine_inv_ι, Category.assoc,
    AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
  rfl

/-- The chart `y ≠ 0` of `E` lies over `Spec ℂ` through `algebraMap`. -/
theorem ellipticInfinityChart_ι_hom :
    ellipticInfinityChart.ι ≫ ellipticCurve.hom = ellipticCurveChartInfinity.hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {infinityEquation}))) := by
  rw [← Iso.inv_comp_eq, ellipticCurve_hom, ← Category.assoc, ← Category.assoc,
    Category.assoc ellipticCurveChartInfinity.inv, ellipticCurveChartInfinity_inv_ι,
    Category.assoc, AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp]
  rfl

/-- The chart `z ≠ 0` of `E` is geometrically integral over `ℂ`. -/
instance geometricallyIntegral_ellipticAffineChart :
    GeometricallyIntegral (ellipticAffineChart.ι ≫ ellipticCurve.hom) := by
  rw [ellipticAffineChart_ι_hom]
  have := geometricallyIntegral_affineChartSpec
  exact geometricallyIntegral_iso_comp _ _

/-- The chart `y ≠ 0` of `E` is geometrically integral over `ℂ`. -/
instance geometricallyIntegral_ellipticInfinityChart :
    GeometricallyIntegral (ellipticInfinityChart.ι ≫ ellipticCurve.hom) := by
  rw [ellipticInfinityChart_ι_hom]
  have := geometricallyIntegral_infinityChartSpec
  exact geometricallyIntegral_iso_comp _ _

/-- The overlap of the two charts maps onto the point `Spec ℂ`: it holds `(i, 1 − i)`. -/
instance surjective_ellipticChartInter :
    Surjective ((ellipticAffineChart ⊓ ellipticInfinityChart).ι ≫ ellipticCurve.hom) := by
  let pt := Classical.arbitrary (Spec ↧ℂ)
  have hmem : ellipticCurveChartMeet.left pt ∈ ellipticAffineChart ⊓ ellipticInfinityChart :=
    ⟨ellipticCurveChartMeet_mem_affineChart pt, ellipticCurveChartMeet_mem_infinityChart pt⟩
  exact ⟨fun _ => ⟨⟨_, hmem⟩, Subsingleton.elim _ _⟩⟩

/-- **`E` is geometrically integral over `ℂ`**: both charts are, and they meet. -/
instance geometricallyIntegral_ellipticCurve : GeometricallyIntegral ellipticCurve.hom :=
  have := surjective_ellipticChartInter
  geometricallyIntegral_of_cover _ ellipticAffineChart ellipticInfinityChart
    ellipticCurve_chart_cover

end Scheme

/-! ### The surface -/

open HodgeLadder.ComplexPointProd

/-- `E` is locally noetherian (locally of finite type over `Spec ℂ`). -/
instance isLocallyNoetherian_ellipticCurve : IsLocallyNoetherian ellipticCurve.left :=
  LocallyOfFiniteType.isLocallyNoetherian ellipticCurve.hom

/-- The abelian surface `E × E`: the categorical product of `ellipticCurve` with itself in
`Over (Spec ℂ)`, the spelling of `complex-points-prod`. -/
abbrev ellipticSquare : Over (Spec ↧ℂ) := ellipticCurve ⨯ ellipticCurve

/-- The fibre product `E ×_ℂ E` is integral (Mathlib's instance for a geometrically integral,
flat, universally open factor over an integral locally noetherian one). -/
instance isIntegral_pullback_ellipticSquare :
    IsIntegral (pullback ellipticCurve.hom ellipticCurve.hom) := inferInstance

/-- `E × E` is nonempty. -/
instance nonempty_ellipticSquare : Nonempty ellipticSquare.left :=
  ⟨(Over.prodLeftIsoPullback ellipticCurve ellipticCurve).inv
    (Classical.arbitrary ↥(pullback ellipticCurve.hom ellipticCurve.hom))⟩

/-- `E × E` is integral. -/
instance isIntegral_ellipticSquare : IsIntegral ellipticSquare.left :=
  isIntegral_of_isOpenImmersion (Over.prodLeftIsoPullback ellipticCurve ellipticCurve).hom

/-- `E × E` is smooth of relative dimension two (`smoothOfRelativeDimension_prod` at `1 + 1`). -/
instance smoothOfRelativeDimension_ellipticSquare :
    SmoothOfRelativeDimension 2 ellipticSquare.hom :=
  inferInstanceAs (SmoothOfRelativeDimension (1 + 1) _)

/-- `E × E` is smooth (`smooth_prod`). -/
theorem smooth_ellipticSquare : Smooth ellipticSquare.hom := inferInstance

/-- `E × E` is projective (`isProjective_prod` of `segre-general`). -/
theorem isProjective_ellipticSquare : IsProjective ellipticSquare.hom := inferInstance

/-- The complex points of `E × E` are Hausdorff (upstream's instance for projective `X`). -/
theorem ellipticSquare_t2Space : T2Space (ComplexPoint ellipticSquare) := inferInstance

/-- `E × E` has a complex point: the pair of origins, through `pointProdHomeomorph`. -/
instance nonempty_complexPoint_ellipticSquare : Nonempty (ComplexPoint ellipticSquare) :=
  ⟨(pointProdHomeomorph ellipticCurve ellipticCurve).symm
    (ellipticCurveOrigin, ellipticCurveOrigin)⟩

/-- Every open subset of the complex points of `E × E` is paracompact (upstream's
`ComplexPoint.openParacompactSpace`). -/
theorem ellipticSquare_openParacompactSpace :
    ∀ U : TopologicalSpace.Opens (ComplexPoint ellipticSquare), ParacompactSpace U :=
  ComplexPoint.openParacompactSpace ellipticSquare

/-- Upstream's dimension of `E × E` is `2` (upstream's `SmoothOfRelativeDimension.dim_eq`). -/
theorem dim_ellipticSquare : TopologicalSpace.dim ellipticSquare.left = 2 :=
  SmoothOfRelativeDimension.dim_eq (f := ellipticSquare.hom) 2

/-- The relative dimension of `E × E` over `ℂ` is unique. -/
theorem relativeDimension_ellipticSquare_eq (d : ℕ)
    [SmoothOfRelativeDimension d ellipticSquare.hom] : d = 2 :=
  (SmoothOfRelativeDimension.dim_eq (f := ellipticSquare.hom) d).symm.trans dim_ellipticSquare

/-! ### The Weil endomorphism -/

/-- `[i]³ = [i]⁻¹`, so `[i]³ ≫ [i]³ = [−1]`. -/
theorem ellipticI_cube_comp_self :
    (ellipticI ≫ ellipticI ≫ ellipticI) ≫ (ellipticI ≫ ellipticI ≫ ellipticI) = ellipticNeg := by
  have h : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI =
      (ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI) ≫ ellipticI ≫ ellipticI := by
    simp only [Category.assoc]
  simp only [Category.assoc]
  rw [h, ellipticI_pow_four, Category.id_comp, ellipticI_comp_self]

/-- **The Weil endomorphism** `[i] × [i]⁻¹ = [i] × [i]³` of `E × E`. Through Künneth,
`H¹(E × E) = pr₁^*H¹(E) ⊕ pr₂^*H¹(E)` (planned in `elliptic-square-cohomology`), it acts as
`[i]^*` on the first summand and `([i]^*)³ = ([i]^*)⁻¹` on the second; on `H^{1,0}` that is `i`
and `−i` (read from the literature, node D6), the signature `(1, 1)` that `weil-elliptic-square`
needs. Not checkable at the pin. -/
def ellipticWeilEndo : ellipticSquare ⟶ ellipticSquare :=
  prod.map ellipticI (ellipticI ≫ ellipticI ≫ ellipticI)

/-- The Weil endomorphism on the first factor is `[i]`. -/
@[reassoc]
theorem ellipticWeilEndo_fst : ellipticWeilEndo ≫ prod.fst = prod.fst ≫ ellipticI :=
  prod.map_fst _ _

/-- The Weil endomorphism on the second factor is `[i]³`. -/
@[reassoc]
theorem ellipticWeilEndo_snd :
    ellipticWeilEndo ≫ prod.snd = prod.snd ≫ ellipticI ≫ ellipticI ≫ ellipticI :=
  prod.map_snd _ _

/-- **The square of the Weil endomorphism is `[−1] × [−1]`.** -/
theorem ellipticWeilEndo_comp_self :
    ellipticWeilEndo ≫ ellipticWeilEndo = prod.map ellipticNeg ellipticNeg := by
  rw [ellipticWeilEndo, prod.map_map, ellipticI_cube_comp_self, ellipticI_comp_self]

/-- **The fourth power of the Weil endomorphism is the identity.** -/
theorem ellipticWeilEndo_pow_four :
    ellipticWeilEndo ≫ ellipticWeilEndo ≫ ellipticWeilEndo ≫ ellipticWeilEndo =
      𝟙 ellipticSquare := by
  rw [← Category.assoc, ellipticWeilEndo_comp_self, prod.map_map,
    ellipticNeg_comp_self, prod.map_id_id]

/-- The Weil endomorphism is an automorphism, with inverse its cube. -/
def ellipticWeilIso : ellipticSquare ≅ ellipticSquare where
  hom := ellipticWeilEndo
  inv := ellipticWeilEndo ≫ ellipticWeilEndo ≫ ellipticWeilEndo
  hom_inv_id := ellipticWeilEndo_pow_four
  inv_hom_id := by simp only [Category.assoc]; exact ellipticWeilEndo_pow_four

/-- The Weil endomorphism is an isomorphism. -/
instance isIso_ellipticWeilEndo : IsIso ellipticWeilEndo := ellipticWeilIso.isIso_hom

/-- **The Weil endomorphism is not the identity**: on the first factor it is `[i] ≠ 𝟙`. -/
theorem ellipticWeilEndo_ne_id : ellipticWeilEndo ≠ 𝟙 ellipticSquare := by
  intro h
  have h1 := ellipticWeilEndo_fst
  rw [h, Category.id_comp] at h1
  have h2 := congrArg (prod.lift (𝟙 ellipticCurve) (𝟙 ellipticCurve) ≫ ·) h1
  simp only [prod.lift_fst_assoc, Category.id_comp, prod.lift_fst] at h2
  exact ellipticI_ne_id h2.symm

/-- The square of the Weil endomorphism is not the identity: on the first factor it is
`[−1] ≠ 𝟙`. -/
theorem ellipticWeilEndo_comp_self_ne_id :
    ellipticWeilEndo ≫ ellipticWeilEndo ≠ 𝟙 ellipticSquare := by
  intro h
  rw [ellipticWeilEndo_comp_self] at h
  have h1 := prod.map_fst ellipticNeg ellipticNeg
  rw [h, Category.id_comp] at h1
  have h2 := congrArg (prod.lift (𝟙 ellipticCurve) (𝟙 ellipticCurve) ≫ ·) h1
  simp only [prod.lift_fst_assoc, Category.id_comp, prod.lift_fst] at h2
  exact ellipticNeg_ne_id h2.symm

/-- **The Weil endomorphism is not `[i] × [i]`**: on the second factor `[i]³ ≠ [i]`, since
otherwise `[−1] = [i]⁴ = 𝟙`. `prod.map ellipticI ellipticI` has signature `(2, 0)` and fails the
balance condition of `IsWeilTypeSurface`. -/
theorem ellipticWeilEndo_ne_prodMap_ellipticI :
    ellipticWeilEndo ≠ prod.map ellipticI ellipticI := by
  intro h
  have h1 := congrArg (· ≫ prod.snd) h
  simp only [ellipticWeilEndo, prod.map_snd] at h1
  have h2 := congrArg (prod.lift (𝟙 ellipticCurve) (𝟙 ellipticCurve) ≫ ·) h1
  simp only [prod.lift_snd_assoc, Category.id_comp] at h2
  have h3 : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI = ellipticI ≫ ellipticI := by
    rw [h2]
  rw [ellipticI_pow_four, ellipticI_comp_self] at h3
  exact ellipticNeg_ne_id h3.symm

/-! ### The witness -/

open AlgebraicGeometry.ComplexPoint

/-- **Rung `elliptic-square-witness`.** `E × E` satisfies the scheme hypotheses of the statements
of record: integral, smooth of relative dimension two (hence smooth), and projective; its
dimension is `2`, and the Weil endomorphism squares to `[−1] × [−1]` and has order four. -/
theorem ellipticSquare_witness :
    IsIntegral ellipticSquare.left ∧ SmoothOfRelativeDimension 2 ellipticSquare.hom ∧
      Smooth ellipticSquare.hom ∧ IsProjective ellipticSquare.hom ∧
      TopologicalSpace.dim ellipticSquare.left = 2 ∧
      ellipticWeilEndo ≫ ellipticWeilEndo = prod.map ellipticNeg ellipticNeg ∧
      ellipticWeilEndo ≫ ellipticWeilEndo ≫ ellipticWeilEndo ≫ ellipticWeilEndo =
        𝟙 ellipticSquare :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, dim_ellipticSquare,
    ellipticWeilEndo_comp_self, ellipticWeilEndo_pow_four⟩

/-- Upstream's `HodgeConjecture` specializes to `E × E`: its instance arguments elaborate at
`ellipticSquare`. -/
theorem hodgeConjecture_ellipticSquare (h : HodgeConjecture) (p : ℕ) :
    Hdg^p(ellipticSquare; ℚ) ≤ algebraicCycleClassSpan ellipticSquare p :=
  h ellipticSquare p

/-- The checked Lefschetz (1,1) theorem (`lefschetz-1-1`) at `E × E`. -/
theorem lefschetzOneOne_ellipticSquare :
    Hdg^1(ellipticSquare; ℚ) ≤ algebraicCycleClassSpan ellipticSquare 1 :=
  HodgeLadder.lefschetzOneOne_holds ellipticSquare

/-- The codimension-zero equality (`nonvacuity-tests`) at `E × E`. -/
theorem hodge_eq_span_zero_ellipticSquare :
    Hdg^0(ellipticSquare; ℚ) = algebraicCycleClassSpan ellipticSquare 0 :=
  hodge_eq_span_zero ellipticSquare

/-- The class of `E × E` itself, at the generic point, is nonzero (upstream's
`cycleComponentSheafClass_genericPoint_ne_zero`). -/
theorem ellipticSquare_fundamentalClass_ne_zero :
    cycleComponentSheafClass ellipticSquare (genericPoint ellipticSquare.left)
      (coheight_genericPoint_eq_zero ellipticSquare) ≠ 0 :=
  cycleComponentSheafClass_genericPoint_ne_zero ellipticSquare

end HodgeLadder.Tests
