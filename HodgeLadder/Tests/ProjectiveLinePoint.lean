module

public import HodgeLadder.Tests.ProjectiveLine
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
public import Other.AlgebraicGeometry.Smooth.DimensionFormula
public import Mathlib.Analysis.Convex.Contractible

/-!
# A point of ℙ¹ with contractible complement

Rung `projective-line-point`. The point `[1 : 0]` of upstream's ℙ¹ has coheight one, and the
complement of its analytic support is homeomorphic to `ℂ`, hence contractible. On Oka's model
`ℙₒ(1; ℂ)` the complement of the chart `X₁ ≠ 0` is the single point `[1 : 0]`: in the chart
`X₀ ≠ 0` it is the only prime of `ℂ[Y]` containing `Y`. The chart `X₁ ≠ 0` of upstream's ℙ¹ is
affine space over `Spec ℂ`, whose complex points are `ℂ` (upstream `affineSpaceHomeomorph`).

## Main definitions

* `HodgeLadder.Tests.infty`, `HodgeLadder.Tests.openOne`, `HodgeLadder.Tests.complInftyHomeomorph`

## Main results

* `HodgeLadder.Tests.coheight_infty`, `HodgeLadder.Tests.not_mem_openOne_iff`
* `HodgeLadder.Tests.exists_point_contractible_compl`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial Set ComplexPoint

namespace HodgeLadder.Tests

/-- Every polynomial in one variable differs from its constant term by a multiple of `X 0`. -/
lemma sub_C_eval_mem_span (f : MvPolynomial (Fin 1) ℂ) :
    f - C (eval 0 f) ∈ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have : p + q - C (eval 0 (p + q)) = (p - C (eval 0 p)) + (q - C (eval 0 q)) := by
      simp only [map_add]; ring
    rw [this]
    exact add_mem hp hq
  | mul_X p i hp =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [map_mul, eval_X, Pi.zero_apply, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The only prime of `ℂ[Y]` containing `Y` is the kernel of evaluation at `0`. -/
lemma asIdeal_eq_of_X_mem (r : PrimeSpectrum (MvPolynomial (Fin 1) ℂ))
    (hr : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ r.asIdeal) :
    r.asIdeal = RingHom.ker (eval₂Hom (RingHom.id ℂ) 0) := by
  ext f
  have hspan : Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} ≤ r.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr hr
  have hev : eval₂Hom (RingHom.id ℂ) 0 f = eval 0 f := rfl
  rw [RingHom.mem_ker, hev]
  constructor
  · intro hf
    by_contra hne
    have hC : C (eval 0 f) ∈ r.asIdeal := by
      have := sub_mem hf (hspan (sub_C_eval_mem_span f))
      simpa using this
    exact r.isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ hC) ((isUnit_iff_ne_zero.mpr hne).map C))
  · intro hf
    have := hspan (sub_C_eval_mem_span f)
    rwa [hf, map_zero, sub_zero] at this

/-- The point `[1 : 0]` of Oka's ℙ¹. -/
noncomputable def okaInfty : ℙₒ(1; ℂ) :=
  (AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin 2)).base
    (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ)
      (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 0 ![1, 0]))

lemma dehomogenizeVec_infty :
    AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec (0 : Fin 2) (![1, 0] : Fin 2 → ℂ) = 0 := by
  funext j
  fin_cases j
  simp [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec]

/-- **The complement of the chart `X₁ ≠ 0` is the single point `[1 : 0]`.** -/
lemma not_mem_U_one_iff (q : ℙₒ(1; ℂ)) :
    q ∉ AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 1 ↔ q = okaInfty := by
  constructor
  · intro hq
    have hcov : q ∈ (⨆ i, AlgebraicGeometry.ProjectiveSpace.U 1 ℂ i) :=
      (AlgebraicGeometry.ProjectiveSpace.iSup_U 1 ℂ) ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
    have hi0 : i = 0 := by
      fin_cases i
      · rfl
      · exact (hq hi).elim
    subst hi0
    rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart] at hi
    obtain ⟨r, rfl⟩ := hi
    have hr : r ∉ (AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin 2)) ⁻¹ᵁ
        AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 1 := hq
    rw [AlgebraicGeometry.ProjectiveSpace.chart_preimage_U] at hr
    have h1 : (1 : Fin 2) = (0 : Fin 2).succAbove 0 := rfl
    rw [h1, dehomogenize_X_succAbove] at hr
    have hX : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ (show PrimeSpectrum _ from r).asIdeal := by
      by_contra h
      exact hr h
    unfold okaInfty
    congr 1
    rw [dehomogenizeVec_infty]
    apply PrimeSpectrum.ext
    exact asIdeal_eq_of_X_mem r hX
  · rintro rfl
    exact fun h => (AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff
      (RingHom.id ℂ) 0 1 ![1, 0] one_ne_zero).mp h rfl

/-- The chart `X₁ ≠ 0` of upstream's ℙ¹. -/
noncomputable def chartOne : Spec (.of (MvPolynomial (Fin 1) ℂ)) ⟶ projectiveLine.left :=
  AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (1 : Fin 2) ≫ okaIso.hom

instance : IsOpenImmersion chartOne := by
  unfold chartOne; infer_instance

/-- The open `X₁ ≠ 0` of upstream's ℙ¹. -/
noncomputable def openOne : projectiveLine.left.Opens := chartOne.opensRange

/-- The point `[1 : 0]` of upstream's ℙ¹. -/
noncomputable def infty : projectiveLine.left := okaIso.hom.base okaInfty

lemma okaIso_hom_inv_base (y : projectiveLine.left) : okaIso.hom.base (okaIso.inv.base y) = y := by
  simp

lemma mem_openOne_iff (y : projectiveLine.left) :
    y ∈ openOne ↔ okaIso.inv.base y ∈ AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 1 := by
  rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart]
  change y ∈ Set.range chartOne.base ↔ okaIso.inv.base y ∈ Set.range _
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp [chartOne]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [chartOne, Scheme.Hom.comp_apply, hr]; simp⟩

/-- **The complement of `X₁ ≠ 0` in upstream's ℙ¹ is the point `[1 : 0]`.** -/
lemma not_mem_openOne_iff (y : projectiveLine.left) : y ∉ openOne ↔ y = infty := by
  rw [mem_openOne_iff, not_mem_U_one_iff, infty]
  constructor
  · intro h
    rw [← h, okaIso_hom_inv_base]
  · rintro rfl
    simp

lemma singleton_infty_eq : ({infty} : Set projectiveLine.left) = (openOne : Set projectiveLine.left)ᶜ := by
  ext y
  simp only [mem_singleton_iff, mem_compl_iff, SetLike.mem_coe]
  exact (not_mem_openOne_iff y).symm

lemma closure_infty : closure ({infty} : Set projectiveLine.left) = {infty} := by
  rw [singleton_infty_eq]
  exact openOne.isOpen.isClosed_compl.closure_eq

/-- `[1 : 0]` has coheight one. -/
lemma coheight_infty : Order.coheight infty = 1 := by
  have hle : Order.coheight infty ≤ 1 :=
    SmoothOfRelativeDimension.coheight_le_complex (f := projectiveLine.hom) (d := 1) infty
  have htop : (⊤ : projectiveLine.left) ∈ openOne := by
    have hz : chartOne.base (Classical.arbitrary _) ∈ openOne := ⟨_, rfl⟩
    exact ((le_top : chartOne.base (Classical.arbitrary _) ≤ ⊤) |>
      (Scheme.le_iff_specializes).mp).mem_open openOne.isOpen hz
  have hlt : infty < ⊤ := by
    refine lt_of_le_not_ge le_top fun h => ?_
    exact ((not_mem_openOne_iff _).mpr rfl)
      (((Scheme.le_iff_specializes).mp h).mem_open openOne.isOpen htop)
  have h0 : Order.coheight infty ≠ 0 := by
    rw [Ne, Order.coheight_eq_zero]
    exact hlt.not_isMax
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr h0)

lemma chartOne_over :
    chartOne ≫ projectiveLine.hom = Spec.map (CommRingCat.ofHom C) := by
  have hfst : okaIso.hom ≫ projectiveLine.hom = AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ :=
    isPullback_projectiveLine.isoPullback_hom_fst
  rw [chartOne, Category.assoc, hfst, AlgebraicGeometry.ProjectiveSpace.chart_toSpec]

/-- The open `X₁ ≠ 0` is affine space over `Spec ℂ`. -/
noncomputable def openOneIso :
    openScheme projectiveLine openOne ≅ Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) :=
  Over.isoMk (chartOne.isoOpensRange.symm ≪≫ (AffineSpace.SpecIso (Fin 1) (.of ℂ)).symm) (by
    change (chartOne.isoOpensRange.inv ≫ (AffineSpace.SpecIso (Fin 1) (.of ℂ)).inv) ≫
      (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) = openOne.ι ≫ projectiveLine.hom
    rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← chartOne_over,
      ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    rfl)

lemma compl_support_infty :
    (cycleComponentSupport projectiveLine infty)ᶜ = Point.overOpen openOne := by
  ext z
  simp only [cycleComponentSupport, closure_infty, mem_compl_iff, mem_preimage,
    mem_singleton_iff]
  rw [← not_mem_openOne_iff, not_not]
  rfl

/-- The complement of `[1 : 0]` in `ℙ¹(ℂ)` is homeomorphic to `ℂ`. -/
noncomputable def complInftyHomeomorph :
    ↥((cycleComponentSupport projectiveLine infty)ᶜ) ≃ₜ (Fin 1 → ℂ) :=
  (Homeomorph.setCongr compl_support_infty).trans
    ((openHomeomorph projectiveLine openOne).symm.trans
      ((Point.isoMapHomeomorph openOneIso).trans (affineSpaceHomeomorph (Fin 1))))

/-- **ℙ¹ has a point of coheight one whose complement is contractible.** -/
theorem exists_point_contractible_compl :
    ∃ (x : projectiveLine.left) (_ : Order.coheight x = 1),
      ContractibleSpace ↥((cycleComponentSupport projectiveLine x)ᶜ) :=
  ⟨infty, coheight_infty, complInftyHomeomorph.toHomotopyEquiv.contractibleSpace⟩

end HodgeLadder.Tests
