module

public import HodgeLadder.General.ProjQuotientMap
public import HodgeLadder.Tests.EllipticCurve
public import LefschetzPort.Oka.AlgebraicGeometry.ProjectiveSpace.LinearSubst

/-!
# Complex multiplication by `i` on the plane cubic

Rung `elliptic-curve-cm`. On `E : y²z = x³ − xz²` (`HodgeLadder.Tests.EllipticCurve`), the
substitution `σ : x ↦ −x, y ↦ iy, z ↦ z` of `ℂ[x, y, z]` sends `F = y²z − x³ + xz²` to `−F`, so it
preserves `(F)` and induces, through `ProjQuotient.projQuotMap`, an endomorphism
`ellipticI : E ⟶ E` over `Spec ℂ`. The substitution `τ : y ↦ −y` fixes `F` and induces
`ellipticNeg`. Both are instances of `diagHom c`, the endomorphism of a diagonal substitution
`Xⱼ ↦ cⱼ Xⱼ` preserving `(F)`; `diagHom c ≫ diagHom d = diagHom (c * d)` is a ring identity of
substitutions read through `Proj.map_comp` (`diagHom_comp`). Since `σ ∘ σ = τ` and `τ ∘ τ = id` hold
exactly as substitutions, with no common rescaling of the variables, this gives:

* `ellipticI_comp_self : ellipticI ≫ ellipticI = ellipticNeg`,
* `ellipticNeg_comp_self : ellipticNeg ≫ ellipticNeg = 𝟙 _`,
* `ellipticI_pow_four : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI = 𝟙 _`.

On points. `Proj.map` of a substitution pulls back coordinates, so the point with coordinates `v`
goes to the point with coordinates `(cⱼ vⱼ)`: in the chart `z ≠ 0`, `(x, y) ↦ (−x, iy)` for `[i]`
and `(x, y) ↦ (x, −y)` for `[−1]` (`chartComplexPoint_comp_diagHom`). Tests: both fix the origin
`[0 : 0 : 1]`; `[i]` swaps the two-torsion points `(±1, 0)` and `[−1]` fixes them, so `[i]` is
neither `𝟙` nor `[−1]` (`ellipticI_ne_id`, `ellipticI_ne_ellipticNeg`); `[−1]` moves `(i, 1 − i)`,
so `[−1] ≠ 𝟙` and `[i]` has order four (`ellipticNeg_ne_id`); `[i]` sends `(i, 1 − i)` to
`(−i, 1 + i)`, which pins the scalar `i` on `y` against its inverse `−i`.

## Main definitions

* `HodgeLadder.Tests.diagSubst`, `diagEquiv`, `diagGraded`, `diagEndo`, `diagHom`, `chartSubst`
* `HodgeLadder.Tests.iScalars`, `negScalars`, `ellipticI`, `ellipticNeg`, `ellipticIIso`
* `HodgeLadder.Tests.ellipticCurvePointI`, `ellipticCurvePointNegI`, `ellipticCurvePointIFlip`

## Main results

* `HodgeLadder.Tests.diagEndo_ι`, `diagHom_comp`, `diagHom_one`, `chart_comp_linearSubstMap_diag`,
  `chartComplexPoint_comp_diagHom`, `chartComplexPoint_injective`
* `HodgeLadder.Tests.diagSubst_iScalars_cubicForm`, `diagSubst_negScalars_cubicForm`
* `HodgeLadder.Tests.ellipticI_comp_self`, `ellipticNeg_comp_self`, `ellipticI_pow_four`
* `HodgeLadder.Tests.ellipticCurveOrigin_comp_ellipticI`,
  `ellipticCurveTwoTorsionPos_comp_ellipticI`, `ellipticCurvePointI_comp_ellipticI`,
  `ellipticI_ne_id`, `ellipticI_ne_ellipticNeg`, `ellipticCurvePointI_comp_ellipticNeg`,
  `ellipticNeg_ne_id`
* `HodgeLadder.Tests.ellipticIIso_inv`, instance `HodgeLadder.Tests.isIso_ellipticI`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped AlgebraicGeometry.ProjectiveSpace

namespace HodgeLadder.Tests

local notation "𝒜" => homogeneousSubmodule (Fin (2 + 1)) ℂ

/-- The diagonal substitution `Xⱼ ↦ cⱼ Xⱼ` of `ℂ[x, y, z]`. -/
def diagSubst (c : Fin 3 → ℂ) : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval fun j => C (c j) * X j

/-- `diagSubst c` sends `Xⱼ` to `cⱼ Xⱼ`. -/
@[simp]
theorem diagSubst_X (c : Fin 3 → ℂ) (j : Fin 3) : diagSubst c (X j) = C (c j) * X j :=
  aeval_X _ _

/-- `diagSubst c` fixes the constants. -/
@[simp]
theorem diagSubst_C (c : Fin 3 → ℂ) (r : ℂ) : diagSubst c (C r) = C r :=
  (diagSubst c).commutes r

/-- Composing diagonal substitutions multiplies the scalars. -/
theorem diagSubst_comp (c d : Fin 3 → ℂ) :
    (diagSubst c).comp (diagSubst d) = diagSubst (c * d) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, diagSubst_X, map_mul, diagSubst_X, diagSubst_X, Pi.mul_apply, map_mul,
    show diagSubst c (C (d j)) = C (d j) from (diagSubst c).commutes (d j)]
  ring

/-- The diagonal substitution with all scalars one is the identity. -/
theorem diagSubst_one : diagSubst 1 = AlgHom.id ℂ (MvPolynomial (Fin 3) ℂ) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  simp

/-- The diagonal substitution with nonzero scalars, as an automorphism. -/
def diagEquiv (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0) :
    MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  AlgEquiv.ofAlgHom (diagSubst c) (diagSubst c⁻¹)
    (by rw [diagSubst_comp, show c * c⁻¹ = 1 from funext fun j => mul_inv_cancel₀ (hc j),
      diagSubst_one])
    (by rw [diagSubst_comp, show c⁻¹ * c = 1 from funext fun j => inv_mul_cancel₀ (hc j),
      diagSubst_one])

/-- A diagonal substitution sends every variable to a linear form. -/
theorem isLinearSubst_diagSubst (c : Fin 3 → ℂ) :
    AlgebraicGeometry.ProjectiveSpace.IsLinearSubst (n := 2) (diagSubst c) := fun j => by
  rw [diagSubst_X, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (X_mem_homogeneousSubmodule_one j)

/-- The diagonal substitution as a graded ring map of `ℂ[x, y, z]`. -/
abbrev diagGraded (c : Fin 3 → ℂ) : 𝒜 →+*ᵍ 𝒜 :=
  AlgebraicGeometry.ProjectiveSpace.linearSubstGradedHom (diagSubst c) (isLinearSubst_diagSubst c)

/-- A diagonal substitution with `c F ∈ (F)` preserves the ideal `(F)` of `E`. -/
theorem ideal_le_comap_diagSubst (c : Fin 3 → ℂ)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) :
    (Hypersurface.ideal cubicForm cubicForm_mem).toIdeal ≤
      (Hypersurface.ideal cubicForm cubicForm_mem).toIdeal.comap
        ((diagGraded c : 𝒜 →+*ᵍ 𝒜) : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 3) ℂ) :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hF)

/-- A diagonal substitution with nonzero scalars is onto, so it meets the hypothesis of
`Proj.map`. -/
theorem irrelevant_le_map_diagGraded (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map (diagGraded c) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _ (diagEquiv c hc).surjective

/-- **The endomorphism of `E` of a diagonal substitution** `[x : y : z] ↦ [c₀x : c₁y : c₂z]`
preserving `(F)`: `Proj.map` of the induced graded map of `ℂ[x, y, z] ⧸ (F)`. -/
def diagEndo (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) :
    ellipticCurveScheme ⟶ ellipticCurveScheme :=
  ProjQuotient.projQuotMap (diagGraded c) (ideal_le_comap_diagSubst c hF)
    (irrelevant_le_map_diagGraded c hc)

/-- `diagEndo c` lies over the automorphism of `ℙ²` induced by the same substitution. -/
@[reassoc]
theorem diagEndo_ι (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) :
    diagEndo c hc hF ≫ ellipticCurveι =
      ellipticCurveι ≫ AlgebraicGeometry.ProjectiveSpace.linearSubstMap (diagEquiv c hc)
        (isLinearSubst_diagSubst c) :=
  ProjQuotient.projQuotMap_quotι _ _ _

/-- **The endomorphism of `E` over `Spec ℂ`** of a diagonal substitution preserving `(F)`. -/
def diagHom (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) : ellipticCurve ⟶ ellipticCurve :=
  Over.homMk (diagEndo c hc hF) (by
    change diagEndo c hc hF ≫ ellipticCurveι ≫ _ = ellipticCurveι ≫ _
    rw [diagEndo_ι_assoc]
    exact congrArg (ellipticCurveι ≫ ·)
      (AlgebraicGeometry.ProjectiveSpace.linearSubstMap_toSpec (diagEquiv c hc)
        (isLinearSubst_diagSubst c) (isLinearSubst_diagSubst c⁻¹)))

/-- The underlying morphism of schemes of `diagHom c` is `diagEndo c`. -/
@[simp]
theorem diagHom_left (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) :
    (diagHom c hc hF).left = diagEndo c hc hF := rfl

/-- **Composition of diagonal endomorphisms** multiplies the scalars. -/
theorem diagHom_comp (c d : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0) (hd : ∀ j, d j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm})
    (hG : diagSubst d cubicForm ∈ Ideal.span {cubicForm})
    (hcd : ∀ j, (c * d) j ≠ 0) (hH : diagSubst (c * d) cubicForm ∈ Ideal.span {cubicForm}) :
    diagHom c hc hF ≫ diagHom d hd hG = diagHom (c * d) hcd hH := by
  ext1
  rw [Over.comp_left, diagHom_left, diagHom_left, diagHom_left, diagEndo, diagEndo, diagEndo,
    ← ProjQuotient.projQuotMap_comp]
  refine ProjQuotient.projQuotMap_congr (GradedRingHom.ext fun p => ?_) _ _ _ _
  change diagSubst c (diagSubst d p) = diagSubst (c * d) p
  rw [← diagSubst_comp]
  rfl

/-- The diagonal endomorphism with all scalars one is the identity. -/
theorem diagHom_one (hF : diagSubst 1 cubicForm ∈ Ideal.span {cubicForm}) :
    diagHom 1 (fun _ => one_ne_zero) hF = 𝟙 ellipticCurve := by
  ext1
  rw [diagHom_left, Over.id_left, diagEndo]
  refine (ProjQuotient.projQuotMap_congr (GradedRingHom.ext fun p => ?_) _
    (by exact le_refl _) _ (by simp)).trans (ProjQuotient.projQuotMap_id _ _)
  change diagSubst 1 p = p
  rw [diagSubst_one]
  rfl

/-! ### The diagonal substitutions in the standard charts -/

/-- The automorphism of `ℙ²` of a diagonal substitution is `Proj.map` of the graded map. -/
theorem linearSubstMap_diag (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0) :
    AlgebraicGeometry.ProjectiveSpace.linearSubstMap (diagEquiv c hc)
        (isLinearSubst_diagSubst c) =
      Proj.map (diagGraded c) (irrelevant_le_map_diagGraded c hc) := rfl

/-- The diagonal substitution `Yⱼ ↦ dⱼ Yⱼ` of `ℂ[Y₀, Y₁]`. -/
def chartSubst (d : Fin 2 → ℂ) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval fun j => C (d j) * X j

/-- `chartSubst d` sends `Yⱼ` to `dⱼ Yⱼ`. -/
@[simp]
theorem chartSubst_X (d : Fin 2 → ℂ) (j : Fin 2) : chartSubst d (X j) = C (d j) * X j :=
  aeval_X _ _

/-- `chartSubst d` fixes the constants. -/
@[simp]
theorem chartSubst_C (d : Fin 2 → ℂ) (r : ℂ) : chartSubst d (C r) = C r :=
  (chartSubst d).commutes r

/-- Evaluation at `v` after `Yⱼ ↦ dⱼ Yⱼ` is evaluation at `(dⱼ vⱼ)`. -/
theorem eval_comp_chartSubst (d v : Fin 2 → ℂ) :
    (eval v).comp (chartSubst d).toRingHom = eval (d * v) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp [chartSubst]
  · simp [chartSubst]

/-- The value of a degree-zero element in the localization. -/
theorem val_fromZeroRingHom {P : Submonoid (MvPolynomial (Fin 3) ℂ)} (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 P a).val = Localization.mk (a : MvPolynomial (Fin 3) ℂ) 1 := rfl

/-- On `D₊(Xᵢ)`, the substitution `Xⱼ ↦ cⱼ Xⱼ` with `cᵢ = 1` is `Yⱼ ↦ c_{i.succAbove j} Yⱼ` on
`ℂ[Y₀, Y₁]` (`Yⱼ = X_{i.succAbove j} / Xᵢ`). -/
theorem awayMap_comp_toAwayX (i : Fin 3) (c : Fin 3 → ℂ) (hci : c i = 1) :
    (HomogeneousLocalization.map (diagGraded c) (P := .powers (X i)) (Q := .powers (X i))
        (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp [hci]⟩)).comp (toAwayX ℂ i) =
      (toAwayX ℂ i).comp (chartSubst (c ∘ i.succAbove)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · apply HomogeneousLocalization.val_injective
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      chartSubst_C, toAwayX_C, awayXBase, RingHom.comp_apply, val_fromZeroRingHom]
    change Localization.mk (diagSubst c (algebraMap ℂ (𝒜 0) r : MvPolynomial (Fin 3) ℂ))
      ⟨diagSubst c 1, _⟩ = _
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp⟩
  · apply HomogeneousLocalization.val_injective
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      chartSubst_X, map_mul, toAwayX_C, toAwayX_X, val_mul, val_awayXDiv, awayXBase,
      RingHom.comp_apply, val_fromZeroRingHom]
    change Localization.mk (diagSubst c (X (i.succAbove k))) ⟨diagSubst c (X i ^ 1), _⟩ = _
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [hci]⟩

/-- **The diagonal substitution in the chart `Xᵢ ≠ 0`** of `ℙ²`, for `cᵢ = 1`. -/
@[reassoc]
theorem chart_comp_linearSubstMap_diag (i : Fin 3) (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hci : c i = 1) :
    AlgebraicGeometry.ProjectiveSpace.chart i ≫
        AlgebraicGeometry.ProjectiveSpace.linearSubstMap (diagEquiv c hc)
          (isLinearSubst_diagSubst c) =
      Spec.map (CommRingCat.ofHom (chartSubst (c ∘ i.succAbove)).toRingHom) ≫
        AlgebraicGeometry.ProjectiveSpace.chart i := by
  rw [AlgebraicGeometry.ProjectiveSpace.chart, Category.assoc, linearSubstMap_diag,
    Proj.awayι_comp_map_of_eq _ _ _ (X_mem_homogeneousSubmodule_one i) _
      (show diagGraded c (X i) = X i by simp [hci]),
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext p : 2
  apply (awayXEquiv ℂ i).injective
  obtain ⟨p, rfl⟩ := (awayXEquiv ℂ i).surjective p
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayXEquiv_symm_apply,
    awayXEquiv_apply, fromAwayX_toAwayX, toAwayX_fromAwayX]
  exact congr($(awayMap_comp_toAwayX i c hci) p)

/-- **The action on chart points.** For `cᵢ = 1`, the diagonal endomorphism sends the point of
the chart `Xᵢ ≠ 0` with affine coordinates `v` to the one with coordinates `c_{i.succAbove j} vⱼ`:
`[v] ↦ [c · v]`. -/
theorem chartComplexPoint_comp_diagHom (i : Fin 3) (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) (hci : c i = 1) (v : Fin 2 → ℂ)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0)
    (hv' : eval ((c ∘ i.succAbove) * v) (dehomogenize ℂ i cubicForm) = 0) :
    chartComplexPoint i v hv ≫ diagHom c hc hF =
      chartComplexPoint i ((c ∘ i.succAbove) * v) hv' := by
  ext1
  refine (cancel_mono ellipticCurveι).mp ?_
  rw [Over.comp_left, Category.assoc, diagHom_left, diagEndo_ι, ← Category.assoc,
    chartComplexPoint_ι, Category.assoc, chart_comp_linearSubstMap_diag i c hc hci,
    ← Category.assoc, ← Spec.map_comp, chartComplexPoint_ι]
  congr 2
  exact congrArg CommRingCat.ofHom (eval_comp_chartSubst _ v)

/-- Chart points with equal coordinates are equal. -/
theorem chartComplexPoint_congr (i : Fin 3) {v w : Fin 2 → ℂ} (h : v = w)
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) (hw : eval w (dehomogenize ℂ i cubicForm) = 0) :
    chartComplexPoint i v hv = chartComplexPoint i w hw := by
  subst h
  rfl

/-- The action on chart points, with the target coordinates named. -/
theorem chartComplexPoint_comp_diagHom_eq (i : Fin 3) (c : Fin 3 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm}) (hci : c i = 1) {v w : Fin 2 → ℂ}
    (hvw : (c ∘ i.succAbove) * v = w) (hv : eval v (dehomogenize ℂ i cubicForm) = 0)
    (hw : eval w (dehomogenize ℂ i cubicForm) = 0) :
    chartComplexPoint i v hv ≫ diagHom c hc hF = chartComplexPoint i w hw :=
  (chartComplexPoint_comp_diagHom i c hc hF hci v hv (hvw ▸ hw)).trans
    (chartComplexPoint_congr i hvw _ _)

/-- Chart points with different coordinates are different. -/
theorem chartComplexPoint_injective (i : Fin 3) {v w : Fin 2 → ℂ}
    (hv : eval v (dehomogenize ℂ i cubicForm) = 0) (hw : eval w (dehomogenize ℂ i cubicForm) = 0)
    (h : chartComplexPoint i v hv = chartComplexPoint i w hw) : v = w := by
  have h1 := congrArg (fun p : ComplexPoint ellipticCurve => p.left ≫ ellipticCurveι) h
  simp only [chartComplexPoint_ι] at h1
  have h2 := Spec.map_injective ((cancel_mono _).mp h1)
  funext j
  simpa using congr($(congrArg CommRingCat.Hom.hom h2) (X j))

/-- Diagonal endomorphisms with equal scalars are equal. -/
theorem diagHom_congr {c d : Fin 3 → ℂ} (h : c = d) (hc : ∀ j, c j ≠ 0) (hd : ∀ j, d j ≠ 0)
    (hF : diagSubst c cubicForm ∈ Ideal.span {cubicForm})
    (hG : diagSubst d cubicForm ∈ Ideal.span {cubicForm}) :
    diagHom c hc hF = diagHom d hd hG := by
  subst h
  rfl

/-! ### Multiplication by `i` and by `−1` -/

/-- The scalars `(−1, i, 1)` of `[x : y : z] ↦ [−x : iy : z]`. -/
def iScalars : Fin 3 → ℂ := ![-1, Complex.I, 1]

/-- The scalars `(1, −1, 1)` of `[x : y : z] ↦ [x : −y : z]`. -/
def negScalars : Fin 3 → ℂ := ![1, -1, 1]

/-- The scalars of `[i]` are nonzero. -/
theorem iScalars_ne_zero : ∀ j, iScalars j ≠ 0 := by
  intro j; fin_cases j <;> simp [iScalars, Complex.I_ne_zero]

/-- The scalars of `[−1]` are nonzero. -/
theorem negScalars_ne_zero : ∀ j, negScalars j ≠ 0 := by
  intro j; fin_cases j <;> simp [negScalars]

/-- The substitution of `[i]`: `x ↦ −x`. -/
theorem diagSubst_iScalars_X_zero : diagSubst iScalars (X 0) = -X 0 := by
  simp [iScalars]

/-- The substitution of `[i]`: `y ↦ iy`. -/
theorem diagSubst_iScalars_X_one : diagSubst iScalars (X 1) = C Complex.I * X 1 := by
  simp [iScalars]

/-- The substitution of `[i]`: `z ↦ z`. -/
theorem diagSubst_iScalars_X_two : diagSubst iScalars (X 2) = X 2 := by
  simp [iScalars]

/-- The substitution of `[−1]`: `x ↦ x`. -/
theorem diagSubst_negScalars_X_zero : diagSubst negScalars (X 0) = X 0 := by
  simp [negScalars]

/-- The substitution of `[−1]`: `y ↦ −y`. -/
theorem diagSubst_negScalars_X_one : diagSubst negScalars (X 1) = -X 1 := by
  simp [negScalars]

/-- The substitution of `[−1]`: `z ↦ z`. -/
theorem diagSubst_negScalars_X_two : diagSubst negScalars (X 2) = X 2 := by
  simp [negScalars]

/-- **`[i]` negates the cubic form**: `(iy)²z − (−x)³ + (−x)z² = −(y²z − x³ + xz²)`. -/
theorem diagSubst_iScalars_cubicForm : diagSubst iScalars cubicForm = -cubicForm := by
  have hI : (C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [cubicForm, map_add, map_sub, map_mul, map_pow, diagSubst_iScalars_X_zero,
    diagSubst_iScalars_X_one, diagSubst_iScalars_X_two]
  linear_combination (X 1 ^ 2 * X 2) * hI

/-- **`[−1]` fixes the cubic form.** -/
theorem diagSubst_negScalars_cubicForm : diagSubst negScalars cubicForm = cubicForm := by
  simp only [cubicForm, map_add, map_sub, map_mul, map_pow, diagSubst_negScalars_X_zero,
    diagSubst_negScalars_X_one, diagSubst_negScalars_X_two]
  ring

/-- `[i]` preserves the ideal `(F)`. -/
theorem diagSubst_iScalars_mem : diagSubst iScalars cubicForm ∈ Ideal.span {cubicForm} := by
  rw [diagSubst_iScalars_cubicForm]
  exact neg_mem (Ideal.subset_span rfl)

/-- `[−1]` preserves the ideal `(F)`. -/
theorem diagSubst_negScalars_mem : diagSubst negScalars cubicForm ∈ Ideal.span {cubicForm} := by
  rw [diagSubst_negScalars_cubicForm]
  exact Ideal.subset_span rfl

/-- **Complex multiplication by `i`** on `E`, `[x : y : z] ↦ [−x : iy : z]`, over `Spec ℂ`. -/
def ellipticI : ellipticCurve ⟶ ellipticCurve :=
  diagHom iScalars iScalars_ne_zero diagSubst_iScalars_mem

/-- **Multiplication by `−1`** on `E`, `[x : y : z] ↦ [x : −y : z]`, over `Spec ℂ`; defined by the
substitution `y ↦ −y` itself. -/
def ellipticNeg : ellipticCurve ⟶ ellipticCurve :=
  diagHom negScalars negScalars_ne_zero diagSubst_negScalars_mem

/-- `(−1, i, 1)² = (1, −1, 1)`. -/
theorem iScalars_mul_self : iScalars * iScalars = negScalars := by
  funext j; fin_cases j <;> simp [iScalars, negScalars]

/-- `(1, −1, 1)² = 1`. -/
theorem negScalars_mul_self : negScalars * negScalars = 1 := by
  funext j; fin_cases j <;> simp [negScalars]

/-- **`[i] ∘ [i] = [−1]`**, exactly: the substitution `(x, y, z) ↦ (−x, iy, z)` applied twice is
`(x, y, z) ↦ (x, −y, z)`. -/
theorem ellipticI_comp_self : ellipticI ≫ ellipticI = ellipticNeg :=
  (diagHom_comp _ _ _ _ _ _ (iScalars_mul_self ▸ negScalars_ne_zero)
    (iScalars_mul_self ▸ diagSubst_negScalars_mem)).trans (diagHom_congr iScalars_mul_self _ _ _ _)

/-- **`[−1] ∘ [−1] = 𝟙`.** -/
theorem ellipticNeg_comp_self : ellipticNeg ≫ ellipticNeg = 𝟙 ellipticCurve := by
  have h1 : diagSubst 1 cubicForm ∈ Ideal.span {cubicForm} := by
    rw [diagSubst_one]; exact Ideal.subset_span rfl
  exact (diagHom_comp _ _ _ _ _ _ (negScalars_mul_self ▸ fun _ => one_ne_zero)
    (negScalars_mul_self ▸ h1)).trans
    ((diagHom_congr negScalars_mul_self _ (fun _ => one_ne_zero) _ h1).trans (diagHom_one h1))

/-- **`[i]⁴ = 𝟙`.** -/
theorem ellipticI_pow_four : ellipticI ≫ ellipticI ≫ ellipticI ≫ ellipticI = 𝟙 ellipticCurve := by
  rw [← Category.assoc, ellipticI_comp_self, ellipticNeg_comp_self]

/-! ### Tests: the action on the origin and the two-torsion points -/

/-- `[i]` fixes the origin `[0 : 0 : 1]`. -/
theorem ellipticCurveOrigin_comp_ellipticI :
    ellipticCurveOrigin ≫ ellipticI = ellipticCurveOrigin :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [iScalars])
    (by funext j; fin_cases j <;> simp [iScalars]) _ _

/-- `[−1]` fixes the origin `[0 : 0 : 1]`. -/
theorem ellipticCurveOrigin_comp_ellipticNeg :
    ellipticCurveOrigin ≫ ellipticNeg = ellipticCurveOrigin :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [negScalars])
    (by funext j; fin_cases j <;> simp [negScalars]) _ _

/-- **`[i]` sends `(1, 0)` to `(−1, 0)`**: `x ↦ −x` on the two-torsion points. -/
theorem ellipticCurveTwoTorsionPos_comp_ellipticI :
    ellipticCurveTwoTorsionPos ≫ ellipticI = ellipticCurveTwoTorsionNeg :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [iScalars])
    (by funext j; fin_cases j <;> simp [iScalars]) _ _

/-- `[i]` sends `(−1, 0)` to `(1, 0)`. -/
theorem ellipticCurveTwoTorsionNeg_comp_ellipticI :
    ellipticCurveTwoTorsionNeg ≫ ellipticI = ellipticCurveTwoTorsionPos :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [iScalars])
    (by funext j; fin_cases j <;> simp [iScalars]) _ _

/-- `[−1]` fixes `(1, 0)`. -/
theorem ellipticCurveTwoTorsionPos_comp_ellipticNeg :
    ellipticCurveTwoTorsionPos ≫ ellipticNeg = ellipticCurveTwoTorsionPos :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [negScalars])
    (by funext j; fin_cases j <;> simp [negScalars]) _ _

/-- `[−1]` fixes `(−1, 0)`. -/
theorem ellipticCurveTwoTorsionNeg_comp_ellipticNeg :
    ellipticCurveTwoTorsionNeg ≫ ellipticNeg = ellipticCurveTwoTorsionNeg :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [negScalars])
    (by funext j; fin_cases j <;> simp [negScalars]) _ _

/-- The point `(i, 1 − i)` of `E`: `(1 − i)² = −2i = i³ − i`. -/
def ellipticCurvePointI : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![Complex.I, 1 - Complex.I] (by
    rw [dehomogenize_two_cubicForm]
    simp only [map_add, map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (1 - Complex.I) * Complex.I_sq)

/-- The point `(−i, 1 + i)` of `E`: `(1 + i)² = 2i = (−i)³ − (−i)`. -/
def ellipticCurvePointNegI : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![-Complex.I, 1 + Complex.I] (by
    rw [dehomogenize_two_cubicForm]
    simp only [map_add, map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (1 + Complex.I) * Complex.I_sq)

/-- **`[i]` sends `(i, 1 − i)` to `(−i, 1 + i)`**: `y ↦ iy` with `i (1 − i) = 1 + i`. This pins the
scalar on `y` to `i`, and the direction of `Proj.map` on points: the inverse substitution
`(x, y) ↦ (−x, −iy)` would give `(−i, −1 − i)`. -/
theorem ellipticCurvePointI_comp_ellipticI :
    ellipticCurvePointI ≫ ellipticI = ellipticCurvePointNegI :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [iScalars])
    (by
      funext j
      fin_cases j
      · simp [iScalars]
      · simp [iScalars, show (2 : Fin 3).succAbove 1 = 1 from rfl]
        linear_combination -Complex.I_sq) _ _

/-- The two-torsion points `(1, 0)` and `(−1, 0)` are different. -/
theorem ellipticCurveTwoTorsionPos_ne_neg :
    ellipticCurveTwoTorsionPos ≠ ellipticCurveTwoTorsionNeg := by
  intro h
  have := congrFun (chartComplexPoint_injective 2 _ _ h) 0
  norm_num at this

/-- **`[i]` is not the identity**: it moves `(1, 0)`. -/
theorem ellipticI_ne_id : ellipticI ≠ 𝟙 ellipticCurve := by
  intro h
  have := ellipticCurveTwoTorsionPos_comp_ellipticI
  rw [h, Category.comp_id] at this
  exact ellipticCurveTwoTorsionPos_ne_neg this

/-- **`[i]` is not `[−1]`**: `[i]` moves `(1, 0)` and `[−1]` fixes it. -/
theorem ellipticI_ne_ellipticNeg : ellipticI ≠ ellipticNeg := by
  intro h
  have := ellipticCurveTwoTorsionPos_comp_ellipticI
  rw [h, ellipticCurveTwoTorsionPos_comp_ellipticNeg] at this
  exact ellipticCurveTwoTorsionPos_ne_neg this

/-- The point `(i, i − 1)` of `E`, the reflection `y ↦ −y` of `(i, 1 − i)`. -/
def ellipticCurvePointIFlip : ComplexPoint ellipticCurve :=
  chartComplexPoint 2 ![Complex.I, -(1 - Complex.I)] (by
    rw [dehomogenize_two_cubicForm]
    simp only [map_add, map_sub, map_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (1 - Complex.I) * Complex.I_sq)

/-- `[−1]` sends `(i, 1 − i)` to `(i, i − 1)`. -/
theorem ellipticCurvePointI_comp_ellipticNeg :
    ellipticCurvePointI ≫ ellipticNeg = ellipticCurvePointIFlip :=
  chartComplexPoint_comp_diagHom_eq 2 _ _ _ (by simp [negScalars])
    (by funext j; fin_cases j <;> simp [negScalars, show (2 : Fin 3).succAbove 1 = 1 from rfl]) _ _

/-- **`[−1]` is not the identity**: it moves `(i, 1 − i)`. So `[i]` has order exactly four. -/
theorem ellipticNeg_ne_id : ellipticNeg ≠ 𝟙 ellipticCurve := by
  intro h
  have := ellipticCurvePointI_comp_ellipticNeg
  rw [h, Category.comp_id] at this
  have h2 := congrFun (chartComplexPoint_injective 2 _ _ this) 1
  simp at h2
  norm_num [Complex.ext_iff] at h2

/-- **`[i]` is an automorphism of `E`**, with inverse `[i]³ = [i] ≫ [−1]`. -/
def ellipticIIso : ellipticCurve ≅ ellipticCurve where
  hom := ellipticI
  inv := ellipticI ≫ ellipticNeg
  hom_inv_id := by rw [← Category.assoc, ellipticI_comp_self, ellipticNeg_comp_self]
  inv_hom_id := by
    rw [← ellipticI_comp_self]
    simp only [Category.assoc]
    exact ellipticI_pow_four

/-- The inverse of `[i]` is `[i]³`, the form `elliptic-square-witness` uses. -/
theorem ellipticIIso_inv : ellipticIIso.inv = ellipticI ≫ ellipticI ≫ ellipticI := by
  rw [ellipticI_comp_self]
  rfl

/-- `[i]` is an isomorphism. -/
instance isIso_ellipticI : IsIso ellipticI := ellipticIIso.isIso_hom

end HodgeLadder.Tests
