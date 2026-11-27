module

public import HodgeLadder.Hodge.CupFiltration
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# The wedge of algebraic forms descends to holomorphic forms

Rung `wedge-descends` (front `cup`, sub-rung of `cup-hodge-filtration`; red team
`docs/sketches/cup-hodge-filtration.redteam.md`, finding 8). Upstream defines the holomorphic
`p`-forms on an analytic open `U ⊆ X(ℂ)` as the quotient
`HolomorphicForm X d U p = Form ℂ 𝒪(U) p ⧸ chartEvaluationKernel X d U p`, where the kernel
consists of the algebraic Kähler forms whose evaluations by coordinate derivatives vanish at every
point of every chosen chart. This file proves that the kernel is a two-sided ideal for the wedge
product `HodgeLadder.formWedge` (multiplication in `⋀_{𝒪(U)} Ω_{𝒪(U)/ℂ}`), on both sides
separately, since graded commutativity of the exterior algebra is not at the pin.

## Route

Fix a chart `e` at `z` with coordinate domain `D = {y ∈ e.target | e.symm y ∈ U}`, and write
`V = ℂ^d`, `V^* = Module.Dual ℂ V`. Make `D → ⋀_ℂ V^*` an `𝒪(U)`-algebra through upstream's
`chartSectionAlgHom` (pointwise multiplication by `f ∘ e.symm`). The `𝒪(U)`-linear map
`Ω_{𝒪(U)/ℂ} → D → ⋀_ℂ V^*`, `df ↦ (y ↦ ι (D(f ∘ e.symm)(y)))`, comes from upstream's
`chartDerivation`; it squares to zero pointwise, so `ExteriorAlgebra.lift` extends it to an
algebra map `HodgeLadder.chartExtMap : ⋀_{𝒪(U)} Ω_{𝒪(U)/ℂ} →ₐ D → ⋀_ℂ V^*`. On a form `θ` of
degree `p` its value at `y` lies in `⋀^p_ℂ V^*`, and Mathlib's pairing
`exteriorPower.pairingDual` carries it to upstream's chart evaluation of `θ` at `y`
(`HodgeLadder.pairingDual_chartPointForm`; the two determinants are transposes of each other).
The pairing is bijective for `V` finite free (`exteriorPower.bijective_pairingDual`), so the chart
evaluation of `θ` at `y` vanishes exactly when `chartExtMap θ y = 0`. Multiplicativity of
`chartExtMap` then gives both sides of `WedgeDescends`.

## Main definitions

* `HodgeLadder.chartCovAlgebra`: the `𝒪(U)`-algebra structure on `D → ⋀_ℂ V^*`
* `HodgeLadder.chartCovι`, `HodgeLadder.chartExtMap`: pointwise `ι` and the algebra map
* `HodgeLadder.chartPointForm`: the value of `chartExtMap θ` at `y`, as an element of `⋀^p_ℂ V^*`

## Main results

* `HodgeLadder.pairingDual_chartPointForm`: the pairing of `chartPointForm θ y` with
  `v₁ ∧ ⋯ ∧ v_p` is the chart evaluation of `θ` at `y` on `(v₁, …, v_p)`
* `HodgeLadder.mem_chartEvaluationKernel_iff_chartExtMap`
* `HodgeLadder.wedgeDescends : WedgeDescends`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLadder

section ChartPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)

attribute [local instance] chartFieldModule chartFieldTower

/-- Fields on the coordinate domain `D` of the chart at `z` with values in the exterior algebra
`⋀_ℂ (ℂ^d)^*` of algebraic covectors. -/
abbrev ChartCovAlg : Type :=
  ↥(chartSectionDomain X d U z) → ExteriorAlgebra ℂ (Module.Dual ℂ (Fin d → ℂ))

/-- The `𝒪(U)`-algebra structure on `D → ⋀_ℂ (ℂ^d)^*`: a holomorphic function `f` acts at `y`
by the scalar `f(e.symm y)` (upstream's `chartFieldModule`). Kept local, not an instance. -/
abbrev chartCovAlgebra : Algebra (OpenHolomorphicFunctions X d U) (ChartCovAlg X d U z) :=
  Algebra.ofModule
    (fun f x y => by
      funext w
      simp only [Pi.mul_apply, chartFieldModule_smul_apply, smul_mul_assoc])
    (fun f x y => by
      funext w
      simp only [Pi.mul_apply, chartFieldModule_smul_apply, mul_smul_comm])

attribute [local instance] chartCovAlgebra

/-- Pointwise `ι`: a field of continuous covectors on `D` goes to the field of their images in
degree one of `⋀_ℂ (ℂ^d)^*`. It is `𝒪(U)`-linear for the chart-field module structures. -/
def chartCovι :
    (↥(chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ)) →ₗ[OpenHolomorphicFunctions X d U]
      ChartCovAlg X d U z where
  toFun F w := ExteriorAlgebra.ι ℂ ((F w : (Fin d → ℂ) →L[ℂ] ℂ) : Module.Dual ℂ (Fin d → ℂ))
  map_add' F G := by funext w; simp
  map_smul' f F := by
    funext w
    simp only [chartFieldModule_smul_apply, RingHom.id_apply]
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul]

/-- **Pointwise chart evaluation as an algebra map.** The `𝒪(U)`-algebra map
`⋀_{𝒪(U)} Ω_{𝒪(U)/ℂ} → (D → ⋀_ℂ (ℂ^d)^*)` sending `df` to `y ↦ D(f ∘ e.symm)(y)`, by the universal
property of the exterior algebra applied to upstream's `chartDerivation`. -/
def chartExtMap :
    Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U) →ₐ[OpenHolomorphicFunctions X d U]
      ChartCovAlg X d U z :=
  ExteriorAlgebra.lift _
    ⟨(chartCovι X d U z).comp (chartDerivation X d U z).liftKaehlerDifferential,
      fun _ => by funext w; exact ExteriorAlgebra.ι_sq_zero _⟩

/-- `chartExtMap` on `df₁ ∧ ⋯ ∧ df_p` at `y` is the wedge of the coordinate derivatives. -/
lemma chartExtMap_ιMulti (p : ℕ) (v : Fin p → OpenHolomorphicFunctions X d U)
    (y : ↥(chartSectionDomain X d U z)) :
    chartExtMap X d U z
        (ExteriorAlgebra.ιMulti _ p fun i => KaehlerDifferential.D ℂ _ (v i)) y =
      ExteriorAlgebra.ιMulti ℂ p fun i =>
        ((chartSectionDifferential X d U z (v i) y.1 : (Fin d → ℂ) →L[ℂ] ℂ) :
          Module.Dual ℂ (Fin d → ℂ)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn,
    Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  simp [chartExtMap, chartCovι, Function.comp]

/-- `chartExtMap` is `𝒪(U)`-linear, with `f` acting at `y` by `f(e.symm y)`. -/
lemma chartExtMap_smul (f : OpenHolomorphicFunctions X d U)
    (x : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U))
    (y : ↥(chartSectionDomain X d U z)) :
    chartExtMap X d U z (f • x) y = chartSection X d U z f y.1 • chartExtMap X d U z x y := by
  rw [map_smul]; rfl

/-- `chartExtMap` on a generator `a₀ da₁ ∧ ⋯ ∧ da_p`. -/
lemma chartExtMap_mk (p : ℕ) (a₀ : OpenHolomorphicFunctions X d U)
    (v : Fin p → OpenHolomorphicFunctions X d U) (y : ↥(chartSectionDomain X d U z)) :
    chartExtMap X d U z (Algebra.DeRham.mk ℂ _ p a₀ v : Algebra.DeRham.ExtAlg ℂ _) y =
      chartSection X d U z a₀ y.1 • ExteriorAlgebra.ιMulti ℂ p fun i =>
        ((chartSectionDifferential X d U z (v i) y.1 : (Fin d → ℂ) →L[ℂ] ℂ) :
          Module.Dual ℂ (Fin d → ℂ)) := by
  rw [Algebra.DeRham.coe_mk, chartExtMap_smul, chartExtMap_ιMulti]

/-- `chartExtMap` is `ℂ`-linear pointwise. -/
lemma chartExtMap_complex_smul (c : ℂ)
    (x : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U))
    (y : ↥(chartSectionDomain X d U z)) :
    chartExtMap X d U z (c • x) y = c • chartExtMap X d U z x y := by
  rw [← algebraMap_smul (OpenHolomorphicFunctions X d U) c x, chartExtMap_smul]
  congr 1
  rw [chartSection_apply_of_mem X d U z _ y.2]
  rfl

/-- `chartExtMap` carries a form of degree `p` into `⋀^p_ℂ (ℂ^d)^*` at every point. -/
lemma chartExtMap_mem (p : ℕ) (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (y : ↥(chartSectionDomain X d U z)) :
    chartExtMap X d U z (θ : Algebra.DeRham.ExtAlg ℂ _) y ∈
      ⋀[ℂ]^p (Module.Dual ℂ (Fin d → ℂ)) := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      rw [chartExtMap_mk]
      exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range ℂ p ⟨_, rfl⟩)
  | zero => simp
  | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  | smul c a ha =>
      rw [Submodule.coe_smul_of_tower, chartExtMap_complex_smul]
      exact Submodule.smul_mem _ _ ha

/-- The value at `y ∈ D` of `chartExtMap θ`, for `θ` of degree `p`, as an element of
`⋀^p_ℂ (ℂ^d)^*`. -/
def chartPointForm (p : ℕ) (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (y : ↥(chartSectionDomain X d U z)) : ⋀[ℂ]^p (Module.Dual ℂ (Fin d → ℂ)) :=
  ⟨chartExtMap X d U z (θ : Algebra.DeRham.ExtAlg ℂ _) y, chartExtMap_mem X d U z p θ y⟩

/-- **Factorization of chart evaluation.** Pairing `chartPointForm θ y` with `w₁ ∧ ⋯ ∧ w_p` by
Mathlib's `exteriorPower.pairingDual` gives upstream's chart evaluation of `θ` at `y` on
`(w₁, …, w_p)`. On a generator both sides are `a₀(e.symm y)` times a determinant, Mathlib's
`det (fⱼ (wᵢ))` and upstream's `det (Lᵢ (wⱼ))`, which agree by `Matrix.det_transpose`. -/
lemma pairingDual_chartPointForm (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (y : ↥(chartSectionDomain X d U z)) (w : Fin p → Fin d → ℂ) :
    exteriorPower.pairingDual ℂ (Fin d → ℂ) p (chartPointForm X d U z p θ y)
        (exteriorPower.ιMulti ℂ p w) =
      chartEvaluation X d U z p θ y.1 w := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      have h : chartPointForm X d U z p (Algebra.DeRham.mk ℂ _ p a₀ v) y =
          chartSection X d U z a₀ y.1 • exteriorPower.ιMulti ℂ p fun i =>
            ((chartSectionDifferential X d U z (v i) y.1 : (Fin d → ℂ) →L[ℂ] ℂ) :
              Module.Dual ℂ (Fin d → ℂ)) :=
        Subtype.ext (chartExtMap_mk X d U z p a₀ v y)
      rw [h, chartEvaluation_mk X d U z p a₀ v y.2, chartGeneratorEvaluation, map_smul,
        LinearMap.smul_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
        ContinuousAlternatingMap.smul_apply,
        ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, ← Matrix.det_transpose]
      rfl
  | zero =>
      have h : chartPointForm X d U z p 0 y = 0 := Subtype.ext (by simp [chartPointForm])
      simp [h]
  | add a b ha hb =>
      have h : chartPointForm X d U z p (a + b) y =
          chartPointForm X d U z p a y + chartPointForm X d U z p b y :=
        Subtype.ext (by simp [chartPointForm])
      rw [h, map_add, LinearMap.add_apply, ha, hb, chartEvaluation_add]
      rfl
  | smul c a ha =>
      have h : chartPointForm X d U z p (c • a) y = c • chartPointForm X d U z p a y :=
        Subtype.ext (by
          simp only [chartPointForm, Submodule.coe_smul_of_tower, chartExtMap_complex_smul])
      rw [h, map_smul, LinearMap.smul_apply, ha, chartEvaluation_smul]
      rfl

/-- The chart evaluation of `θ` at `y ∈ D` vanishes exactly when `chartPointForm θ y` does:
`exteriorPower.pairingDual` is bijective for `ℂ^d` and `⋀^p ℂ^d` is spanned by the `ιMulti`. -/
lemma chartPointForm_eq_zero_iff (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (y : ↥(chartSectionDomain X d U z)) :
    chartPointForm X d U z p θ y = 0 ↔ chartEvaluation X d U z p θ y.1 = 0 := by
  constructor
  · intro h
    refine ContinuousAlternatingMap.ext fun w => ?_
    rw [← pairingDual_chartPointForm, h, map_zero, LinearMap.zero_apply]
    rfl
  · intro h
    refine (exteriorPower.bijective_pairingDual ℂ (Fin d → ℂ) p).1 ?_
    rw [map_zero]
    refine exteriorPower.linearMap_ext ?_
    ext w
    simp [pairingDual_chartPointForm, h]

/-- **The kernel through the algebra map.** A form lies in upstream's `chartEvaluationKernel`
exactly when `chartExtMap` kills it at every point of every chart. -/
lemma mem_chartEvaluationKernel_iff_chartExtMap (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    θ ∈ chartEvaluationKernel X d U p ↔
      ∀ z y, chartExtMap X d U z (θ : Algebra.DeRham.ExtAlg ℂ _) y = 0 := by
  rw [mem_chartEvaluationKernel_iff]
  constructor
  · intro h z y
    exact congrArg Subtype.val ((chartPointForm_eq_zero_iff X d U z p θ y).2 (h z y.1 y.2))
  · intro h z y hy
    exact (chartPointForm_eq_zero_iff X d U z p θ ⟨y, hy⟩).1 (Subtype.ext (h z ⟨y, hy⟩))

end ChartPoint

/-- **Wedge descends** (rung `wedge-descends`). Upstream's `chartEvaluationKernel` is a two-sided
ideal for `formWedge`: if `θ` or `η` has vanishing chart evaluations, so does `θ ∧ η`. Both sides
are proved directly from multiplicativity of `chartExtMap`, with no appeal to graded
commutativity. Hence the wedge product descends to upstream's
`HolomorphicForm X d U p = Form ℂ 𝒪(U) p ⧸ chartEvaluationKernel X d U p`. -/
theorem wedgeDescends : WedgeDescends := by
  intro X d _ U p q θ η
  simp only [mem_chartEvaluationKernel_iff_chartExtMap]
  refine ⟨fun hθ z y => ?_, fun hη z y => ?_⟩
  · show chartExtMap X d U z ((θ : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) *
        (η : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U))) y = 0
    rw [map_mul, Pi.mul_apply, hθ z y, zero_mul]
  · show chartExtMap X d U z ((θ : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U)) *
        (η : Algebra.DeRham.ExtAlg ℂ (OpenHolomorphicFunctions X d U))) y = 0
    rw [map_mul, Pi.mul_apply, hη z y, mul_zero]

end HodgeLadder
