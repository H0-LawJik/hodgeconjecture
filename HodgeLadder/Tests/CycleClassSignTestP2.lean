module

public import HodgeLadder.Tests.ProjectivePlanePoint
public import HodgeLadder.Tests.CycleClassMultiplicativeP2
public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization
public import Other.AlgebraicGeometry.ComplexPoint.CoclassOrientation
public import Other.AlgebraicTopology.Singular.Sheaf.ChainStalk
meta import Lean

/-!
# A degree map on `H⁴(ℙ²; ℚ)` from the complex orientation

Rung `cycle-class-sign-test-p2` (kind test). The checked `planeLines_cup_eq_planeOrigin` gives
`[L₀] ∪ [L₁] = [pt]` on ℙ², exact, sign `+`. This file asks whether upstream's `[pt]` has the
literature's normalization: degree `1` against the complex orientation.

The degree is computed, from upstream's definitions only:

1. `H^{q+3}(ℙ²(ℂ) ∖ pt; ℚ) = 0` for every `q` (`subsingleton_H'_compl_planeOrigin`: the
   Mayer–Vietoris steps of `p2-point-class-nonzero`, in every degree), so forgetting the support
   `Z = {pt}` is bijective on `H⁴` (`forgetSupport_planeOrigin_bijective`, rung
   `forget-support-exact` in degrees 3 and 4).
2. A class of `H⁴_Z(ℙ²; ℚ)` goes to `H⁴(⊤, ⊤ ∖ Z; ℚ)` by upstream's transport
   (`rationalSupportAddEquivSupportedInjectiveHomology`, then
   `complexSupportInjectiveSectionCohomologyEquiv` at `⊤`), and to
   `H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}; ℚ)` along the identity of points (`planeOriginPairMap`).
3. It is evaluated on upstream's `complexLocalOrientation projectivePlane 2 pt`, through upstream's
   universal-coefficient equivalence `relativeCohomologyEquivDualHomology`.

`planeDegree` is the composite. Then `deg [pt] = 1` (`planeDegree_planeOrigin`), from upstream's
`cycleComponentSupportedInjectiveClass_point_normalization`,
`analyticComponentPointSupportedInjectiveCoclass_relative` and
`analyticPointLocalCoclass_apply_complexLocalOrientation`, with no input from the multiplicativity
proof; a guard at the end of the file checks that by import closure. With the checked identity,
`deg ([L₀] ∪ [L₁]) = 1` (`planeDegree_planeLines_cup`), and `[L₀] ∪ [L₁] ≠ −[pt]`
(`planeLines_cup_ne_neg_planeOrigin`). The value `1` is upstream's point normalization read as a
number: the steps taken here (the inverse of `forgetSupport`, identity pair maps) carry no sign.
The cup corollary reads the product through the checked identity and is not a second computation
of it.

The degree is an isomorphism `H⁴(ℙ²; ℚ) ≅ ℚ` (`planeDegree_bijective`). It agrees with evaluation on
any class of `H₄(ℙ²(ℂ); ℚ)` that restricts to the complex local orientation at the point
(`planeDegree_eq_eval_of_restrict`), which is how the literature defines the degree, `⟨α, [ℙ²]⟩`.
No such global class is constructed at the pin.

## Main definitions

* `HodgeLadder.Tests.planeDegree`, with `planeOriginForgetEquiv`, `planeOriginLocalize`,
  `planeOriginEvaluation`
* `HodgeLadder.Tests.pointToNeighborhoodSupportPairMap`, `planeOriginPairMap`,
  `planeOriginSupportInclusion`

## Main results

* `HodgeLadder.Tests.planeDegree_planeOrigin`: `deg [pt] = 1`.
* `HodgeLadder.Tests.planeDegree_planeLines_cup`: `deg ([L₀] ∪ [L₁]) = 1`.
* `HodgeLadder.Tests.planeLines_cup_ne_neg_planeOrigin`, `planeDegree_neg_planeOrigin`,
  `planeDegree_eq_one_iff`.
* `HodgeLadder.Tests.planeDegree_forgetSupport`, `planeDegree_bijective`,
  `planeDegree_eq_eval_of_restrict`: well-definedness, and agreement with `⟨−, [ℙ²]⟩`.
* `HodgeLadder.Tests.subsingleton_H'_compl_planeOrigin`, `forgetSupport_planeOrigin_bijective`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint Order
open AlgebraicTopology.Singular

namespace HodgeLadder.Tests

/-- The closed support `{[0 : 0 : 1]}` of the point class. -/
abbrev planeOriginSupport : Closeds (ComplexPoint projectivePlane) :=
  cycleComponentAnalyticClosedSupport projectivePlane planeOrigin

/-- `H^{q+3}(ℙ²(ℂ) ∖ [0 : 0 : 1]; ℚ) = 0` for every `q`. -/
theorem subsingleton_H'_compl_planeOrigin (q : ℕ) :
    Subsingleton (Sheaf.H' planeConst (q + 3) planeOriginSupport.compl) := by
  have hc : ∀ (U : Opens (ComplexPoint projectivePlane)) [ContractibleSpace U] (n : ℕ),
      Subsingleton (Sheaf.H' planeConst (n + 1) U) := fun U _ n =>
    contractibleOpen_subsingleton_H' projectivePlane U (n + 1) n.succ_pos
  -- `H^{q+1}` of the two half-spaces `Im v₀ > 0`, `Im v₀ < 0` (disjoint, each convex)
  have h1 : Subsingleton (Sheaf.H' planeConst (q + 1)
      (planeChartZeroOpen chartHalfPos isOpen_chartHalfPos ⊔
        planeChartZeroOpen chartHalfNeg isOpen_chartHalfNeg)) := by
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartHalfPos starConvex_chartHalfPos
      ⟨fun _ => Complex.I, by simp [chartHalfPos]⟩
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartHalfNeg starConvex_chartHalfNeg
      ⟨fun _ => -Complex.I, by simp [chartHalfNeg]⟩
    refine TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ q ?_ (hc _ q) (hc _ q)
    rw [planeChartZeroOpen_inf,
      planeChartZeroOpen_congr _ isOpen_empty chartHalfPos_inter_chartHalfNeg,
      planeChartZeroOpen_empty]
    exact TopCat.Sheaf.subsingleton_H'_bot planeConst q
  -- `H^{q+2}` of `ℂ^* × ℂ`, covered by the two slit pieces
  have h2 : Subsingleton (Sheaf.H' planeConst (q + 2) (planeChartOpen 0 ⊓ planeChartOpen 1)) := by
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartSlitPos starConvex_chartSlitPos
      ⟨fun _ => 1, by simp [chartSlitPos]⟩
    have := contractibleSpace_planeChartZeroOpen _ isOpen_chartSlitNeg starConvex_chartSlitNeg
      ⟨fun _ => -1, by simp [chartSlitNeg]⟩
    rw [planeChartOpen_zero_inf_one,
      planeChartZeroOpen_congr _ (isOpen_chartSlitPos.union isOpen_chartSlitNeg)
        chartSlitPos_union_chartSlitNeg.symm, ← planeChartZeroOpen_sup]
    refine TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ (q + 1) ?_ (hc _ (q + 1))
      (hc _ (q + 1))
    rw [planeChartZeroOpen_inf,
      planeChartZeroOpen_congr _ (isOpen_chartHalfPos.union isOpen_chartHalfNeg)
        chartSlitPos_inter_chartSlitNeg, ← planeChartZeroOpen_sup]
    exact h1
  -- `H^{q+3}` of the complement, covered by the two charts `x₀ ≠ 0`, `x₁ ≠ 0`
  have := contractibleSpace_planeChartOpen 0
  have := contractibleSpace_planeChartOpen 1
  rw [planeOrigin_support_compl]
  exact TopCat.Sheaf.subsingleton_H'_sup planeConst _ _ (q + 2) h2 (hc _ (q + 2)) (hc _ (q + 2))

/-- Forgetting the support `{[0 : 0 : 1]}` is bijective in degree four. -/
theorem forgetSupport_planeOrigin_bijective :
    Function.Bijective (forgetSupport ℚ projectivePlane planeOriginSupport (2 * 2)) :=
  ⟨forgetSupport_injective_of_subsingleton projectivePlane planeOriginSupport 3
      subsingleton_H'_three_compl_planeOrigin,
    forgetSupport_surjective_of_subsingleton projectivePlane planeOriginSupport 4
      (subsingleton_H'_compl_planeOrigin 1)⟩

/-- `H⁴_{pt}(ℙ²; ℚ) ≃ H⁴(ℙ²; ℚ)`, forgetting the support. -/
def planeOriginForgetEquiv :
    H_[planeOriginSupport]^(2 * 2)(projectivePlane; ℚ) ≃+ H^(2 * 2)(projectivePlane; ℚ) :=
  AddEquiv.ofBijective _ forgetSupport_planeOrigin_bijective

/-- The map of pairs `(M, M ∖ {y}) → (V, V ∖ S)` for `V = M` and `S ⊆ {y}`. -/
def pointToNeighborhoodSupportPairMap {M : Type} [TopologicalSpace M] (V S : Set M) (y : M)
    (hV : ∀ m, m ∈ V) (hS : S ⊆ {y}) :
    pointComplementPair y ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun m => ⟨m, hV m⟩, continuous_id.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun m => ⟨⟨m.1, hV m.1⟩, fun h => m.2 (hS h)⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩) rfl

/-- `(M, M ∖ {y}) → (V, V ∖ S) → (M, M ∖ {y})` is the identity. -/
theorem pointToNeighborhoodSupportPairMap_comp_toPoint {M : Type} [TopologicalSpace M]
    (V S : Set M) (y : M) (hV : ∀ m, m ∈ V) (hS : S ⊆ {y}) (hy : y ∈ S) :
    pointToNeighborhoodSupportPairMap V S y hV hS ≫ neighborhoodSupportToPointPairMap V S y hy =
      𝟙 _ := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- `(V, V ∖ S) → (M, M ∖ {y}) → (V, V ∖ S)` is the identity. -/
theorem toPoint_comp_pointToNeighborhoodSupportPairMap {M : Type} [TopologicalSpace M]
    (V S : Set M) (y : M) (hV : ∀ m, m ∈ V) (hS : S ⊆ {y}) (hy : y ∈ S) :
    neighborhoodSupportToPointPairMap V S y hy ≫ pointToNeighborhoodSupportPairMap V S y hV hS =
      𝟙 _ := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Pulling back to `(V, V ∖ S)` and then to `(M, M ∖ {y})` is the identity. -/
theorem relativeCohomologyMap_pointToNeighborhood_toPoint {M : Type} [TopologicalSpace M]
    (V S : Set M) (y : M) (hV : ∀ m, m ∈ V) (hS : S ⊆ {y}) (hy : y ∈ S) (n : ℕ)
    (c : RelativeCohomology ℚ (pointComplementPair y) n) :
    relativeCohomologyMap ℚ n (pointToNeighborhoodSupportPairMap V S y hV hS)
        (relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V S y hy) c) = c := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    pointToNeighborhoodSupportPairMap_comp_toPoint, relativeCohomologyMap_id, LinearMap.id_apply]

/-- Pulling back to `(M, M ∖ {y})` and then to `(V, V ∖ S)` is the identity. -/
theorem relativeCohomologyMap_toPoint_pointToNeighborhood {M : Type} [TopologicalSpace M]
    (V S : Set M) (y : M) (hV : ∀ m, m ∈ V) (hS : S ⊆ {y}) (hy : y ∈ S) (n : ℕ)
    (c : RelativeCohomology ℚ (neighborhoodSupportComplementPair V S) n) :
    relativeCohomologyMap ℚ n (neighborhoodSupportToPointPairMap V S y hy)
        (relativeCohomologyMap ℚ n (pointToNeighborhoodSupportPairMap V S y hV hS) c) = c := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    toPoint_comp_pointToNeighborhoodSupportPairMap, relativeCohomologyMap_id, LinearMap.id_apply]

/-- The map of pairs `(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}) → (⊤, ⊤ ∖ Z)` for `Z = {pt}`, the identity on
points. -/
abbrev planeOriginPairMap :
    pointComplementPair planeOriginPoint ⟶
      neighborhoodSupportComplementPair
        ((⊤ : Opens (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))
        (planeOriginSupport : Set (ComplexPoint projectivePlane)) :=
  pointToNeighborhoodSupportPairMap _ _ planeOriginPoint (fun _ => trivial)
    planeOrigin_support_eq_singleton.le

/-- A supported class read in the local cohomology `H⁴(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}; ℚ)`: upstream's
injective model, upstream's transport `complexSupportInjectiveSectionCohomologyEquiv` to
`H⁴(⊤, ⊤ ∖ Z; ℚ)`, then the pullback along `planeOriginPairMap`. -/
def planeOriginLocalize :
    H_[planeOriginSupport]^(2 * 2)(projectivePlane; ℚ) →+
      RelativeCohomology ℚ (pointComplementPair planeOriginPoint) (2 * 2) :=
  (relativeCohomologyMap ℚ (2 * 2) planeOriginPairMap).toAddMonoidHom.comp
    ((complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤
        (2 * 2)).toAddMonoidHom.comp
      (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport
        (2 * 2)).toAddMonoidHom)

/-- Evaluation of a local class on upstream's complex local orientation at `[0 : 0 : 1]`, through
upstream's universal-coefficient equivalence. -/
def planeOriginEvaluation :
    RelativeCohomology ℚ (pointComplementPair planeOriginPoint) (2 * 2) →ₗ[ℚ] ℚ :=
  (LinearMap.applyₗ (complexLocalOrientation projectivePlane 2 planeOriginPoint)).comp
    (relativeCohomologyEquivDualHomology ℚ (pointComplementPair planeOriginPoint)
      (2 * 2)).toLinearMap

/-- **The degree map** `H⁴(ℙ²; ℚ) → ℚ`: lift a class to `H⁴_{pt}(ℙ²; ℚ)` (forgetting the support
is bijective, `forgetSupport_planeOrigin_bijective`), read it in local cohomology at the point
(`planeOriginLocalize`) and evaluate it on the complex local orientation there
(`planeOriginEvaluation`). -/
def planeDegree : H^(2 * 2)(projectivePlane; ℚ) →+ ℚ :=
  planeOriginEvaluation.toAddMonoidHom.comp
    (planeOriginLocalize.comp planeOriginForgetEquiv.symm.toAddMonoidHom)

/-- **Well-definedness**: on a class with support at the point, the degree is the evaluation of
its local class on the orientation. -/
theorem planeDegree_forgetSupport (a : H_[planeOriginSupport]^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree (forgetSupport ℚ projectivePlane planeOriginSupport (2 * 2) a) =
      planeOriginEvaluation (planeOriginLocalize a) := by
  have h : planeOriginForgetEquiv.symm
      (forgetSupport ℚ projectivePlane planeOriginSupport (2 * 2) a) = a :=
    planeOriginForgetEquiv.symm_apply_apply a
  simp only [planeDegree, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

/-- **`deg [pt] = 1`**: the class of `[0 : 0 : 1]` has degree one against the complex
orientation. Computed from upstream's point-class normalization. -/
theorem planeDegree_planeOrigin :
    planeDegree (cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin) =
      1 := by
  rw [cycleComponentSheafClass_eq_forgetSupport, planeDegree_forgetSupport]
  have hy₀ : planeOriginPoint ∈ cycleComponentSupport projectivePlane planeOrigin :=
    show planeOriginPoint.underlying ∈ closure {planeOrigin} from subset_closure rfl
  obtain ⟨z, -⟩ := (range_cycleComponentMap projectivePlane planeOrigin).ge hy₀
  have h2 : complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤
      (2 * 2) (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport
        (2 * 2) (cycleComponentSupportedInjectiveClass projectivePlane planeOrigin
          coheight_planeOrigin)) =
      analyticComponentPointRelativeCoclass projectivePlane planeOrigin 2 z := by
    rw [cycleComponentSupportedInjectiveClass_point_normalization projectivePlane planeOrigin 2 z
      coheight_planeOrigin, AddEquiv.apply_symm_apply,
      analyticComponentPointSupportedInjectiveCoclass_relative]
  change planeOriginEvaluation (relativeCohomologyMap ℚ (2 * 2) planeOriginPairMap
    (complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤ (2 * 2)
      (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport (2 * 2)
        (cycleComponentSupportedInjectiveClass projectivePlane planeOrigin
          coheight_planeOrigin)))) = 1
  rw [h2]
  have hz : cycleComponentMap projectivePlane planeOrigin z ∈
      (planeOriginSupport : Set (ComplexPoint projectivePlane)) :=
    range_cycleComponentMap_subset projectivePlane planeOrigin ⟨z, rfl⟩
  change planeOriginEvaluation (relativeCohomologyMap ℚ (2 * 2) planeOriginPairMap
    (relativeCohomologyMap ℚ (2 * 2)
      (neighborhoodSupportToPointPairMap
        ((⊤ : Opens (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))
        (planeOriginSupport : Set (ComplexPoint projectivePlane))
        (cycleComponentMap projectivePlane planeOrigin z) hz)
      (analyticPointLocalCoclass projectivePlane 2
        (cycleComponentMap projectivePlane planeOrigin z)))) = 1
  generalize cycleComponentMap projectivePlane planeOrigin z = w at hz ⊢
  obtain rfl : w = planeOriginPoint := by
    have := hz; rw [planeOrigin_support_eq_singleton] at this; exact this
  have h3 := relativeCohomologyMap_pointToNeighborhood_toPoint
    ((⊤ : Opens (ComplexPoint projectivePlane)) : Set (ComplexPoint projectivePlane))
    (planeOriginSupport : Set (ComplexPoint projectivePlane)) planeOriginPoint (fun _ => trivial)
    planeOrigin_support_eq_singleton.le hz (2 * 2)
    (analyticPointLocalCoclass projectivePlane 2 planeOriginPoint)
  refine (congrArg planeOriginEvaluation h3).trans ?_
  exact analyticPointLocalCoclass_apply_complexLocalOrientation projectivePlane 2 planeOriginPoint

/-- **`deg ([L₀] ∪ [L₁]) = 1`**, as in the literature. -/
theorem planeDegree_planeLines_cup :
    planeDegree (HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring)) = 1 := by
  rw [planeLines_cup_eq_planeOrigin]
  exact planeDegree_planeOrigin

/-- The degree map is an isomorphism `H⁴(ℙ²; ℚ) ≅ ℚ`. -/
theorem planeDegree_bijective : Function.Bijective planeDegree := by
  have hy₀ : planeOriginPoint ∈ (planeOriginSupport : Set (ComplexPoint projectivePlane)) := by
    rw [planeOrigin_support_eq_singleton]; rfl
  have hg : Function.Bijective (relativeCohomologyMap ℚ (2 * 2) planeOriginPairMap) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨relativeCohomologyMap ℚ (2 * 2) (neighborhoodSupportToPointPairMap _ _ _ hy₀),
        relativeCohomologyMap_toPoint_pointToNeighborhood _ _ _ _ _ hy₀ _,
        relativeCohomologyMap_pointToNeighborhood_toPoint _ _ _ _ _ hy₀ _⟩
  have he : Function.Bijective planeOriginEvaluation := by
    refine ⟨?_, fun q => ⟨q • analyticPointLocalCoclass projectivePlane 2 planeOriginPoint, ?_⟩⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      apply (relativeCohomologyEquivDualHomology ℚ (pointComplementPair planeOriginPoint)
        (2 * 2)).injective
      rw [map_zero]
      refine LinearMap.ext fun h => ?_
      obtain ⟨r, rfl⟩ := (Submodule.span_singleton_eq_top_iff ℚ
        (complexLocalOrientation projectivePlane 2 planeOriginPoint)).mp
          (span_complexLocalOrientation_eq_top projectivePlane 2 planeOriginPoint) h
      rw [map_smul]
      change r • planeOriginEvaluation c = _
      rw [hc, smul_zero, LinearMap.zero_apply]
    · rw [map_smul]
      change q • analyticPointLocalCoclassDual projectivePlane 2 planeOriginPoint
        (complexLocalOrientation projectivePlane 2 planeOriginPoint) = q
      rw [analyticPointLocalCoclass_apply_complexLocalOrientation, smul_eq_mul, mul_one]
  simp only [planeDegree, planeOriginLocalize, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    LinearMap.toAddMonoidHom_coe]
  exact he.comp (hg.comp ((AddEquiv.bijective _).comp ((AddEquiv.bijective _).comp
    (AddEquiv.bijective _))))

/-! ### Consequences -/

/-- `H⁴(ℙ²; ℚ)` is a line and `[pt]` is its degree-one class: `deg α = 1` exactly when
`α = [pt]`. -/
theorem planeDegree_eq_one_iff (α : H^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree α = 1 ↔
      α = cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin := by
  constructor
  · intro h
    exact planeDegree_bijective.1 (h.trans planeDegree_planeOrigin.symm)
  · rintro rfl
    exact planeDegree_planeOrigin

/-- `deg (−[pt]) = −1`: the degree separates the point class from its negative. -/
theorem planeDegree_neg_planeOrigin :
    planeDegree (-cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin) =
      -1 := by
  rw [map_neg, planeDegree_planeOrigin]

/-- `[L₀] ∪ [L₁] ≠ −[pt]`, read off the degree (`1` against `−1`). It also follows from
`planeLines_cup_eq_planeOrigin` and `projectivePlane_point_class_ne_zero` alone, since `[pt] ≠ 0` in
a ℚ-vector space; it adds nothing beyond `deg [pt] = 1`. -/
theorem planeLines_cup_ne_neg_planeOrigin :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0))
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1))
        (2 * (1 + 1)) (by ring) ≠
      -cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin := by
  intro h
  have h1 : planeDegree
      (-cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin) = 1 :=
    h ▸ planeDegree_planeLines_cup
  rw [planeDegree_neg_planeOrigin] at h1
  norm_num at h1

/-! ### Agreement with evaluation on a fundamental class -/

/-- Every open of `ℙ²(ℂ)` is paracompact (upstream's `openParacompactSpace`), for upstream's
sheaf–singular comparison `rationalCohomologyAddEquivSingularCohomology`. -/
local instance : ∀ V : Opens (ComplexPoint projectivePlane), ParacompactSpace V :=
  openParacompactSpace projectivePlane

/-- The map of pairs `(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt}) → (ℙ²(ℂ), ℙ²(ℂ) ∖ Z)` for `Z = {pt}`, the identity
of ℙ²(ℂ) (upstream's `supportInclusionPairMap`). -/
abbrev planeOriginSupportInclusion :
    pointComplementPair planeOriginPoint ⟶
      TopPair.ofSubset (X := TopCat.of (ComplexPoint projectivePlane))
        (planeOriginSupport.compl : Set (ComplexPoint projectivePlane)) :=
  supportInclusionPairMap (TopCat.of (ComplexPoint projectivePlane))
    planeOrigin_support_eq_singleton.le

/-- `planeOriginPairMap` is `planeOriginSupportInclusion` followed by the ladder's
`ofSubsetIsoNeighborhoodTop`; all three are the identity on points. -/
theorem planeOriginPairMap_eq_comp :
    planeOriginPairMap =
      planeOriginSupportInclusion ≫
        (HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop planeOriginSupport).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- An absolute class read in `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ {pt})` and pushed to `H₄(ℙ²(ℂ), ℙ²(ℂ) ∖ Z)` is
the class read there directly (upstream's `relativeChainProjection_supportInclusion`). -/
theorem relativeHomologyMap_planeOriginSupportInclusion_projection
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2)) :
    relativeHomologyMap ℚ (2 * 2) planeOriginSupportInclusion
        ((relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ) =
      (relativeHomologyProjection ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint projectivePlane))
          (planeOriginSupport.compl : Set (ComplexPoint projectivePlane))) (2 * 2)).hom μ := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f (2 * 2))
    (relativeChainProjection_supportInclusion ℚ (TopCat.of (ComplexPoint projectivePlane))
      planeOrigin_support_eq_singleton.le)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h μ

/-- If `μ` restricts to the complex local orientation at the point, the orientation pushed to
`(⊤, ⊤ ∖ Z)` is the image of `μ` there. -/
theorem relativeHomologyMap_planeOriginPairMap_orientation
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint) :
    relativeHomologyMap ℚ (2 * 2) planeOriginPairMap
        (complexLocalOrientation projectivePlane 2 planeOriginPoint) =
      relativeHomologyMap ℚ (2 * 2)
        (HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop planeOriginSupport).hom
        ((relativeHomologyProjection ℚ
          (TopPair.ofSubset (X := TopCat.of (ComplexPoint projectivePlane))
            (planeOriginSupport.compl : Set (ComplexPoint projectivePlane))) (2 * 2)).hom μ) := by
  rw [← hμ, planeOriginPairMap_eq_comp,
    ← relativeHomologyMap_planeOriginSupportInclusion_projection]
  simp only [relativeHomologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Agreement with `⟨−, [ℙ²]⟩`**: if a class `μ ∈ H₄(ℙ²(ℂ); ℚ)` restricts to the complex
local orientation at `[0 : 0 : 1]`, then `deg α` is the evaluation of `Ψ α` on `μ`, with `Ψ`
upstream's `rationalCohomologyAddEquivSingularCohomology`. A fundamental class of ℙ²(ℂ) for the
complex orientation is such a `μ`; none is constructed at the pin, so the hypothesis is not
discharged here. -/
theorem planeDegree_eq_eval_of_restrict
    (μ : Homology ℚ (TopCat.of (ComplexPoint projectivePlane)) (2 * 2))
    (hμ : (relativeHomologyProjection ℚ (pointComplementPair planeOriginPoint) (2 * 2)).hom μ =
      complexLocalOrientation projectivePlane 2 planeOriginPoint)
    (α : H^(2 * 2)(projectivePlane; ℚ)) :
    planeDegree α = cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint projectivePlane))
      (2 * 2) (rationalCohomologyAddEquivSingularCohomology projectivePlane (2 * 2) α) μ := by
  obtain ⟨a, rfl⟩ := forgetSupport_planeOrigin_bijective.2 α
  rw [planeDegree_forgetSupport, ← HodgeLadder.Cup.forgetRel_supportedEquivPair,
    HodgeLadder.Cup.supportedEquivPair_eq_transport]
  have hf : ∀ x, ConcreteCategory.hom (HodgeLadder.Cup.forgetRel
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint projectivePlane))
        (planeOriginSupport.compl : Set (ComplexPoint projectivePlane))) (2 * 2)) x =
      AlgebraicTopology.Singular.forgetSupport ℚ (TopCat.of (ComplexPoint projectivePlane))
        (planeOriginSupport : Set (ComplexPoint projectivePlane)) (2 * 2) x :=
    fun _ => rfl
  rw [hf]
  have h1 := cohomologyEquivDualHomology_forgetSupport ℚ (TopCat.of (ComplexPoint projectivePlane))
    (planeOriginSupport : Set (ComplexPoint projectivePlane)) (2 * 2)
    (relativeCohomologyMap ℚ (2 * 2)
      (HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop planeOriginSupport).hom
      (complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤ (2 * 2)
        (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport
          (2 * 2) a))) μ
  refine Eq.trans ?_ h1.symm
  have h2 := relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ (2 * 2)
    (HodgeLadder.Cup.ofSubsetIsoNeighborhoodTop planeOriginSupport).hom
    (complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤ (2 * 2)
        (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport
          (2 * 2) a))
    ((relativeHomologyProjection ℚ
          (TopPair.ofSubset (X := TopCat.of (ComplexPoint projectivePlane))
            (planeOriginSupport.compl : Set (ComplexPoint projectivePlane))) (2 * 2)).hom μ)
  refine Eq.trans ?_ h2.symm
  have h3 := relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ (2 * 2)
    planeOriginPairMap
    (complexSupportInjectiveSectionCohomologyEquiv projectivePlane planeOriginSupport ⊤ (2 * 2)
        (rationalSupportAddEquivSupportedInjectiveHomology projectivePlane planeOriginSupport
          (2 * 2) a))
    (complexLocalOrientation projectivePlane 2 planeOriginPoint)
  exact h3.trans (congrArg _ (relativeHomologyMap_planeOriginPairMap_orientation μ hμ))

end HodgeLadder.Tests

-- Independence guard: the degree map and `deg [pt] = 1` do not use the multiplicativity proof.
-- The module imports it (for `planeDegree_planeLines_cup`, the positive control). Bodies of
-- imported theorems are not visible under the module system, so the guard walks the constants of
-- this file (types and values) and judges every imported constant by its module: it fails if that
-- module is forbidden or imports a forbidden module, directly or transitively. This is sound,
-- since a proof in a module uses only constants of the module and its imports. A docstring cannot
-- precede `run_cmd`.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let forbidden : List Name :=
    [`HodgeLadder.Cycle.Multiplicative, `HodgeLadder.Tests.CycleClassMultiplicativeP2,
     `HodgeLadder.Local.ClassProduct, `HodgeLadder.Normalization.Germ]
  for m in forbidden do
    unless (env.getModuleIdx? m).isSome do
      throwError "independence guard is stale: {m} is not imported"
  -- modules whose import closure meets a forbidden module (`moduleNames` is in import order)
  let mut tainted : NameSet := {}
  for i in [0:names.size] do
    let m := names[i]!
    if forbidden.contains m ||
        env.header.moduleData[i]!.imports.any (fun im => tainted.contains im.module) then
      tainted := tainted.insert m
  let check (roots : List Name) : CommandElabM (Option (Name × Name)) := do
    let mut todo := roots
    let mut visited : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail
      if visited.contains n then continue
      visited := visited.insert n
      if let some i := env.getModuleIdxFor? n then
        let m := names[i.toNat]!
        if tainted.contains m then return some (n, m)
        continue
      match env.find? n with
      | some ci =>
        todo := (ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList ++ todo
      | none => throwError "independence guard: {n} not found"
    return none
  -- positive control: the cup corollary goes through the multiplicativity proof
  if (← check [`HodgeLadder.Tests.planeDegree_planeLines_cup]).isNone then
    throwError "independence guard is blind: planeDegree_planeLines_cup shows no forbidden use"
  if let some (n, m) ← check [`HodgeLadder.Tests.planeDegree,
      `HodgeLadder.Tests.planeDegree_planeOrigin, `HodgeLadder.Tests.planeDegree_bijective,
      `HodgeLadder.Tests.planeDegree_forgetSupport] then
    throwError "the degree uses {n}, from {m}, which is or imports the multiplicativity proof"
