module

public import HodgeLadder.Tests.P1p1Witness
public import HodgeLadder.Tests.ProjectiveLinePoint
public import HodgeLadder.Tests.ProjectiveChart
public import HodgeLadder.Normalization.ProductChart
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# Two fibres of ℙ¹ × ℙ¹ meeting transversally in a point

Rung `p1p1-fibres-transversal`: on `p1p1 = projectiveLine ⨯ projectiveLine`, the inputs of
`cycle-class-multiplicative` for the fibres `{∞} × ℙ¹`, `ℙ¹ × {∞}` and the point `(∞, ∞)`,
in the exact form of the hypotheses `hx`, `hw`, `ht`, `hT`, `htr` at `a = b = 1`, `d = 2`.
Here `∞ = [1 : 0]` is `infty` of rung `projective-line-point`.

The fibres are images of generic points under sections of the projections: with
`constInfty : ℙ¹ ⟶ ℙ¹` the constant map at `∞` (through `Spec ℂ`),

* `p1p1FibreFst` is the image of the generic point of ℙ¹ under `prod.lift constInfty (𝟙 _)`,
  the fibre of the first projection over `∞`;
* `p1p1FibreSnd` is its image under `prod.lift (𝟙 _) constInfty`, the fibre of the second
  projection over `∞`;
* `p1p1Corner` is the underlying point of `p1p1CornerPoint = prod.lift ∞ ∞`.

The chart is `prodChart` of the standard chart `x₀ ≠ 0` of ℙ¹ (`projectiveChart 1 0`, coordinate
`x₁ / x₀`, which vanishes exactly at `∞`) with itself, first factor first; it lies in the maximal
analytic atlas by `prodChart_mem_maximalAtlas` and `projectiveChart_mem_maximalAtlas`. Coordinate
`0` cuts out `{∞} × ℙ¹` and coordinate `1` cuts out `ℙ¹ × {∞}` (conventions row "Complex points of
a product and product charts").

Route. A complex point `z` with first projection `∞` is the image of its second projection under
the section, so its underlying point specializes from `p1p1FibreFst`; conversely the closure of
`p1p1FibreFst` maps to the closed point `∞` under the first projection. Coheights:
`p1p1Corner < p1p1FibreFst < ⊤` and upstream's bound `coheight ≤ 2` on a smooth surface. Smooth
locus: each section is a closed immersion (a section of a separated projection), its source ℙ¹ is
reduced, so its kernel is the vanishing ideal of the closure of the fibre and the reduced closure
`cycleComponentι` is ℙ¹ through Mathlib's `Scheme.Hom.toImage`; it is smooth over `ℂ` at every
point. No ring of an affine open of `p1p1` is computed.

## Main definitions

* `HodgeLadder.Tests.lineChart`, `inftyPoint`, `constInfty`, `fibreSectionFst`, `fibreSectionSnd`
* `HodgeLadder.Tests.p1p1FibreFst`, `p1p1FibreSnd`, `p1p1CornerPoint`, `p1p1Corner`,
  `p1p1Chart`

## Main results

* `HodgeLadder.Tests.coheight_p1p1FibreFst`, `coheight_p1p1FibreSnd`, `coheight_p1p1Corner_add`
  (`hx`, `hw`, `ht`), with `coheight_p1p1Corner`
* `HodgeLadder.Tests.p1p1Corner_support_eq_inter` (`hT`), `p1p1Corner_support_eq_singleton`
* `HodgeLadder.Tests.mem_p1p1FibreFst_support_iff`, `mem_p1p1FibreSnd_support_iff`: in the product
  chart the fibres are the coordinate hyperplanes `{v₀ = 0}` and `{v₁ = 0}`
* `HodgeLadder.Tests.p1p1Chart_mem_maximalAtlas`, `p1p1Fibres_transversal` (`htr`)
* `HodgeLadder.Tests.p1p1Corner_support_subset_smoothSupportAmbientOpen_fst`, `_snd` (`hxreg`,
  `hwreg`), from `smooth_cycleComponentι_p1p1FibreFst`, `smooth_cycleComponentι_p1p1FibreSnd`
* General: `ker_eq_vanishingIdeal_of_isReduced`, `smooth_cycleComponentι_of_closedImmersion`
* Non-vacuity: `p1p1FibreFst_ne_p1p1FibreSnd`, `p1p1Chart_p1p1CornerPoint`,
  `not_forall_mem_p1p1FibreFst_iff_coord_one` (the swapped coordinate order fails)

With these, `cycleComponentSheafClass_cup_of_transversal p1p1 (d := 2)` and its `_noReg` form
apply term by term (rung `cycle-class-multiplicative-p1p1`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLadder.Tests

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLadder.Normalization
open HodgeLadder.ComplexPointProd

/-! ### The point `∞` of ℙ¹ and its chart -/

/-- The standard chart `x₀ ≠ 0` of upstream's ℙ¹(ℂ), coordinate `x₁ / x₀`
(`projectiveChart 1 0`). -/
def lineChart : OpenPartialHomeomorph (ComplexPoint projectiveLine) (Fin 1 → ℂ) :=
  projectiveChart 1 0

/-- The chart `x₀ ≠ 0` of ℙ¹(ℂ) lies in the maximal analytic atlas. -/
theorem lineChart_mem_maximalAtlas :
    lineChart ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 1 → ℂ) ω (ComplexPoint projectiveLine) :=
  projectiveChart_mem_maximalAtlas 1 0

/-- The complex point `∞ = [1 : 0]` of ℙ¹: the inverse of the chart `x₀ ≠ 0` at the origin. -/
def inftyPoint : ComplexPoint projectiveLine := lineChart.symm 0

/-- The underlying point of the inverse chart at `v`, in Oka's terms. -/
theorem lineChart_symm_underlying (v : Fin 1 → ℂ) :
    (lineChart.symm v).underlying =
      okaIso.hom.base ((AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin 2)).base
        (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v)) :=
  projectiveChart_symm_underlying 1 0 v

/-- The underlying point of `inftyPoint` is the scheme point `infty`. -/
theorem inftyPoint_underlying : inftyPoint.underlying = infty := by
  rw [inftyPoint, lineChart_symm_underlying, infty, okaInfty, dehomogenizeVec_infty]

/-- The inverse chart is injective on underlying points. -/
theorem lineChart_symm_underlying_injective {u v : Fin 1 → ℂ}
    (h : (lineChart.symm u).underlying = (lineChart.symm v).underlying) : u = v := by
  rw [lineChart_symm_underlying, lineChart_symm_underlying] at h
  exact AlgebraicGeometry.ProjectiveSpace.evalPoint_injective (RingHom.id ℂ)
    Function.surjective_id ((AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin 2)
      ).isOpenEmbedding.injective (okaIso.hom.isOpenEmbedding.injective h))

/-- A complex point of ℙ¹ over `infty` lies in the source of the chart `x₀ ≠ 0`. -/
theorem mem_lineChart_source_of_underlying (b : ComplexPoint projectiveLine)
    (hb : b.underlying = infty) : b ∈ lineChart.source := by
  have h : b.underlying ∈ projectiveChartOpen 1 0 := by
    rw [hb]
    exact ⟨_, rfl⟩
  rw [lineChart, projectiveChart, affineChart_source]
  exact ⟨(openEquiv _ _).symm ⟨b, h⟩,
    congrArg Subtype.val ((openEquiv _ _).apply_symm_apply _)⟩

/-- `inftyPoint` lies in the source of the chart. -/
theorem inftyPoint_mem_source : inftyPoint ∈ lineChart.source :=
  mem_lineChart_source_of_underlying _ inftyPoint_underlying

/-- In the chart `x₀ ≠ 0`, a complex point lies over `∞` exactly when its coordinate vanishes. -/
theorem underlying_eq_infty_iff (b : ComplexPoint projectiveLine) (hb : b ∈ lineChart.source) :
    b.underlying = infty ↔ lineChart b 0 = 0 := by
  have hb' : lineChart.symm (lineChart b) = b := lineChart.left_inv hb
  constructor
  · intro h
    have : lineChart b = 0 := by
      apply lineChart_symm_underlying_injective
      rw [hb', h, ← inftyPoint_underlying, inftyPoint]
    rw [this]; rfl
  · intro h
    have : lineChart b = 0 := funext fun i => by fin_cases i; exact h
    rw [← hb', this, ← inftyPoint, inftyPoint_underlying]

/-- A complex point of ℙ¹ over `infty` is `inftyPoint`. -/
theorem eq_inftyPoint_of_underlying (b : ComplexPoint projectiveLine)
    (hb : b.underlying = infty) : b = inftyPoint := by
  have hs := mem_lineChart_source_of_underlying b hb
  have h0 := (underlying_eq_infty_iff b hs).mp hb
  have : lineChart b = 0 := funext fun i => by fin_cases i; exact h0
  rw [← lineChart.left_inv hs, this]
  rfl

/-! ### Sections of the projections -/

/-- The constant map `ℙ¹ ⟶ ℙ¹` at `∞`, through `Spec ℂ`. -/
def constInfty : projectiveLine ⟶ projectiveLine :=
  (Over.homMk projectiveLine.hom : projectiveLine ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ inftyPoint

/-- A complex point followed by the constant map at `∞` is `inftyPoint`. -/
theorem map_constInfty (b : ComplexPoint projectiveLine) :
    Point.map constInfty b = inftyPoint := by
  have h : b ≫ (Over.homMk projectiveLine.hom : projectiveLine ⟶ Over.mk (𝟙 (Spec ↧ℂ))) =
      𝟙 _ := by
    ext1
    simpa using Over.w b
  change b ≫ _ ≫ inftyPoint = inftyPoint
  rw [← Category.assoc, h, Category.id_comp]

/-- The section `b ↦ (∞, b)` of the second projection; its image is `{∞} × ℙ¹`. -/
def fibreSectionFst : projectiveLine ⟶ p1p1 := prod.lift constInfty (𝟙 _)

/-- The section `a ↦ (a, ∞)` of the first projection; its image is `ℙ¹ × {∞}`. -/
def fibreSectionSnd : projectiveLine ⟶ p1p1 := prod.lift (𝟙 _) constInfty

/-- The fibre `{∞} × ℙ¹`, as the scheme point of its generic point. -/
def p1p1FibreFst : p1p1.left := fibreSectionFst.left (⊤ : projectiveLine.left)

/-- The fibre `ℙ¹ × {∞}`, as the scheme point of its generic point. -/
def p1p1FibreSnd : p1p1.left := fibreSectionSnd.left (⊤ : projectiveLine.left)

/-- The complex point `(∞, ∞)` of ℙ¹ × ℙ¹. -/
def p1p1CornerPoint : ComplexPoint p1p1 := prod.lift inftyPoint inftyPoint

/-- The scheme point `(∞, ∞)` of ℙ¹ × ℙ¹. -/
def p1p1Corner : p1p1.left := p1p1CornerPoint.underlying

/-- `infty` is not the generic point of ℙ¹. -/
theorem infty_ne_top : infty ≠ (⊤ : projectiveLine.left) := by
  intro h
  have h1 := coheight_infty
  rw [h, Order.coheight_top] at h1
  exact zero_ne_one h1

/-- A point of `Spec ℂ` is the closed point, so a complex point sends every point of `Spec ℂ` to
its underlying point. -/
theorem point_left_apply {X : Over (Spec ↧ℂ)} (b : ComplexPoint X) (p : Spec ↧ℂ) :
    b.left p = b.underlying := by
  obtain rfl := Subsingleton.elim (α := Spec ↧ℂ) p (IsLocalRing.closedPoint ℂ)
  rfl

/-- The section `b ↦ (∞, b)` on complex points. -/
theorem map_fibreSectionFst (b : ComplexPoint projectiveLine) :
    Point.map fibreSectionFst b = prod.lift inftyPoint b := by
  apply prod.hom_ext
  · rw [prod.lift_fst, ← map_constInfty b]
    change b ≫ prod.lift constInfty (𝟙 _) ≫ prod.fst = b ≫ constInfty
    rw [prod.lift_fst]
  · rw [prod.lift_snd]
    change b ≫ prod.lift constInfty (𝟙 _) ≫ prod.snd = b
    rw [prod.lift_snd, Category.comp_id]

/-- The section `a ↦ (a, ∞)` on complex points. -/
theorem map_fibreSectionSnd (a : ComplexPoint projectiveLine) :
    Point.map fibreSectionSnd a = prod.lift a inftyPoint := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
    change a ≫ prod.lift (𝟙 _) constInfty ≫ prod.fst = a
    rw [prod.lift_fst, Category.comp_id]
  · rw [prod.lift_snd, ← map_constInfty a]
    change a ≫ prod.lift (𝟙 _) constInfty ≫ prod.snd = a ≫ constInfty
    rw [prod.lift_snd]

/-- A complex point of ℙ¹ × ℙ¹ is the pair of its projections. -/
theorem eq_prodLift (z : ComplexPoint p1p1) :
    z = prod.lift (Point.map prod.fst z) (Point.map prod.snd z) :=
  prod.hom_ext (by rw [prod.lift_fst]; rfl) (by rw [prod.lift_snd]; rfl)

/-- The first projection of `p1p1FibreFst` is `∞`. -/
theorem fst_p1p1FibreFst :
    (prod.fst : p1p1 ⟶ projectiveLine).left p1p1FibreFst = infty := by
  have h : (fibreSectionFst ≫ prod.fst).left = constInfty.left := by
    rw [fibreSectionFst, prod.lift_fst]
  rw [p1p1FibreFst, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  change (projectiveLine.hom ≫ inftyPoint.left) _ = _
  rw [Scheme.Hom.comp_apply, point_left_apply, inftyPoint_underlying]

/-- The second projection of `p1p1FibreFst` is the generic point of ℙ¹. -/
theorem snd_p1p1FibreFst :
    (prod.snd : p1p1 ⟶ projectiveLine).left p1p1FibreFst = ⊤ := by
  have h : (fibreSectionFst ≫ prod.snd).left = 𝟙 _ := by
    rw [fibreSectionFst, prod.lift_snd]
    rfl
  rw [p1p1FibreFst, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rfl

/-- The first projection of `p1p1FibreSnd` is the generic point of ℙ¹. -/
theorem fst_p1p1FibreSnd :
    (prod.fst : p1p1 ⟶ projectiveLine).left p1p1FibreSnd = ⊤ := by
  have h : (fibreSectionSnd ≫ prod.fst).left = 𝟙 _ := by
    rw [fibreSectionSnd, prod.lift_fst]
    rfl
  rw [p1p1FibreSnd, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rfl

/-- The second projection of `p1p1FibreSnd` is `∞`. -/
theorem snd_p1p1FibreSnd :
    (prod.snd : p1p1 ⟶ projectiveLine).left p1p1FibreSnd = infty := by
  have h : (fibreSectionSnd ≫ prod.snd).left = constInfty.left := by
    rw [fibreSectionSnd, prod.lift_snd]
  rw [p1p1FibreSnd, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  change (projectiveLine.hom ≫ inftyPoint.left) _ = _
  rw [Scheme.Hom.comp_apply, point_left_apply, inftyPoint_underlying]

/-- A point specializing from a point over `∞` lies over `∞`: the closed point `∞` of ℙ¹. -/
theorem eq_infty_of_specializes {a b : projectiveLine.left} (h : a ⤳ b) (ha : a = infty) :
    b = infty := by
  have : b ∈ closure ({infty} : Set projectiveLine.left) :=
    specializes_iff_mem_closure.mp (ha ▸ h)
  rwa [closure_infty] at this

/-! ### Supports -/

/-- A complex point lies on `{∞} × ℙ¹` exactly when its first projection lies over `∞`. -/
theorem mem_p1p1FibreFst_support_iff_fst (z : ComplexPoint p1p1) :
    z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ↔
      (Point.map prod.fst z).underlying = infty := by
  change z.underlying ∈ closure {p1p1FibreFst} ↔ _
  rw [← specializes_iff_mem_closure, Point.underlying_map]
  constructor
  · intro h
    exact eq_infty_of_specializes (h.map (prod.fst : p1p1 ⟶ projectiveLine).left.continuous)
      fst_p1p1FibreFst
  · intro h
    have h1 := eq_inftyPoint_of_underlying (Point.map prod.fst z) h
    have hz : z = Point.map fibreSectionFst (Point.map prod.snd z) := by
      rw [map_fibreSectionFst, ← h1]
      exact eq_prodLift z
    rw [hz, Point.underlying_map]
    exact ((Scheme.le_iff_specializes).mp le_top).map fibreSectionFst.left.continuous

/-- A complex point lies on `ℙ¹ × {∞}` exactly when its second projection lies over `∞`. -/
theorem mem_p1p1FibreSnd_support_iff_snd (z : ComplexPoint p1p1) :
    z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd ↔
      (Point.map prod.snd z).underlying = infty := by
  change z.underlying ∈ closure {p1p1FibreSnd} ↔ _
  rw [← specializes_iff_mem_closure, Point.underlying_map]
  constructor
  · intro h
    exact eq_infty_of_specializes (h.map (prod.snd : p1p1 ⟶ projectiveLine).left.continuous)
      snd_p1p1FibreSnd
  · intro h
    have h1 := eq_inftyPoint_of_underlying (Point.map prod.snd z) h
    have hz : z = Point.map fibreSectionSnd (Point.map prod.fst z) := by
      rw [map_fibreSectionSnd, ← h1]
      exact eq_prodLift z
    rw [hz, Point.underlying_map]
    exact ((Scheme.le_iff_specializes).mp le_top).map fibreSectionSnd.left.continuous

/-- The projections of `(∞, ∞)`. -/
theorem map_fst_p1p1CornerPoint : Point.map prod.fst p1p1CornerPoint = inftyPoint :=
  prod.lift_fst _ _

/-- The projections of `(∞, ∞)`. -/
theorem map_snd_p1p1CornerPoint : Point.map prod.snd p1p1CornerPoint = inftyPoint :=
  prod.lift_snd _ _

/-- `(∞, ∞)` lies on `{∞} × ℙ¹`. -/
theorem p1p1CornerPoint_mem_fst :
    p1p1CornerPoint ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst := by
  rw [mem_p1p1FibreFst_support_iff_fst, map_fst_p1p1CornerPoint, inftyPoint_underlying]

/-- `(∞, ∞)` lies on `ℙ¹ × {∞}`. -/
theorem p1p1CornerPoint_mem_snd :
    p1p1CornerPoint ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd := by
  rw [mem_p1p1FibreSnd_support_iff_snd, map_snd_p1p1CornerPoint, inftyPoint_underlying]

/-! ### Specialization order and coheights: hypotheses `hx`, `hw`, `ht` -/

/-- `(∞, ∞)` is a proper specialization of `{∞} × ℙ¹`. -/
theorem p1p1Corner_lt_p1p1FibreFst : p1p1Corner < p1p1FibreFst := by
  refine lt_of_le_not_ge ?_ ?_
  · rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
    exact p1p1CornerPoint_mem_fst
  · rw [Scheme.le_iff_specializes]
    intro h
    have h' := h.map (prod.snd : p1p1 ⟶ projectiveLine).left.continuous
    rw [snd_p1p1FibreFst] at h'
    have hc : (prod.snd : p1p1 ⟶ projectiveLine).left p1p1Corner = infty := by
      rw [p1p1Corner, ← Point.underlying_map, map_snd_p1p1CornerPoint, inftyPoint_underlying]
    exact infty_ne_top (eq_infty_of_specializes h' hc).symm

/-- `(∞, ∞)` is a proper specialization of `ℙ¹ × {∞}`. -/
theorem p1p1Corner_lt_p1p1FibreSnd : p1p1Corner < p1p1FibreSnd := by
  refine lt_of_le_not_ge ?_ ?_
  · rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
    exact p1p1CornerPoint_mem_snd
  · rw [Scheme.le_iff_specializes]
    intro h
    have h' := h.map (prod.fst : p1p1 ⟶ projectiveLine).left.continuous
    rw [fst_p1p1FibreSnd] at h'
    have hc : (prod.fst : p1p1 ⟶ projectiveLine).left p1p1Corner = infty := by
      rw [p1p1Corner, ← Point.underlying_map, map_fst_p1p1CornerPoint, inftyPoint_underlying]
    exact infty_ne_top (eq_infty_of_specializes h' hc).symm

/-- `{∞} × ℙ¹` is not the generic point of ℙ¹ × ℙ¹. -/
theorem p1p1FibreFst_lt_top : p1p1FibreFst < ⊤ := by
  refine lt_of_le_not_ge le_top fun h => ?_
  rw [Scheme.le_iff_specializes] at h
  have h1 := eq_infty_of_specializes (h.map (prod.fst : p1p1 ⟶ projectiveLine).left.continuous)
    fst_p1p1FibreFst
  have h2 := ((Scheme.le_iff_specializes).mp (le_top : p1p1FibreSnd ≤ ⊤)).map
    (prod.fst : p1p1 ⟶ projectiveLine).left.continuous
  rw [fst_p1p1FibreSnd] at h2
  exact infty_ne_top (eq_infty_of_specializes h2 h1).symm

/-- `ℙ¹ × {∞}` is not the generic point of ℙ¹ × ℙ¹. -/
theorem p1p1FibreSnd_lt_top : p1p1FibreSnd < ⊤ := by
  refine lt_of_le_not_ge le_top fun h => ?_
  rw [Scheme.le_iff_specializes] at h
  have h1 := eq_infty_of_specializes (h.map (prod.snd : p1p1 ⟶ projectiveLine).left.continuous)
    snd_p1p1FibreSnd
  have h2 := ((Scheme.le_iff_specializes).mp (le_top : p1p1FibreFst ≤ ⊤)).map
    (prod.snd : p1p1 ⟶ projectiveLine).left.continuous
  rw [snd_p1p1FibreFst] at h2
  exact infty_ne_top (eq_infty_of_specializes h2 h1).symm

/-- The coheight of a point strictly between `(∞, ∞)` and the generic point is one. -/
theorem coheight_eq_one_of_between {y : p1p1.left} (h1 : y < ⊤) (h2 : p1p1Corner < y) :
    Order.coheight y = (1 : ℕ) := by
  have h3 := Order.coheight_add_one_le h1
  have h4 := Order.coheight_add_one_le h2
  have h5 : Order.coheight p1p1Corner ≤ (2 : ℕ) :=
    SmoothOfRelativeDimension.coheight_le_complex (f := p1p1.hom) (d := 2) p1p1Corner
  rw [Order.coheight_top, zero_add] at h3
  have h6 := h4.trans h5
  generalize Order.coheight y = c at h3 h6 ⊢
  induction c using ENat.recTopCoe with
  | top => simp at h6
  | coe n =>
    norm_cast at h3 h6 ⊢
    omega

/-- `{∞} × ℙ¹` has coheight one: hypothesis `hx`. -/
theorem coheight_p1p1FibreFst : Order.coheight p1p1FibreFst = (1 : ℕ) :=
  coheight_eq_one_of_between p1p1FibreFst_lt_top p1p1Corner_lt_p1p1FibreFst

/-- `ℙ¹ × {∞}` has coheight one: hypothesis `hw`. -/
theorem coheight_p1p1FibreSnd : Order.coheight p1p1FibreSnd = (1 : ℕ) :=
  coheight_eq_one_of_between p1p1FibreSnd_lt_top p1p1Corner_lt_p1p1FibreSnd

/-- `(∞, ∞)` has coheight two. -/
theorem coheight_p1p1Corner : Order.coheight p1p1Corner = (2 : ℕ) := by
  have h2 := Order.coheight_add_one_le p1p1Corner_lt_p1p1FibreFst
  have h3 : Order.coheight p1p1Corner ≤ (2 : ℕ) :=
    SmoothOfRelativeDimension.coheight_le_complex (f := p1p1.hom) (d := 2) p1p1Corner
  rw [coheight_p1p1FibreFst] at h2
  refine le_antisymm h3 ?_
  have h22 : ((2 : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + 1 := by norm_num
  rw [h22]
  exact h2

/-- The coheight of `(∞, ∞)` in the form `↑a + ↑b` with `a = b = 1`: hypothesis `ht`. -/
theorem coheight_p1p1Corner_add :
    Order.coheight p1p1Corner = ((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) := by
  rw [coheight_p1p1Corner]; rfl

/-! ### The intersection: hypothesis `hT` -/

/-- `({∞} × ℙ¹)(ℂ) ∩ (ℙ¹ × {∞})(ℂ)` is the single complex point `(∞, ∞)`. -/
theorem mem_p1p1Fibres_inter_iff (z : ComplexPoint p1p1) :
    (z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ∧
      z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd) ↔ z = p1p1CornerPoint := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [mem_p1p1FibreFst_support_iff_fst] at h1
    rw [mem_p1p1FibreSnd_support_iff_snd] at h2
    rw [eq_prodLift z, eq_inftyPoint_of_underlying _ h1, eq_inftyPoint_of_underlying _ h2]
    rfl
  · rintro rfl
    exact ⟨p1p1CornerPoint_mem_fst, p1p1CornerPoint_mem_snd⟩

/-- The support of `(∞, ∞)` is the intersection of the supports of the fibres: hypothesis `hT`
of `cycle-class-multiplicative`. -/
theorem p1p1Corner_support_eq_inter :
    (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set (ComplexPoint p1p1)) =
      (cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst : Set (ComplexPoint p1p1)) ∩
        cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd := by
  ext y
  refine ⟨fun hy => ⟨?_, ?_⟩, fun hy => ?_⟩
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp p1p1Corner_lt_p1p1FibreFst.le) hy
  · exact specializes_iff_closure_subset.mp
      ((Scheme.le_iff_specializes).mp p1p1Corner_lt_p1p1FibreSnd.le) hy
  · rw [(mem_p1p1Fibres_inter_iff y).mp hy]
    exact subset_closure rfl

/-- The support of `(∞, ∞)` is the single complex point `(∞, ∞)`. -/
theorem p1p1Corner_support_eq_singleton :
    (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set (ComplexPoint p1p1)) =
      {p1p1CornerPoint} := by
  rw [p1p1Corner_support_eq_inter]
  ext y
  exact mem_p1p1Fibres_inter_iff y

/-! ### The product chart: hypothesis `htr` -/

/-- The product of the chart `x₀ ≠ 0` of ℙ¹ with itself, first factor first: coordinates
`(x₁ / x₀ ∘ pr₁, x₁ / x₀ ∘ pr₂)`. -/
def p1p1Chart : OpenPartialHomeomorph (ComplexPoint p1p1) (Fin 2 → ℂ) :=
  prodChart projectiveLine projectiveLine lineChart lineChart

/-- The product chart lies in the maximal analytic atlas of `(ℙ¹ × ℙ¹)(ℂ)`. -/
theorem p1p1Chart_mem_maximalAtlas :
    p1p1Chart ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint p1p1) :=
  prodChart_mem_maximalAtlas lineChart_mem_maximalAtlas lineChart_mem_maximalAtlas

/-- Coordinate `0` of the product chart is the chart of the first projection. -/
theorem p1p1Chart_apply_zero (z : ComplexPoint p1p1) :
    p1p1Chart z 0 = lineChart (Point.map prod.fst z) 0 := by
  rw [p1p1Chart, prodChart_apply]
  rfl

/-- Coordinate `1` of the product chart is the chart of the second projection. -/
theorem p1p1Chart_apply_one (z : ComplexPoint p1p1) :
    p1p1Chart z 1 = lineChart (Point.map prod.snd z) 0 := by
  rw [p1p1Chart, prodChart_apply]
  rfl

/-- The source of the product chart. -/
theorem mem_p1p1Chart_source_iff (z : ComplexPoint p1p1) :
    z ∈ p1p1Chart.source ↔
      Point.map prod.fst z ∈ lineChart.source ∧ Point.map prod.snd z ∈ lineChart.source := by
  rw [p1p1Chart, prodChart_source]
  rfl

/-- `(∞, ∞)` lies in the source of the product chart. -/
theorem p1p1CornerPoint_mem_source : p1p1CornerPoint ∈ p1p1Chart.source := by
  rw [mem_p1p1Chart_source_iff, map_fst_p1p1CornerPoint, map_snd_p1p1CornerPoint]
  exact ⟨inftyPoint_mem_source, inftyPoint_mem_source⟩

/-- In the product chart, `{∞} × ℙ¹` is the hyperplane `{v₀ = 0}`. -/
theorem mem_p1p1FibreFst_support_iff (z : ComplexPoint p1p1) (hz : z ∈ p1p1Chart.source) :
    z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ↔ p1p1Chart z 0 = 0 := by
  rw [mem_p1p1FibreFst_support_iff_fst, p1p1Chart_apply_zero]
  exact underlying_eq_infty_iff _ ((mem_p1p1Chart_source_iff z).mp hz).1

/-- In the product chart, `ℙ¹ × {∞}` is the hyperplane `{v₁ = 0}`. -/
theorem mem_p1p1FibreSnd_support_iff (z : ComplexPoint p1p1) (hz : z ∈ p1p1Chart.source) :
    z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd ↔ p1p1Chart z 1 = 0 := by
  rw [mem_p1p1FibreSnd_support_iff_snd, p1p1Chart_apply_one]
  exact underlying_eq_infty_iff _ ((mem_p1p1Chart_source_iff z).mp hz).2

/-- The product chart is adapted to both fibres at every point of their intersection,
`{∞} × ℙ¹` as coordinate `0` and `ℙ¹ × {∞}` as coordinate `1`: hypothesis `htr` of
`cycle-class-multiplicative` with `a = b = 1`, `d = 2`. -/
theorem p1p1Fibres_transversal :
    ∀ y ∈ (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set (ComplexPoint p1p1)),
      ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint p1p1),
        y ∈ φ.source ∧
        ∀ z ∈ φ.source,
          (z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ↔
            ∀ i : Fin 1, φ z ⟨i, by omega⟩ = 0) ∧
          (z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreSnd ↔
            ∀ j : Fin 1, φ z ⟨1 + j, by omega⟩ = 0) := by
  intro y hy
  rw [p1p1Corner_support_eq_singleton] at hy
  rw [Set.mem_singleton_iff.mp hy]
  refine ⟨p1p1Chart, p1p1Chart_mem_maximalAtlas, p1p1CornerPoint_mem_source,
    fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_p1p1FibreFst_support_iff z hz]
    exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩
  · rw [mem_p1p1FibreSnd_support_iff z hz]
    exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩

/-! ### Smooth locus: hypotheses `hxreg`, `hwreg` -/

/-- Upstream's ℙ¹ is separated over `Spec ℂ`: Oka's `ℙₒ(1; ℂ) ⟶ Spec ℂ` is proper. -/
instance isSeparated_projectiveLine : IsSeparated projectiveLine.hom := by
  rw [projectiveLine_hom_eq]
  infer_instance

/-- The second projection of ℙ¹ × ℙ¹ is separated (a base change of `ℙ¹ ⟶ Spec ℂ`). -/
instance isSeparated_p1p1_snd : IsSeparated (prod.snd : p1p1 ⟶ projectiveLine).left := by
  rw [← Over.prodLeftIsoPullback_hom_snd]
  infer_instance

/-- The first projection of ℙ¹ × ℙ¹ is separated (a base change of `ℙ¹ ⟶ Spec ℂ`). -/
instance isSeparated_p1p1_fst : IsSeparated (prod.fst : p1p1 ⟶ projectiveLine).left := by
  rw [← Over.prodLeftIsoPullback_hom_fst]
  infer_instance

/-- The section `b ↦ (∞, b)` is a closed immersion: a section of the separated second
projection. -/
instance isClosedImmersion_fibreSectionFst : IsClosedImmersion fibreSectionFst.left := by
  have h : fibreSectionFst.left ≫ (prod.snd : p1p1 ⟶ projectiveLine).left = 𝟙 _ := by
    rw [← Over.comp_left, fibreSectionFst, prod.lift_snd]
    rfl
  have : IsClosedImmersion (fibreSectionFst.left ≫ (prod.snd : p1p1 ⟶ projectiveLine).left) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (prod.snd : p1p1 ⟶ projectiveLine).left

/-- The section `a ↦ (a, ∞)` is a closed immersion: a section of the separated first
projection. -/
instance isClosedImmersion_fibreSectionSnd : IsClosedImmersion fibreSectionSnd.left := by
  have h : fibreSectionSnd.left ≫ (prod.fst : p1p1 ⟶ projectiveLine).left = 𝟙 _ := by
    rw [← Over.comp_left, fibreSectionSnd, prod.lift_fst]
    rfl
  have : IsClosedImmersion (fibreSectionSnd.left ≫ (prod.fst : p1p1 ⟶ projectiveLine).left) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (prod.fst : p1p1 ⟶ projectiveLine).left

/-- The kernel of a morphism of schemes from a reduced scheme is the vanishing ideal of the
closure of its range. -/
theorem ker_eq_vanishingIdeal_of_isReduced {P Y : Scheme} [IsReduced P] (s : P ⟶ Y) :
    s.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range s)) := by
  have h1 : s.ker = (Scheme.Hom.ker (𝟙 P)).map s := by
    rw [← Scheme.Hom.ker_comp, Category.id_comp]
  rw [h1, Scheme.Hom.ker_eq_bot_of_isIso, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 2
  ext y
  simp

/-- **Smoothness of a reduced closure that is the image of a section.** If `s : P ⟶ X` over
`Spec ℂ` is a closed immersion from a reduced smooth `P` and the closure of its range is
`closure {x}`, then the reduced closure of `x` is smooth over `ℂ`: it is `P`, through Mathlib's
`Scheme.Hom.toImage`. -/
theorem smooth_cycleComponentι_of_closedImmersion {P X : Over (Spec ↧ℂ)} [IsReduced P.left]
    [Smooth P.hom] (s : P ⟶ X) [IsClosedImmersion s.left] (x : X.left)
    (hx : closure (Set.range s.left) = closure {x}) :
    Smooth (cycleComponentι X.left x ≫ X.hom) := by
  have hker : s.left.ker =
      Scheme.IdealSheafData.vanishingIdeal (X := X.left) ⟨closure {x}, isClosed_closure⟩ := by
    rw [ker_eq_vanishingIdeal_of_isReduced]
    congr 1
    ext1
    exact hx
  change Smooth ((Scheme.IdealSheafData.vanishingIdeal
    (X := X.left) ⟨closure {x}, isClosed_closure⟩).subschemeι ≫ X.hom)
  rw [← hker]
  have hι : s.left.ker.subschemeι = inv s.left.toImage ≫ s.left := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [hι, Category.assoc, Over.w s]
  infer_instance

/-- The reduced closure of `{∞} × ℙ¹` is smooth over `ℂ`. -/
theorem smooth_cycleComponentι_p1p1FibreFst :
    Smooth (cycleComponentι p1p1.left p1p1FibreFst ≫ p1p1.hom) :=
  smooth_cycleComponentι_of_closedImmersion fibreSectionFst p1p1FibreFst
    (by rw [← Set.image_univ]; exact ((genericPoint_spec _).image (Scheme.Hom.continuous _)).symm)

/-- The reduced closure of `ℙ¹ × {∞}` is smooth over `ℂ`. -/
theorem smooth_cycleComponentι_p1p1FibreSnd :
    Smooth (cycleComponentι p1p1.left p1p1FibreSnd ≫ p1p1.hom) :=
  smooth_cycleComponentι_of_closedImmersion fibreSectionSnd p1p1FibreSnd
    (by rw [← Set.image_univ]; exact ((genericPoint_spec _).image (Scheme.Hom.continuous _)).symm)

/-- `(∞, ∞)` lies off the singular locus of `{∞} × ℙ¹`: hypothesis `hxreg` of
`cycle-class-multiplicative`. -/
theorem p1p1Corner_support_subset_smoothSupportAmbientOpen_fst :
    (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set (ComplexPoint p1p1)) ⊆
      cycleComponentSmoothSupportAmbientOpen p1p1 p1p1FibreFst := by
  have := smooth_cycleComponentι_p1p1FibreFst
  rintro y - ⟨z, hz, -⟩
  exact hz (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)

/-- `(∞, ∞)` lies off the singular locus of `ℙ¹ × {∞}`: hypothesis `hwreg` of
`cycle-class-multiplicative`. -/
theorem p1p1Corner_support_subset_smoothSupportAmbientOpen_snd :
    (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set (ComplexPoint p1p1)) ⊆
      cycleComponentSmoothSupportAmbientOpen p1p1 p1p1FibreSnd := by
  have := smooth_cycleComponentι_p1p1FibreSnd
  rintro y - ⟨z, hz, -⟩
  exact hz (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)

/-! ### Non-vacuity -/

/-- The two fibres are different scheme points: their first projections are `∞` and the generic
point. -/
theorem p1p1FibreFst_ne_p1p1FibreSnd : p1p1FibreFst ≠ p1p1FibreSnd := by
  intro h
  have h1 := fst_p1p1FibreFst
  rw [h, fst_p1p1FibreSnd] at h1
  exact infty_ne_top h1.symm

/-- The product chart sends `(∞, ∞)` to the origin. -/
theorem p1p1Chart_p1p1CornerPoint : p1p1Chart p1p1CornerPoint = 0 := by
  have h0 : lineChart inftyPoint 0 = 0 :=
    (underlying_eq_infty_iff _ inftyPoint_mem_source).mp inftyPoint_underlying
  funext i
  fin_cases i
  · change p1p1Chart p1p1CornerPoint 0 = 0
    rw [p1p1Chart_apply_zero, map_fst_p1p1CornerPoint, h0]
  · change p1p1Chart p1p1CornerPoint 1 = 0
    rw [p1p1Chart_apply_one, map_snd_p1p1CornerPoint, h0]

/-- Coordinate `1` of the product chart does not cut out `{∞} × ℙ¹`: the order of `htr` is
visible. -/
theorem not_forall_mem_p1p1FibreFst_iff_coord_one : ¬ ∀ z ∈ p1p1Chart.source,
    (z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst ↔ p1p1Chart z 1 = 0) := by
  intro h
  have ht : (![1] : Fin 1 → ℂ) ∈ lineChart.target := by
    rw [lineChart, projectiveChart, affineChart_target]; trivial
  set b : ComplexPoint projectiveLine := lineChart.symm ![1]
  have hb1 : lineChart b 0 = 1 := by rw [show lineChart b = ![1] from lineChart.right_inv ht]; rfl
  set z : ComplexPoint p1p1 := prod.lift inftyPoint b
  have hfst : Point.map prod.fst z = inftyPoint := prod.lift_fst _ _
  have hsnd : Point.map prod.snd z = b := prod.lift_snd _ _
  have hz : z ∈ p1p1Chart.source := by
    rw [mem_p1p1Chart_source_iff, hfst, hsnd]
    exact ⟨inftyPoint_mem_source, lineChart.map_target ht⟩
  have hmem : z ∈ cycleComponentAnalyticClosedSupport p1p1 p1p1FibreFst := by
    rw [mem_p1p1FibreFst_support_iff_fst, hfst, inftyPoint_underlying]
  have := (h z hz).mp hmem
  rw [p1p1Chart_apply_one, hsnd, hb1] at this
  exact one_ne_zero this

end HodgeLadder.Tests
