module

public import HodgeLadder.Tests.ChartCohomology
public import HodgeLadder.Tests.CycleClassMultiplicativeP1p1

/-!
# The class of the point `(∞, ∞)` of ℙ¹ × ℙ¹ is nonzero

Rung `p1p1-point-class-nonzero`: the class of `(∞, ∞)` in `H⁴(ℙ¹ × ℙ¹; ℚ)`, upstream's
`cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add`, is nonzero, with
`∞ = [1 : 0]` as in `p1p1-fibres-transversal`. With `cycle-class-multiplicative-p1p1` this makes
`[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] = [(∞, ∞)]` a non-vacuous identity.

Route, as for `p2-point-class-nonzero`. The criterion
`cycleComponentSheafClass_ne_zero_of_subsingleton_odd` at `p = 1` reduces the rung to
`H³(U; ℚ) = 0` for the complement `U` of the point (`forget-support-exact`). Write `U₀`, `U₁` for
the standard opens `x₀ ≠ 0`, `x₁ ≠ 0` of ℙ¹, so `ℙ¹ ∖ {∞} = U₁`. Then

`U = (U₁ × U₀ ∪ U₁ × U₁) ∪ U₀ × U₁`,

three copies of `ℂ²` (each the source of a product of standard charts, `p1p1StdChart`). Two
Mayer–Vietoris steps (`TopCat.Sheaf.subsingleton_H'_sup` from the Oka port) reduce `H³(U) = 0` to
`H²` of two intersections, `U₁ × (U₀ ∩ U₁)` and `(U₀ ∩ U₁) × U₁`. Each is `{v k ≠ 0}` in a product
chart, a copy of `ℂ^* × ℂ`; its `H²` vanishes by the two further Mayer–Vietoris steps of the ℙ²
rung (slit pieces, then half-spaces), done once for any chart onto `ℂⁿ` and any coordinate in
`HodgeLadder.Tests.ChartCohomology` (`subsingleton_H'_two_chartPreOpen_coord_ne_zero`). Every
piece is star-convex in a chart, hence contractible, hence acyclic in positive degrees
(`contractible-open-acyclic`). No orientation or sign enters: the statement is `≠ 0`.

## Main definitions

* `HodgeLadder.Tests.p1p1StdChart`, `p1p1StdOpen`, `p1p1Const`

## Main results

* `HodgeLadder.Tests.p1p1_point_class_ne_zero`: the rung.
* `HodgeLadder.Tests.p1p1Fibres_cup_ne_zero`: `[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] ≠ 0`.
* `HodgeLadder.Tests.subsingleton_H'_three_compl_p1p1Corner`: `H³((ℙ¹ × ℙ¹)(ℂ) ∖ (∞, ∞); ℚ) = 0`.
* `HodgeLadder.Tests.p1p1Corner_support_compl`, `p1p1StdOpen_inf_one_zero`,
  `p1p1StdOpen_sup_inf_zero_one`: the cover and its intersections.
* `HodgeLadder.Tests.mem_projectiveChart_one_source_iff`: the chart `x₁ ≠ 0` of ℙ¹ is the
  complement of `∞`.
* `HodgeLadder.Tests.contractibleSpace_p1p1StdOpen`, `p1p1StdChart_target`,
  `eq_p1p1CornerPoint_iff`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint Order

namespace HodgeLadder.Tests

open HodgeLadder.Normalization HodgeLadder.ComplexPointProd

/-! ### The chart `x₁ ≠ 0` of ℙ¹ -/

/-- The chart `x₁ ≠ 0` of ℙ¹(ℂ) covers every complex point except `∞ = [1 : 0]`. -/
theorem mem_projectiveChart_one_source_iff (b : ComplexPoint projectiveLine) :
    b ∈ (projectiveChart 1 1).source ↔ b ≠ inftyPoint := by
  have key : ∀ c ∈ lineChart.source,
      c ∈ (projectiveChart 1 1).source ↔ lineChart c 0 ≠ 0 := fun c hc => by
    rw [mem_projectiveChart_source_iff_coord 1 0 1 c hc]
    rfl
  constructor
  · rintro hb rfl
    rw [key _ inftyPoint_mem_source] at hb
    exact hb ((underlying_eq_infty_iff _ inftyPoint_mem_source).mp inftyPoint_underlying)
  · intro hne
    obtain ⟨j, hj⟩ := exists_mem_projectiveChart_source 1 b
    fin_cases j
    · have hj : b ∈ lineChart.source := hj
      rw [key b hj]
      intro h0
      exact hne (eq_inftyPoint_of_underlying b ((underlying_eq_infty_iff b hj).mpr h0))
    · exact hj


/-! ### Standard product charts of ℙ¹ × ℙ¹ -/

/-- The product of the standard charts `xᵢ ≠ 0` and `xⱼ ≠ 0` of ℙ¹, first factor first. -/
def p1p1StdChart (i j : Fin 2) : OpenPartialHomeomorph (ComplexPoint p1p1) (Fin 2 → ℂ) :=
  prodChart projectiveLine projectiveLine (projectiveChart 1 i) (projectiveChart 1 j)

/-- The chart `p1p1StdChart i j` is onto `ℂ²`. -/
theorem p1p1StdChart_target (i j : Fin 2) : (p1p1StdChart i j).target = Set.univ := by
  rw [p1p1StdChart, prodChart_target, projectiveChart, projectiveChart, affineChart_target,
    affineChart_target, Set.univ_prod_univ, Set.preimage_univ]

/-- The source of `p1p1StdChart i j`. -/
theorem mem_p1p1StdChart_source_iff (i j : Fin 2) (z : ComplexPoint p1p1) :
    z ∈ (p1p1StdChart i j).source ↔ Point.map prod.fst z ∈ (projectiveChart 1 i).source ∧
      Point.map prod.snd z ∈ (projectiveChart 1 j).source := by
  rw [p1p1StdChart, prodChart_source]
  rfl

/-- Coordinate `0` of `p1p1StdChart i j` is the chart of the first projection. -/
theorem p1p1StdChart_apply_zero (i j : Fin 2) (z : ComplexPoint p1p1) :
    p1p1StdChart i j z 0 = projectiveChart 1 i (Point.map prod.fst z) 0 := by
  rw [p1p1StdChart, prodChart_apply]
  rfl

/-- Coordinate `1` of `p1p1StdChart i j` is the chart of the second projection. -/
theorem p1p1StdChart_apply_one (i j : Fin 2) (z : ComplexPoint p1p1) :
    p1p1StdChart i j z 1 = projectiveChart 1 j (Point.map prod.snd z) 0 := by
  rw [p1p1StdChart, prodChart_apply]
  rfl

/-- The open `{xᵢ ≠ 0} × {xⱼ ≠ 0}` of `(ℙ¹ × ℙ¹)(ℂ)`, the source of `p1p1StdChart i j`. -/
abbrev p1p1StdOpen (i j : Fin 2) : Opens (ComplexPoint p1p1) :=
  chartPreOpen (p1p1StdChart i j) Set.univ isOpen_univ

/-- Membership in `p1p1StdOpen i j`. -/
theorem mem_p1p1StdOpen_iff (i j : Fin 2) (z : ComplexPoint p1p1) :
    z ∈ p1p1StdOpen i j ↔ Point.map prod.fst z ∈ (projectiveChart 1 i).source ∧
      Point.map prod.snd z ∈ (projectiveChart 1 j).source := by
  rw [mem_chartPreOpen, ← mem_p1p1StdChart_source_iff]
  exact and_iff_left trivial

/-- Each `p1p1StdOpen i j` is contractible (it is `ℂ²`). -/
theorem contractibleSpace_p1p1StdOpen (i j : Fin 2) : ContractibleSpace (p1p1StdOpen i j) :=
  contractibleSpace_chartPreOpen _ (p1p1StdChart_target i j) _ _ (starConvex_univ 0)
    Set.univ_nonempty

/-- A complex point of ℙ¹ × ℙ¹ is `(∞, ∞)` exactly when both projections are `∞`. -/
theorem eq_p1p1CornerPoint_iff (z : ComplexPoint p1p1) :
    z = p1p1CornerPoint ↔
      Point.map prod.fst z = inftyPoint ∧ Point.map prod.snd z = inftyPoint := by
  constructor
  · rintro rfl
    exact ⟨map_fst_p1p1CornerPoint, map_snd_p1p1CornerPoint⟩
  · rintro ⟨h1, h2⟩
    rw [eq_prodLift z, h1, h2]
    rfl

/-- The complement of `(∞, ∞)` is the union of `{x₁ ≠ 0} × {x₀ ≠ 0}`, `{x₁ ≠ 0} × {x₁ ≠ 0}`
and `{x₀ ≠ 0} × {x₁ ≠ 0}`. -/
theorem p1p1Corner_support_compl :
    (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner).compl =
      (p1p1StdOpen 1 0 ⊔ p1p1StdOpen 1 1) ⊔ p1p1StdOpen 0 1 := by
  ext z
  change z ∉ (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner : Set _) ↔
    (z ∈ p1p1StdOpen 1 0 ∨ z ∈ p1p1StdOpen 1 1) ∨ z ∈ p1p1StdOpen 0 1
  rw [p1p1Corner_support_eq_singleton, Set.mem_singleton_iff, eq_p1p1CornerPoint_iff,
    mem_p1p1StdOpen_iff, mem_p1p1StdOpen_iff, mem_p1p1StdOpen_iff,
    mem_projectiveChart_one_source_iff, mem_projectiveChart_one_source_iff]
  have hcov : ∀ b : ComplexPoint projectiveLine,
      b ∈ (projectiveChart 1 0).source ∨ b ≠ inftyPoint := fun b => by
    obtain ⟨j, hj⟩ := exists_mem_projectiveChart_source 1 b
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr ((mem_projectiveChart_one_source_iff b).mp hj)
  have h0 : inftyPoint ∈ (projectiveChart 1 0).source := inftyPoint_mem_source
  rcases hcov (Point.map prod.fst z) with ha | ha <;>
  rcases hcov (Point.map prod.snd z) with hb | hb <;>
  by_cases ha' : Point.map prod.fst z = inftyPoint <;>
  by_cases hb' : Point.map prod.snd z = inftyPoint <;>
  simp_all

/-- In the chart `{x₁ ≠ 0} × {x₀ ≠ 0}`, the intersection with `{x₁ ≠ 0} × {x₁ ≠ 0}` is
`{v₁ ≠ 0}`. -/
theorem p1p1StdOpen_inf_one_zero :
    p1p1StdOpen 1 0 ⊓ p1p1StdOpen 1 1 =
      chartPreOpen (p1p1StdChart 1 0) {v | v 1 ≠ 0} (isOpen_coord_ne_zero 1) := by
  ext z
  change z ∈ p1p1StdOpen 1 0 ∧ z ∈ p1p1StdOpen 1 1 ↔ z ∈ (p1p1StdChart 1 0).source ∧
    p1p1StdChart 1 0 z 1 ≠ 0
  rw [mem_p1p1StdOpen_iff, mem_p1p1StdOpen_iff, mem_p1p1StdChart_source_iff,
    p1p1StdChart_apply_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h4⟩
    exact ⟨⟨h1, h2⟩, (mem_projectiveChart_source_iff_coord 1 0 1 _ h2).mp h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, h2⟩, h1, (mem_projectiveChart_source_iff_coord 1 0 1 _ h2).mpr h4⟩

/-- In the chart `{x₀ ≠ 0} × {x₁ ≠ 0}`, the intersection with `{x₁ ≠ 0} × ℙ¹` is `{v₀ ≠ 0}`. -/
theorem p1p1StdOpen_sup_inf_zero_one :
    (p1p1StdOpen 1 0 ⊔ p1p1StdOpen 1 1) ⊓ p1p1StdOpen 0 1 =
      chartPreOpen (p1p1StdChart 0 1) {v | v 0 ≠ 0} (isOpen_coord_ne_zero 0) := by
  ext z
  change (z ∈ p1p1StdOpen 1 0 ∨ z ∈ p1p1StdOpen 1 1) ∧ z ∈ p1p1StdOpen 0 1 ↔
    z ∈ (p1p1StdChart 0 1).source ∧ p1p1StdChart 0 1 z 0 ≠ 0
  rw [mem_p1p1StdOpen_iff, mem_p1p1StdOpen_iff, mem_p1p1StdOpen_iff, mem_p1p1StdChart_source_iff,
    p1p1StdChart_apply_zero]
  constructor
  · rintro ⟨h | h, h3, h4⟩
    · exact ⟨⟨h3, h4⟩, (mem_projectiveChart_source_iff_coord 1 0 1 _ h3).mp h.1⟩
    · exact ⟨⟨h3, h4⟩, (mem_projectiveChart_source_iff_coord 1 0 1 _ h3).mp h.1⟩
  · rintro ⟨⟨h3, h4⟩, h5⟩
    exact ⟨Or.inr ⟨(mem_projectiveChart_source_iff_coord 1 0 1 _ h3).mpr h5, h4⟩, h3, h4⟩

/-! ### `H³` of the complement of the point -/

/-- The rational constant sheaf on `(ℙ¹ × ℙ¹)(ℂ)`. -/
abbrev p1p1Const : TopCat.AbSheaf (TopCat.of (ComplexPoint p1p1)) :=
  (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint p1p1))).obj (AddCommGrpCat.of ℚ)

/-- `H³((ℙ¹ × ℙ¹)(ℂ) ∖ (∞, ∞); ℚ) = 0`. -/
theorem subsingleton_H'_three_compl_p1p1Corner :
    Subsingleton (Sheaf.H' p1p1Const 3
      (cycleComponentAnalyticClosedSupport p1p1 p1p1Corner).compl) := by
  have hc : ∀ (U : Opens (ComplexPoint p1p1)) [ContractibleSpace U] (q : ℕ),
      Subsingleton (Sheaf.H' p1p1Const (q + 1) U) := fun U _ q =>
    contractibleOpen_subsingleton_H' p1p1 U (q + 1) q.succ_pos
  have := contractibleSpace_p1p1StdOpen 1 0
  have := contractibleSpace_p1p1StdOpen 1 1
  have := contractibleSpace_p1p1StdOpen 0 1
  -- `H³({x₁ ≠ 0} × ℙ¹)`, covered by two copies of `ℂ²` meeting in `ℂ × ℂ^*`
  have hA : Subsingleton (Sheaf.H' p1p1Const 3 (p1p1StdOpen 1 0 ⊔ p1p1StdOpen 1 1)) := by
    refine TopCat.Sheaf.subsingleton_H'_sup p1p1Const _ _ 2 ?_ (hc _ 2) (hc _ 2)
    rw [p1p1StdOpen_inf_one_zero]
    exact subsingleton_H'_two_chartPreOpen_coord_ne_zero p1p1 _ (p1p1StdChart_target 1 0) 1
  rw [p1p1Corner_support_compl]
  refine TopCat.Sheaf.subsingleton_H'_sup p1p1Const _ _ 2 ?_ hA (hc _ 2)
  rw [p1p1StdOpen_sup_inf_zero_one]
  exact subsingleton_H'_two_chartPreOpen_coord_ne_zero p1p1 _ (p1p1StdChart_target 0 1) 0

/-! ### The class -/

/-- **`p1p1-point-class-nonzero`**: the class of `(∞, ∞)` in `H⁴(ℙ¹ × ℙ¹; ℚ)` is nonzero. -/
theorem p1p1_point_class_ne_zero :
    cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner_add ≠ 0 :=
  cycleComponentSheafClass_ne_zero_of_subsingleton_odd p1p1 p1p1Corner 1
    coheight_p1p1Corner_add subsingleton_H'_three_compl_p1p1Corner

/-- The rung with the coheight in the form `↑2`, in degree `2 * 2`. -/
example : cycleComponentSheafClass p1p1 p1p1Corner coheight_p1p1Corner ≠ 0 :=
  p1p1_point_class_ne_zero

/-- `[{∞} × ℙ¹] ∪ [ℙ¹ × {∞}] ≠ 0` in `H⁴(ℙ¹ × ℙ¹; ℚ)`: the cup product equals the nonzero class of
`(∞, ∞)` (`p1p1Fibres_cup_eq_p1p1Corner`). -/
theorem p1p1Fibres_cup_ne_zero :
    HodgeLadder.Cup.cup
        (cycleComponentSheafClass p1p1 p1p1FibreFst coheight_p1p1FibreFst)
        (cycleComponentSheafClass p1p1 p1p1FibreSnd coheight_p1p1FibreSnd)
        (2 * (1 + 1)) (by ring) ≠ 0 := by
  rw [p1p1Fibres_cup_eq_p1p1Corner]
  exact p1p1_point_class_ne_zero

end HodgeLadder.Tests
