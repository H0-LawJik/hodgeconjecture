module

public import HodgeLadder.Tests.ProjectivePlanePoint

/-!
# Cohomology of coordinate opens in a chart

General lemmas for rung `p1p1-point-class-nonzero`, kept below the cup stack so that a later user
imports only `HodgeLadder.Tests.ProjectivePlanePoint`. They are the any-`n`, any-coordinate forms
of the chart lemmas and of the `H²` step of `p2-point-class-nonzero`.

* The standard charts of ℙⁿ for every `n`: a point of the chart `xᵢ ≠ 0` lies in `xⱼ ≠ 0` iff
  coordinate `j` of `Fin.insertNth i 1 (φᵢ z)` is nonzero, and the charts cover ℙⁿ(ℂ).
* `chartPreOpen φ S hS`: the open `φ.source ∩ φ⁻¹(S)` of a partial homeomorphism, bundled as
  `Opens`, with its lattice lemmas; it is contractible when `S` is nonempty and star-convex and
  the target of `φ` is everything.
* The slit pieces and half-spaces of `{v | v k ≠ 0} ⊆ ℂⁿ`.
* `subsingleton_H'_two_chartPreOpen_coord_ne_zero`: on a smooth projective integral `X`, in a
  chart onto `ℂⁿ`, the open `{v k ≠ 0}` (a copy of `ℂ^* × ℂ^{n-1}`) has no rational cohomology in
  degree two, by two Mayer–Vietoris steps over star-convex pieces.

The ℙ² forms in `HodgeLadder.Tests.ProjectivePlanePoint` are the case `n = 2` by `rfl`
(`planeChartZeroOpen S hS` is `chartPreOpen (projectiveChart 2 0) S hS`); the `example` at the end
derives the ℙ² `H²` step from the general lemma.

## Main definitions

* `HodgeLadder.Tests.chartPreOpen`
* `HodgeLadder.Tests.coordSlitPos`, `coordSlitNeg`, `coordHalfPos`, `coordHalfNeg`, `coordProj`

## Main results

* `HodgeLadder.Tests.mem_projectiveChart_source_iff_underlying`,
  `mem_projectiveChart_source_iff_coord`, `exists_mem_projectiveChart_source`
* `HodgeLadder.Tests.chartPreOpen_inf`, `chartPreOpen_sup`, `chartPreOpen_empty`,
  `chartPreOpen_congr`, `contractibleSpace_chartPreOpen`
* `HodgeLadder.Tests.coordSlitPos_union_coordSlitNeg`, `coordSlitPos_inter_coordSlitNeg`,
  `coordHalfPos_inter_coordHalfNeg`
* `HodgeLadder.Tests.subsingleton_H'_two_chartPreOpen_coord_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory Limits Topology TopologicalSpace AlgebraicGeometry ComplexPoint Order

namespace HodgeLadder.Tests

open HodgeLadder.Normalization

/-! ### Standard charts of ℙⁿ -/

/-- A complex point of ℙⁿ lies in the source of the chart `xᵢ ≠ 0` exactly when its underlying
point lies in the standard open `xᵢ ≠ 0`. -/
theorem mem_projectiveChart_source_iff_underlying (n : ℕ) (i : Fin (n + 1))
    (z : ComplexPoint (projectiveSpace n)) :
    z ∈ (projectiveChart n i).source ↔
      z.underlying ∈ (okaIsoSpace n).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U n ℂ i := by
  rw [← projectiveChartOpen_eq, projectiveChart, affineChart_source]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Point.underlying_map]
    exact q.underlying.property
  · intro h
    exact ⟨(openEquiv _ _).symm ⟨z, h⟩,
      congrArg Subtype.val ((openEquiv _ _).apply_symm_apply _)⟩

/-- A point of the chart `xᵢ ≠ 0` of ℙⁿ lies in the standard open `xⱼ ≠ 0` exactly when
coordinate `j` of `Fin.insertNth i 1 (φᵢ z)` is nonzero. -/
theorem mem_projectiveChart_source_iff_coord (n : ℕ) (i j : Fin (n + 1))
    (z : ComplexPoint (projectiveSpace n)) (hz : z ∈ (projectiveChart n i).source) :
    z ∈ (projectiveChart n j).source ↔
      Fin.insertNth (α := fun _ => ℂ) i 1 (projectiveChart n i z) j ≠ 0 := by
  rw [mem_projectiveChart_source_iff_underlying, ← projectiveChart_symm_mem_U_iff n i j,
    (projectiveChart n i).left_inv hz]

/-- The standard charts cover ℙⁿ(ℂ). -/
theorem exists_mem_projectiveChart_source (n : ℕ) (z : ComplexPoint (projectiveSpace n)) :
    ∃ j : Fin (n + 1), z ∈ (projectiveChart n j).source := by
  have hcov : (okaIsoSpace n).inv.base z.underlying ∈
      (⨆ j, AlgebraicGeometry.ProjectiveSpace.U n ℂ j) :=
    (AlgebraicGeometry.ProjectiveSpace.iSup_U n ℂ) ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  refine ⟨j, (mem_projectiveChart_source_iff_underlying n j z).mpr ?_⟩
  have := (Scheme.Hom.apply_mem_image_iff (okaIsoSpace n).hom).mpr hj
  simpa using this


/-! ### Opens cut out in a chart -/

/-- The open `φ⁻¹(S)` of the source of a chart `φ`, for an open `S` of the model space. -/
def chartPreOpen {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (φ : OpenPartialHomeomorph M E) (S : Set E) (hS : IsOpen S) : Opens M :=
  ⟨φ.source ∩ φ ⁻¹' S, φ.isOpen_inter_preimage hS⟩

section ChartPreOpen

variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E] (φ : OpenPartialHomeomorph M E)

/-- Membership in `chartPreOpen`. -/
theorem mem_chartPreOpen {S : Set E} (hS : IsOpen S) (z : M) :
    z ∈ chartPreOpen φ S hS ↔ z ∈ φ.source ∧ φ z ∈ S :=
  Iff.rfl

/-- `chartPreOpen` carries intersections to intersections. -/
theorem chartPreOpen_inf (S T : Set E) (hS : IsOpen S) (hT : IsOpen T) :
    chartPreOpen φ S hS ⊓ chartPreOpen φ T hT = chartPreOpen φ (S ∩ T) (hS.inter hT) := by
  ext z
  simp only [chartPreOpen, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- `chartPreOpen` carries unions to unions. -/
theorem chartPreOpen_sup (S T : Set E) (hS : IsOpen S) (hT : IsOpen T) :
    chartPreOpen φ S hS ⊔ chartPreOpen φ T hT = chartPreOpen φ (S ∪ T) (hS.union hT) := by
  ext z
  simp only [chartPreOpen, Opens.coe_sup, Opens.coe_mk, Set.mem_union, Set.mem_inter_iff,
    Set.mem_preimage]
  tauto

/-- `chartPreOpen φ ∅` is empty. -/
theorem chartPreOpen_empty : chartPreOpen φ ∅ isOpen_empty = ⊥ := by
  ext z
  simp [chartPreOpen]

/-- `chartPreOpen` depends only on the set, not on the openness proof. -/
theorem chartPreOpen_congr {S T : Set E} (hS : IsOpen S) (hT : IsOpen T) (h : S = T) :
    chartPreOpen φ S hS = chartPreOpen φ T hT := by
  subst h; rfl

/-- In a chart onto a real vector space, a star-convex nonempty open of the model space cuts out a
contractible open. -/
theorem contractibleSpace_chartPreOpen [AddCommGroup E] [Module ℝ E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] (ht : φ.target = Set.univ) (S : Set E) (hS : IsOpen S) {c : E}
    (hc : StarConvex ℝ c S) (hne : S.Nonempty) : ContractibleSpace (chartPreOpen φ S hS) := by
  have himg : φ '' (chartPreOpen φ S hS : Set M) = S := by
    change φ '' (φ.source ∩ φ ⁻¹' S) = S
    ext v
    refine ⟨fun ⟨z, ⟨_, hz⟩, hzv⟩ => hzv ▸ hz, fun hv => ?_⟩
    have hvt : v ∈ φ.target := by rw [ht]; trivial
    refine ⟨φ.symm v, ⟨φ.map_target hvt, ?_⟩, φ.right_inv hvt⟩
    change φ (φ.symm v) ∈ S
    rw [φ.right_inv hvt]; exact hv
  obtain ⟨v, hv⟩ := hne
  refine contractibleSpace_of_starConvex_image φ (s := (chartPreOpen φ S hS : Set M))
    Set.inter_subset_left (c := c) (by rw [himg]; exact hc) ?_
  rw [← himg] at hv
  obtain ⟨z, hz, -⟩ := hv
  exact ⟨z, hz⟩

end ChartPreOpen

/-! ### Four pieces of `{v | v k ≠ 0}` -/

section Coord

variable {n : ℕ}

/-- `{v | v k ∈ ℂ ∖ (-∞, 0]}`. -/
def coordSlitPos (k : Fin n) : Set (Fin n → ℂ) := {v | v k ∈ Complex.slitPlane}
/-- `{v | -v k ∈ ℂ ∖ (-∞, 0]}`. -/
def coordSlitNeg (k : Fin n) : Set (Fin n → ℂ) := {v | -v k ∈ Complex.slitPlane}
/-- `{v | 0 < Im v k}`. -/
def coordHalfPos (k : Fin n) : Set (Fin n → ℂ) := {v | 0 < (v k).im}
/-- `{v | Im v k < 0}`. -/
def coordHalfNeg (k : Fin n) : Set (Fin n → ℂ) := {v | (v k).im < 0}

/-- `coordSlitPos k` is open. -/
theorem isOpen_coordSlitPos (k : Fin n) : IsOpen (coordSlitPos k) :=
  Complex.isOpen_slitPlane.preimage (continuous_apply k)
/-- `coordSlitNeg k` is open. -/
theorem isOpen_coordSlitNeg (k : Fin n) : IsOpen (coordSlitNeg k) :=
  Complex.isOpen_slitPlane.preimage (continuous_apply k).neg
/-- `coordHalfPos k` is open. -/
theorem isOpen_coordHalfPos (k : Fin n) : IsOpen (coordHalfPos k) :=
  isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply k))
/-- `coordHalfNeg k` is open. -/
theorem isOpen_coordHalfNeg (k : Fin n) : IsOpen (coordHalfNeg k) :=
  isOpen_lt (Complex.continuous_im.comp (continuous_apply k)) continuous_const
/-- `{v | v k ≠ 0}` is open. -/
theorem isOpen_coord_ne_zero (k : Fin n) : IsOpen {v : Fin n → ℂ | v k ≠ 0} :=
  isOpen_ne_fun (continuous_apply k) continuous_const

/-- The two slit pieces cover `{v | v k ≠ 0}`. -/
theorem coordSlitPos_union_coordSlitNeg (k : Fin n) :
    coordSlitPos k ∪ coordSlitNeg k = {v | v k ≠ 0} := by
  ext v
  simp only [coordSlitPos, coordSlitNeg, Set.mem_union, Set.mem_ofPred_eq,
    Complex.mem_slitPlane_iff,
    Complex.neg_re, Complex.neg_im, ne_eq, neg_eq_zero, Complex.ext_iff, Complex.zero_re,
    Complex.zero_im, not_and_or, Left.neg_pos_iff]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h.ne'
    · exact Or.inr h
    · exact Or.inl h.ne
    · exact Or.inr h
  · rintro (h | h)
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- The two slit pieces meet in `{v | Im v k ≠ 0}`, the union of the two half-spaces. -/
theorem coordSlitPos_inter_coordSlitNeg (k : Fin n) :
    coordSlitPos k ∩ coordSlitNeg k = coordHalfPos k ∪ coordHalfNeg k := by
  ext v
  simp only [coordSlitPos, coordSlitNeg, coordHalfPos, coordHalfNeg, Set.mem_union,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Complex.mem_slitPlane_iff, Complex.neg_re,
    Complex.neg_im, ne_eq, neg_eq_zero, Left.neg_pos_iff]
  constructor
  · rintro ⟨h | h, h' | h'⟩
    · exact absurd (h.trans h') (lt_irrefl _)
    · rcases lt_or_gt_of_ne h' with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rintro (h | h)
    · exact ⟨Or.inr h.ne', Or.inr h.ne'⟩
    · exact ⟨Or.inr h.ne, Or.inr h.ne⟩

/-- The two half-spaces are disjoint. -/
theorem coordHalfPos_inter_coordHalfNeg (k : Fin n) :
    coordHalfPos k ∩ coordHalfNeg k = ∅ := by
  ext v
  simp only [coordHalfPos, coordHalfNeg, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro h; exact h.le

/-- The `ℝ`-linear coordinate `v ↦ v k`. -/
def coordProj (k : Fin n) : (Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k

/-- `coordSlitPos k` is star-convex about the constant vector `1`. -/
theorem starConvex_coordSlitPos (k : Fin n) : StarConvex ℝ (fun _ => 1) (coordSlitPos k) :=
  Complex.starConvex_one_slitPlane.linear_preimage (coordProj k)
/-- `coordSlitNeg k` is star-convex about the constant vector `-1`. -/
theorem starConvex_coordSlitNeg (k : Fin n) : StarConvex ℝ (fun _ => -1) (coordSlitNeg k) :=
  (show StarConvex ℝ ((-coordProj k) (fun _ => -1)) Complex.slitPlane by
    simpa [coordProj] using Complex.starConvex_one_slitPlane).linear_preimage (-coordProj k)
/-- `coordHalfPos k` is star-convex about the constant vector `i`. -/
theorem starConvex_coordHalfPos (k : Fin n) : StarConvex ℝ (fun _ => Complex.I) (coordHalfPos k) :=
  ((convex_halfSpace_im_gt 0).linear_preimage (coordProj k)).starConvex
    (show (0 : ℝ) < Complex.I.im by simp)
/-- `coordHalfNeg k` is star-convex about the constant vector `-i`. -/
theorem starConvex_coordHalfNeg (k : Fin n) :
    StarConvex ℝ (fun _ => -Complex.I) (coordHalfNeg k) :=
  ((convex_halfSpace_im_lt 0).linear_preimage (coordProj k)).starConvex
    (show (-Complex.I).im < (0 : ℝ) by simp)

end Coord

/-! ### `H²` of a coordinate complement in a chart -/

/-- On a smooth projective integral `X`, in a chart `φ` onto `ℂⁿ` (target everything), the open
`{v k ≠ 0}` of the chart, homeomorphic to `ℂ^* × ℂ^{n-1}`, has no rational cohomology in degree
two. Two Mayer–Vietoris steps over the slit pieces and the half-spaces, all star-convex. -/
theorem subsingleton_H'_two_chartPreOpen_coord_ne_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {n : ℕ}
    (φ : OpenPartialHomeomorph (ComplexPoint X) (Fin n → ℂ)) (ht : φ.target = Set.univ)
    (k : Fin n) :
    Subsingleton (Sheaf.H' ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
      (AddCommGrpCat.of ℚ)) 2 (chartPreOpen φ {v | v k ≠ 0} (isOpen_coord_ne_zero k))) := by
  set F := (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)
  have hc : ∀ (U : Opens (ComplexPoint X)) [ContractibleSpace U] (q : ℕ),
      Subsingleton (Sheaf.H' F (q + 1) U) := fun U _ q =>
    contractibleOpen_subsingleton_H' X U (q + 1) q.succ_pos
  have h1 : Subsingleton (Sheaf.H' F 1
      (chartPreOpen φ _ (isOpen_coordHalfPos k) ⊔ chartPreOpen φ _ (isOpen_coordHalfNeg k))) := by
    have := contractibleSpace_chartPreOpen φ ht _ (isOpen_coordHalfPos k)
      (starConvex_coordHalfPos k) ⟨fun _ => Complex.I, by simp [coordHalfPos]⟩
    have := contractibleSpace_chartPreOpen φ ht _ (isOpen_coordHalfNeg k)
      (starConvex_coordHalfNeg k) ⟨fun _ => -Complex.I, by simp [coordHalfNeg]⟩
    refine TopCat.Sheaf.subsingleton_H'_sup F _ _ 0 ?_ (hc _ 0) (hc _ 0)
    rw [chartPreOpen_inf, chartPreOpen_congr φ _ isOpen_empty (coordHalfPos_inter_coordHalfNeg k),
      chartPreOpen_empty]
    exact TopCat.Sheaf.subsingleton_H'_bot F 0
  have := contractibleSpace_chartPreOpen φ ht _ (isOpen_coordSlitPos k)
    (starConvex_coordSlitPos k) ⟨fun _ => 1, by simp [coordSlitPos]⟩
  have := contractibleSpace_chartPreOpen φ ht _ (isOpen_coordSlitNeg k)
    (starConvex_coordSlitNeg k) ⟨fun _ => -1, by simp [coordSlitNeg]⟩
  rw [chartPreOpen_congr φ _ ((isOpen_coordSlitPos k).union (isOpen_coordSlitNeg k))
    (coordSlitPos_union_coordSlitNeg k).symm, ← chartPreOpen_sup]
  refine TopCat.Sheaf.subsingleton_H'_sup F _ _ 1 ?_ (hc _ 1) (hc _ 1)
  rw [chartPreOpen_inf, chartPreOpen_congr φ _ ((isOpen_coordHalfPos k).union
    (isOpen_coordHalfNeg k)) (coordSlitPos_inter_coordSlitNeg k), ← chartPreOpen_sup]
  exact h1


/-- The `H²` step of `subsingleton_H'_three_compl_planeOrigin` is the case `n = 2`, `k = 0` of
`subsingleton_H'_two_chartPreOpen_coord_ne_zero` (`planeChartZeroOpen` is `chartPreOpen` of the
chart `x₀ ≠ 0` by `rfl`). -/
example : Subsingleton (Sheaf.H' planeConst 2 (planeChartOpen 0 ⊓ planeChartOpen 1)) := by
  rw [planeChartOpen_zero_inf_one]
  exact subsingleton_H'_two_chartPreOpen_coord_ne_zero projectivePlane (projectiveChart 2 0)
    (by rw [projectiveChart, affineChart_target]) 0

end HodgeLadder.Tests
