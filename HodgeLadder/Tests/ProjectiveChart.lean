module

public import HodgeLadder.Normalization.AffineChart
public import HodgeLadder.Tests.ProjectivePlane

/-!
# The standard affine charts of ℙⁿ are holomorphic charts

Rung `affine-chart-analytic-p2`, the instance of `affine-chart-analytic` that
`p2-lines-transversal` reads. Oka's chart `ProjectiveSpace.chart i : Spec ℂ[Y₀, …, Y_{n-1}] →
ℙₒ(n; ℂ)`, with `Yₘ = x_{i.succAbove m} / xᵢ`, followed by `okaIsoSpace n`, has image an open
`projectiveChartOpen n i` of upstream's ℙⁿ that is isomorphic to `𝔸ⁿ` over `Spec ℂ`
(`projectiveChartIso`). Its affine chart `projectiveChart n i` lies in the maximal analytic atlas
of ℙⁿ(ℂ) by the rung. The inverse chart sends `v` to the point with homogeneous coordinates
`Fin.insertNth i 1 v` (`projectiveChart_symm_underlying`, `projectiveChart_symm_mem_U_iff`); on
ℙ² at `i = 2` the coordinates are `(x₀ / x₂, x₁ / x₂)`. Convention row: "Algebraic affine chart
and the standard chart of ℙⁿ" in `docs/conventions.md`.

## Main definitions

* `HodgeLadder.Normalization.projectiveChartImmersion`, `projectiveChartOpen`,
  `projectiveChartSchemeIso`, `projectiveChartIso`, `projectiveChart`

## Main results

* `HodgeLadder.Normalization.projectiveChart_mem_maximalAtlas`,
  `HodgeLadder.Normalization.projectivePlane_chart_mem_maximalAtlas`
* `HodgeLadder.Normalization.projectiveChartOpen_eq`, `projectiveChartSchemeIso_over`
* `HodgeLadder.Normalization.projectiveChart_symm_underlying`,
  `HodgeLadder.Normalization.projectiveChart_symm_mem_U_iff`
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace HodgeLadder.Normalization

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint

section Projective

open HodgeLadder.Tests

/-- Oka's standard chart `xᵢ ≠ 0` of ℙⁿ, `Spec ℂ[Y₀, …, Y_{n-1}] → ℙₒ(n; ℂ)` with
`Yₘ = x_{i.succAbove m} / xᵢ`, followed by `okaIsoSpace n` into upstream's ℙⁿ. -/
def projectiveChartImmersion (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (MvPolynomial (Fin n) ℂ)) ⟶ (projectiveSpace n).left :=
  AlgebraicGeometry.ProjectiveSpace.chart i ≫ (okaIsoSpace n).hom

instance (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveChartImmersion n i) := by
  unfold projectiveChartImmersion
  infer_instance

/-- The standard open `xᵢ ≠ 0` of upstream's ℙⁿ: the image of the standard chart. -/
abbrev projectiveChartOpen (n : ℕ) (i : Fin (n + 1)) : (projectiveSpace n).left.Opens :=
  (projectiveChartImmersion n i).opensRange

/-- The standard open is the image of Oka's `D₊(xᵢ)` under `okaIsoSpace n`. -/
theorem projectiveChartOpen_eq (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartOpen n i =
      (okaIsoSpace n).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U n ℂ i :=
  (Scheme.Hom.opensRange_comp _ _).trans
    (congrArg _ (AlgebraicGeometry.ProjectiveSpace.opensRange_chart i))

/-- The scheme isomorphism from the standard open `xᵢ ≠ 0` of ℙⁿ to `𝔸ⁿ`. -/
def projectiveChartSchemeIso (n : ℕ) (i : Fin (n + 1)) :
    (projectiveChartOpen n i).toScheme ≅ complexAffineSpace (Fin n) :=
  (projectiveChartImmersion n i).isoOpensRange.symm ≪≫
    (AffineSpace.SpecIso (Fin n) (.of ℂ)).symm

/-- `projectiveChartSchemeIso` lies over `Spec ℂ`. -/
theorem projectiveChartSchemeIso_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveChartSchemeIso n i).hom ≫ (complexAffineSpace (Fin n) ↘ Spec ↧ℂ) =
      (projectiveChartOpen n i).ι ≫ (projectiveSpace n).hom := by
  have h := AlgebraicGeometry.ProjectiveSpace.chart_toSpec (R := ℂ) i
  have h2 := okaIsoSpace_hom_toBase n
  have h3 : (projectiveChartOpen n i).ι =
      (projectiveChartImmersion n i).isoOpensRange.inv ≫ projectiveChartImmersion n i :=
    (Scheme.Hom.isoOpensRange_inv_comp (projectiveChartImmersion n i)).symm
  have h4 : projectiveChartImmersion n i ≫ (projectiveSpace n).hom =
      Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    change (AlgebraicGeometry.ProjectiveSpace.chart i ≫ (okaIsoSpace n).hom) ≫ _ = _
    rw [Category.assoc, h2, h]
  rw [h3, Category.assoc, h4]
  simp [projectiveChartSchemeIso]

/-- The standard open `xᵢ ≠ 0` of ℙⁿ is `𝔸ⁿ` over `Spec ℂ`, through Oka's chart and Mathlib's
`AffineSpace.SpecIso`. -/
def projectiveChartIso (n : ℕ) (i : Fin (n + 1)) :
    openScheme (projectiveSpace n) (projectiveChartOpen n i) ≅
      Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ) :=
  Over.isoMk (projectiveChartSchemeIso n i) (projectiveChartSchemeIso_over n i)

/-- The standard affine chart `xᵢ ≠ 0` of upstream's ℙⁿ(ℂ), with coordinates
`x_{i.succAbove m} / xᵢ`. -/
def projectiveChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ComplexPoint (projectiveSpace n)) (Fin n → ℂ) :=
  affineChart (projectiveSpace n) (projectiveChartOpen n i) (projectiveChartIso n i)

/-- The standard affine chart of ℙⁿ(ℂ) lies in the maximal analytic atlas. -/
theorem projectiveChart_mem_maximalAtlas (n : ℕ) (i : Fin (n + 1)) :
    projectiveChart n i ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω (ComplexPoint (projectiveSpace n)) :=
  affineChart_mem_maximalAtlas _ _ _

/-- The inverse of the standard chart in Oka's terms: `v ∈ ℂⁿ` goes to the complex point whose
underlying point is Oka's chart applied to the point of `Spec ℂ[Y]` cut out by evaluation at `v`,
moved to upstream's ℙⁿ by `okaIsoSpace n`. With `chart_base_evalPoint_mem_U_iff` this is the point
with homogeneous coordinates `Fin.insertNth i 1 v`. -/
theorem projectiveChart_symm_underlying (n : ℕ) (i : Fin (n + 1)) (v : Fin n → ℂ) :
    ((projectiveChart n i).symm v).underlying =
      (okaIsoSpace n).hom.base ((AlgebraicGeometry.ProjectiveSpace.chart i).base
        (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ) v)) := by
  set z := (affineSpaceEquiv (Fin n)).symm v
  have h1 : ((projectiveChart n i).symm v).underlying =
      (projectiveChartImmersion n i).base
        ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying) := by
    change (Point.map (openInclusion _ _) (Point.map (projectiveChartIso n i).inv z)).underlying = _
    simp only [Point.underlying_map]
    change ((projectiveChartOpen n i).ι).base
      (((projectiveChartImmersion n i).isoOpensRange.hom).base
        ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying)) = _
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι]
  rw [h1]
  change (okaIsoSpace n).hom.base ((ProjectiveSpace.chart i).base _) = _
  congr 2
  apply PrimeSpectrum.ext
  ext P
  have key : ∀ s : Γ(Spec (.of (MvPolynomial (Fin n) ℂ)), ⊤),
      (AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.base z.underlying ∈
        (Spec (.of (MvPolynomial (Fin n) ℂ))).basicOpen s ↔
        MvPolynomial.eval v (affineGlobalPolynomial
          ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop s)) ≠ 0 := by
    intro s
    rw [← evaluate_affineSpaceEquiv_symm_top]
    rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := ⊤) _ z trivial]
    change _ ↔ z.underlying ∈ (complexAffineSpace (Fin n)).basicOpen _
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  have hP := key ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ))).inv P)
  rw [AlgebraicGeometry.basicOpen_eq_of_affine] at hP
  have hpoly : affineGlobalPolynomial ((AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ))).inv P)) = P := by
    rw [affineGlobalPolynomial]
    change ((Scheme.ΓSpecIso _).inv ≫ (AffineSpace.SpecIso (Fin n) (.of ℂ)).hom.appTop ≫
      (AffineSpace.SpecIso (Fin n) (.of ℂ)).inv.appTop ≫ (Scheme.ΓSpecIso _).hom) P = P
    rw [← Scheme.Hom.comp_appTop_assoc, Iso.inv_hom_id, Scheme.Hom.id_appTop]
    simp
  rw [hpoly] at hP
  change P ∈ _ ↔ P ∈ RingHom.ker _
  rw [RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
  have : (MvPolynomial.eval₂ (RingHom.id ℂ) v P) = MvPolynomial.eval v P := rfl
  rw [this]
  constructor
  · intro h; by_contra h'; exact (PrimeSpectrum.mem_basicOpen _ _).mp (hP.mpr h') h
  · intro h; by_contra h'; exact hP.mp ((PrimeSpectrum.mem_basicOpen _ _).mpr h') h

/-- The inverse chart at `v` lies over the standard open `xⱼ ≠ 0` exactly when coordinate `j` of
`Fin.insertNth i 1 v` is nonzero. On ℙ² at `i = 2`: in `U j` for `j = 0, 1` iff `v j ≠ 0`. -/
theorem projectiveChart_symm_mem_U_iff (n : ℕ) (i j : Fin (n + 1)) (v : Fin n → ℂ) :
    ((projectiveChart n i).symm v).underlying ∈
        (okaIsoSpace n).hom ''ᵁ AlgebraicGeometry.ProjectiveSpace.U n ℂ j ↔
      Fin.insertNth (α := fun _ => ℂ) i 1 v j ≠ 0 := by
  rw [projectiveChart_symm_underlying, Scheme.Hom.apply_mem_image_iff]
  have h := AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff (R := ℂ)
    (RingHom.id ℂ) i j (Fin.insertNth (α := fun _ => ℂ) i 1 v) (by simp)
  rwa [AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec_insertNth] at h

/-- The instance for `p2-lines-transversal`: each standard affine chart of ℙ²(ℂ) (at `i = 2` the
chart `x₂ ≠ 0` with coordinates `(x₀ / x₂, x₁ / x₂)`) lies in the maximal analytic atlas of
upstream's charted space on ℙ²(ℂ). -/
theorem projectivePlane_chart_mem_maximalAtlas (i : Fin 3) :
    projectiveChart 2 i ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω (ComplexPoint projectivePlane) :=
  projectiveChart_mem_maximalAtlas 2 i

end Projective

end HodgeLadder.Normalization
