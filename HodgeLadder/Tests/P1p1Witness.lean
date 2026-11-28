module

public import HodgeLadder.Tests.ProjectivePlane
public import HodgeLadder.General.ComplexPointProd
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import HodgeLadder.General.Segre

/-!
# ℙ¹ × ℙ¹ over ℂ satisfies the hypotheses of the statements of record

Rung `p1p1-witness`. The surface `p1p1 := projectiveLine ⨯ projectiveLine`, the categorical
product in `Over (Spec ↧ℂ)` used by `complex-points-prod`, is integral, smooth of relative
dimension two and projective in upstream's sense.

* Integrality. Oka's `ℙₒ(n; K)` is integral for every field `K` (the ℙⁿ proof over ℂ uses
  nothing else), so `ℙₒ(n; R) ⟶ Spec R` is geometrically integral for every ring `R`
  (`geometricallyIntegral_toSpec`, from Oka's base change `isPullback_map`), hence so is
  `projectiveLine.hom`. Mathlib's instance for fibre products of a geometrically integral, flat,
  universally open morphism with an integral locally noetherian scheme then gives
  `IsIntegral (pullback projectiveLine.hom projectiveLine.hom)`, and `Over.prodLeftIsoPullback`
  carries it to `p1p1.left`.
* Smoothness. `smoothOfRelativeDimension_prod` at `d = e = 1`, written `1 + 1`, and the instance
  `smooth_prod`.
* Projectivity. Upstream's `IsProjective` asks for a closed immersion into some `ℙ(Fin (d + 1);
  Spec ℂ)` over `Spec ℂ`. The Segre embedding `ℙ¹ × ℙ¹ ⟶ ℙ³` of `HodgeLadder.General.Segre`
  provides it (`exists_segre_oka`); `p1p1OkaIso` and `okaIsoSpace 3` transport it.
* Hausdorff complex points, from `pointProdHomeomorph` and upstream's instance on ℙ¹.

## Main definitions

* `HodgeLadder.Tests.p1p1`, `HodgeLadder.Tests.p1p1OkaIso`

## Main results

* `HodgeLadder.Tests.geometricallyIntegral_toSpec`, `geometricallyIntegral_projectiveLine`
* instances `IsIntegral p1p1.left`, `SmoothOfRelativeDimension 2 p1p1.hom`,
  `IsProjective p1p1.hom`, `T2Space (ComplexPoint p1p1)`
* `HodgeLadder.Tests.p1p1_witness`, `dim_p1p1`, `p1p1_openParacompactSpace`
* tests `nonempty_complexPoint_p1p1`, `pairEquiv_values`, `segreF_quadric`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Set TopologicalSpace

namespace HodgeLadder.Tests

/-! ### ℙⁿ over a field -/

section Field

variable (n : ℕ) (K : Type) [Field K]

/-- Over a field, the standard chart `x₀ ≠ 0` of ℙⁿ meets every standard chart: the point with
all homogeneous coordinates `1` lies in both. -/
theorem chart_zero_inter_nonempty_field (i : Fin (n + 1)) :
    (((AlgebraicGeometry.ProjectiveSpace.U n K 0 : ℙₒ(n; K).Opens) : Set ℙₒ(n; K)) ∩
      ((AlgebraicGeometry.ProjectiveSpace.U n K i : ℙₒ(n; K).Opens) : Set ℙₒ(n; K))).Nonempty := by
  let v : Fin (n + 1) → K := fun _ => 1
  let p := (AlgebraicGeometry.ProjectiveSpace.chart (R := K) (0 : Fin (n + 1))).base
    (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id K)
      (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 0 v))
  refine ⟨p, ?_, ?_⟩
  · rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart]
    exact ⟨_, rfl⟩
  · exact (AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff (RingHom.id K) 0 i v
      one_ne_zero).mpr one_ne_zero

/-- Oka's ℙⁿ over a field is reduced: its standard charts are spectra of polynomial rings. -/
instance isReduced_okaProjectiveSpace_field : IsReduced ℙₒ(n; K) := by
  have (i : (AlgebraicGeometry.ProjectiveSpace.affineOpenCover n K).openCover.I₀) :
      IsReduced ((AlgebraicGeometry.ProjectiveSpace.affineOpenCover n K).openCover.X i) :=
    inferInstanceAs (IsReduced (Spec (.of (MvPolynomial (Fin n) K))))
  exact IsReduced.of_openCover
    (𝒰 := (AlgebraicGeometry.ProjectiveSpace.affineOpenCover n K).openCover)

/-- Over a field, each standard chart of ℙⁿ is irreducible. -/
lemma isIrreducible_U_field (i : Fin (n + 1)) :
    IsIrreducible ((AlgebraicGeometry.ProjectiveSpace.U n K i : ℙₒ(n; K).Opens) :
      Set ℙₒ(n; K)) := by
  rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart, Scheme.Hom.coe_opensRange,
    ← image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (.of (MvPolynomial (Fin n) K)))).image _
    (AlgebraicGeometry.ProjectiveSpace.chart i).base.hom.continuous.continuousOn

/-- Oka's ℙⁿ over a field is irreducible. -/
instance irreducibleSpace_okaProjectiveSpace_field : IrreducibleSpace ℙₒ(n; K) := by
  refine irreducibleSpace_of_cover (AlgebraicGeometry.ProjectiveSpace.U n K 0).isOpen
    (isIrreducible_U_field n K 0) (isIrreducible_U_field n K) ?_
    (chart_zero_inter_nonempty_field n K)
  have h := AlgebraicGeometry.ProjectiveSpace.iSup_U n K
  rw [← Opens.coe_iSup, h, Opens.coe_top]

/-- Oka's ℙⁿ over a field is integral (the ℂ proof of `p2-witness`, for any field). -/
instance isIntegral_okaProjectiveSpace_field : IsIntegral ℙₒ(n; K) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end Field

/-! ### Geometric integrality of ℙ¹ -/

/-- Oka's `ℙₒ(n; R) ⟶ Spec R` is geometrically integral for every ring `R`: its base change to a
field `K` is `ℙₒ(n; K)` (Oka's `isPullback_map`), which is integral. -/
theorem geometricallyIntegral_toSpec (n : ℕ) (R : Type) [CommRing R] :
    GeometricallyIntegral (AlgebraicGeometry.ProjectiveSpace.toSpec n R) := by
  refine ⟨geometrically_iff_of_commRing.mpr fun K _ _ Y fst snd h => ?_⟩
  have e := h.isoIsPullback _ _ (AlgebraicGeometry.ProjectiveSpace.isPullback_map (n := n)
    (algebraMap R K))
  have : Nonempty Y := ⟨e.inv.base (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- Upstream's structure morphism of ℙ¹ is Oka's, through `okaIso`. -/
theorem projectiveLine_hom_eq :
    projectiveLine.hom = okaIso.inv ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ := by
  rw [Iso.eq_inv_comp]; exact isPullback_projectiveLine.isoPullback_hom_fst

/-- Upstream's ℙ¹ is geometrically integral over `Spec ℂ`. -/
instance geometricallyIntegral_projectiveLine : GeometricallyIntegral projectiveLine.hom := by
  rw [projectiveLine_hom_eq]
  refine ⟨fun K _ y Z fst snd hpb => (geometricallyIntegral_toSpec 1 ℂ).1 y (fst ≫ okaIso.inv)
    snd (hpb.of_iso (Iso.refl _) okaIso.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp))⟩

/-- Upstream's ℙ¹ is locally noetherian (locally of finite type over `Spec ℂ`). -/
instance isLocallyNoetherian_projectiveLine : IsLocallyNoetherian projectiveLine.left :=
  LocallyOfFiniteType.isLocallyNoetherian projectiveLine.hom

/-! ### The surface -/

open HodgeLadder.ComplexPointProd

/-- ℙ¹ × ℙ¹ over ℂ: the categorical product of `projectiveLine` with itself in `Over (Spec ℂ)`,
the spelling of `complex-points-prod`. -/
noncomputable abbrev p1p1 : Over (Spec ↧ℂ) := projectiveLine ⨯ projectiveLine

/-- The fibre product `ℙ¹ ×_ℂ ℙ¹` is integral (Mathlib's instance for a geometrically integral,
flat, universally open factor over an integral locally noetherian one). -/
instance isIntegral_pullback_p1p1 :
    IsIntegral (pullback projectiveLine.hom projectiveLine.hom) := inferInstance

/-- ℙ¹ × ℙ¹ is nonempty. -/
instance nonempty_p1p1 : Nonempty p1p1.left :=
  ⟨(Over.prodLeftIsoPullback projectiveLine projectiveLine).inv.base
    (Classical.arbitrary ↥(pullback projectiveLine.hom projectiveLine.hom))⟩

/-- ℙ¹ × ℙ¹ is integral. -/
instance isIntegral_p1p1 : IsIntegral p1p1.left :=
  isIntegral_of_isOpenImmersion (Over.prodLeftIsoPullback projectiveLine projectiveLine).hom

/-- ℙ¹ × ℙ¹ is smooth of relative dimension two, from `smoothOfRelativeDimension_prod` at
`1 + 1`. -/
instance smoothOfRelativeDimension_p1p1 : SmoothOfRelativeDimension 2 p1p1.hom :=
  inferInstanceAs (SmoothOfRelativeDimension (1 + 1) _)

/-- ℙ¹ × ℙ¹ is smooth (the instance `smooth_prod`). -/
theorem smooth_p1p1 : Smooth p1p1.hom := inferInstance

/-- The complex points of ℙ¹ × ℙ¹ are Hausdorff: `pointProdHomeomorph` and upstream's instance on
ℙ¹. -/
instance t2Space_p1p1 : T2Space (ComplexPoint p1p1) :=
  (pointProdHomeomorph projectiveLine projectiveLine).symm.t2Space

/-! ### Projectivity -/

/-- The Segre embedding over any ring: a closed immersion `ℙ¹ ×_R ℙ¹ ⟶ ℙ³` over `Spec R`
(`HodgeLadder.Segre.segre`). -/
theorem exists_segre_oka (R : Type) [CommRing R] :
    ∃ s : pullback (AlgebraicGeometry.ProjectiveSpace.toSpec 1 R)
        (AlgebraicGeometry.ProjectiveSpace.toSpec 1 R) ⟶ ℙₒ(3; R),
      IsClosedImmersion s ∧ s ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 3 R =
        pullback.fst _ _ ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 1 R :=
  ⟨Segre.segre R, Segre.isClosedImmersion_segre R, Segre.segre_toSpec R⟩

/-- `ℙ¹ × ℙ¹` is the fibre product of two copies of Oka's `ℙₒ(1; ℂ)` over `Spec ℂ`. -/
noncomputable def p1p1OkaIso :
    p1p1.left ≅ pullback (AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ)
      (AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ) :=
  Over.prodLeftIsoPullback projectiveLine projectiveLine ≪≫
    asIso (pullback.map _ _ _ _ okaIso.inv okaIso.inv (𝟙 _)
      (by rw [Category.comp_id, projectiveLine_hom_eq])
      (by rw [Category.comp_id, projectiveLine_hom_eq]))

/-- `p1p1OkaIso` lies over `Spec ℂ`. -/
theorem p1p1OkaIso_hom_fst :
    p1p1OkaIso.hom ≫ pullback.fst _ _ ≫ AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ =
      p1p1.hom := by
  simp only [p1p1OkaIso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_fst_assoc,
    pullback.map]
  rw [← projectiveLine_hom_eq, Over.prodLeftIsoPullback_hom_fst_assoc]
  exact Over.w (prod.fst : p1p1 ⟶ projectiveLine)

/-- ℙ¹ × ℙ¹ is projective in upstream's sense: the Segre embedding into `ℙ(Fin (3 + 1); Spec ℂ)`,
transported by `p1p1OkaIso` and upstream's `okaIsoSpace 3`. -/
instance isProjective_p1p1 : IsProjective p1p1.hom := by
  obtain ⟨s, hs, hso⟩ := exists_segre_oka ℂ
  exact ⟨⟨{ ambientDimension := 3
            immersion := p1p1OkaIso.hom ≫ s ≫ (okaIsoSpace 3).hom
            immersion_toBase := by
              rw [Category.assoc, Category.assoc,
                show ProjectiveSpace.toBase (Fin (3 + 1)) (Spec ↧ℂ) = (projectiveSpace 3).hom
                  from rfl, okaIsoSpace_hom_toBase, hso, p1p1OkaIso_hom_fst] }⟩⟩

/-! ### The witness -/

/-- **Rung `p1p1-witness`.** ℙ¹ × ℙ¹ satisfies the scheme hypotheses of the statements of
record: integral, smooth of relative dimension two (hence smooth), and projective. -/
theorem p1p1_witness :
    IsIntegral p1p1.left ∧ SmoothOfRelativeDimension 2 p1p1.hom ∧ Smooth p1p1.hom ∧
      IsProjective p1p1.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Upstream's dimension of ℙ¹ × ℙ¹ is `2` (upstream's `SmoothOfRelativeDimension.dim_eq`). -/
theorem dim_p1p1 : TopologicalSpace.dim p1p1.left = 2 :=
  SmoothOfRelativeDimension.dim_eq (f := p1p1.hom) 2

/-- Every open subset of the complex points of ℙ¹ × ℙ¹ is paracompact (upstream's
`ComplexPoint.openParacompactSpace`). -/
theorem p1p1_openParacompactSpace :
    ∀ U : Opens (ComplexPoint p1p1), ParacompactSpace U :=
  ComplexPoint.openParacompactSpace p1p1

/-! ### Tests -/

/-- A complex point of ℙ¹: the origin of the standard chart `x₀ ≠ 0`. -/
noncomputable def projectiveLinePoint : ComplexPoint projectiveLine :=
  Over.homMk (Spec.map (CommRingCat.ofHom (MvPolynomial.eval (0 : Fin 1 → ℂ))) ≫
      AlgebraicGeometry.ProjectiveSpace.chart 0 ≫ okaIso.hom) (by
    change _ ≫ projectiveLine.hom = 𝟙 _
    rw [projectiveLine_hom_eq, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      AlgebraicGeometry.ProjectiveSpace.chart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext r
    simp)

/-- ℙ¹ × ℙ¹ has a complex point: the pair of origins, through `pointProdHomeomorph`. -/
instance nonempty_complexPoint_p1p1 : Nonempty (ComplexPoint p1p1) :=
  ⟨(pointProdHomeomorph projectiveLine projectiveLine).symm
    (projectiveLinePoint, projectiveLinePoint)⟩

/-- The coordinates of ℙ³ in the Segre map are ordered lexicographically:
`pairEquiv (k, l) = 2k + l`. -/
theorem pairEquiv_values :
    Segre.pairEquiv (0, 0) = 0 ∧ Segre.pairEquiv (0, 1) = 1 ∧ Segre.pairEquiv (1, 0) = 2 ∧
      Segre.pairEquiv (1, 1) = 3 := by
  decide

/-- The Segre coordinates satisfy the quadric relation `x₀ x₃ = x₁ x₂` on every piece. This is a
sanity check only: the pin of the map is `Segre.segreF_X` with `pairEquiv_values`. -/
theorem segreF_quadric (R : Type) [CommRing R] (a : Fin 2 × Fin 2) :
    Segre.segreF R a (MvPolynomial.X (Segre.pairEquiv (0, 0)) *
        MvPolynomial.X (Segre.pairEquiv (1, 1)) -
      MvPolynomial.X (Segre.pairEquiv (0, 1)) * MvPolynomial.X (Segre.pairEquiv (1, 0))) = 0 := by
  rw [map_sub, map_mul, map_mul, Segre.segreF_X, Segre.segreF_X, Segre.segreF_X, Segre.segreF_X]
  ring

end HodgeLadder.Tests
