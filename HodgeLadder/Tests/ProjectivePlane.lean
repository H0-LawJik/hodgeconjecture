module

public import HodgeLadder.Tests.ProjectiveLine
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-!
# ℙⁿ and ℙ² over ℂ satisfy the hypotheses of the statements of record

Rung `p2-witness`. Upstream's projective space `ProjectiveSpace.toBase (Fin (n + 1)) (Spec ℂ)`,
as an object of `Over (Spec ℂ)`, is integral, smooth of relative dimension `n`, and projective,
for every `n`. The plane `projectivePlane` is the case `n = 2`, written with `Fin 3` as in the
ledger. The proofs follow the ℙ¹ witness (`projective-line-witness`) with `n + 1` standard
charts in place of two.

Smoothness: upstream's structure morphism is a base change of `ℙₒ(n; ULift ℤ) ⟶ Spec (ULift ℤ)`,
smooth of relative dimension `n` by `smoothOfRelativeDimension_toSpec`. Projective: the identity
presentation. Integrality: `ℙₒ(n; ℂ)` is reduced (its charts are) and irreducible (every
standard chart is irreducible and meets the chart `x₀ ≠ 0`), and Oka's base change identifies it
with upstream's object.

The Hausdorff property of `ComplexPoint` comes from upstream
(`ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint`, and also
`IsProjective.complexPoint_t2Space`);
paracompactness of opens is upstream's `ComplexPoint.openParacompactSpace`, restated here for
`projectivePlane` so that consumers can install it as a local instance.

## Main definitions

* `HodgeLadder.Tests.projectiveSpace`, `HodgeLadder.Tests.projectivePlane`,
  `HodgeLadder.Tests.okaIsoSpace`

## Main results

* instances `IsIntegral (projectiveSpace n).left`, `SmoothOfRelativeDimension n
  (projectiveSpace n).hom`, `Smooth (projectiveSpace n).hom`, `IsProjective (projectiveSpace n).hom`
* `HodgeLadder.Tests.irreducibleSpace_of_cover`, `okaIsoSpace_hom_toBase`, `okaIsoSpace_hom_snd`
* `HodgeLadder.Tests.dim_projectiveSpace`, `relativeDimension_projectiveSpace_eq`
* `HodgeLadder.Tests.projectivePlane_witness`, `projectivePlane_t2Space`,
  `projectivePlane_openParacompactSpace`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial Set TopologicalSpace

namespace HodgeLadder.Tests

/-- ℙⁿ over ℂ in upstream's sense. -/
noncomputable abbrev projectiveSpace (n : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (_root_.ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))

/-- ℙ² over ℂ in upstream's sense, with `Fin 3` homogeneous coordinates. -/
noncomputable abbrev projectivePlane : Over (Spec ↧ℂ) :=
  Over.mk (_root_.ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))

/-- The plane is the case `n = 2` of `projectiveSpace`. -/
theorem projectivePlane_eq : projectivePlane = projectiveSpace 2 := rfl

/-! ### Smoothness and projectivity -/

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The structure morphism of upstream's integral `Proj` model of ℙⁿ is smooth of relative
dimension `n`. -/
theorem smooth_terminal_space (n : ℕ) :
    SmoothOfRelativeDimension n
      (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  have h : terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ))) =
      AlgebraicGeometry.ProjectiveSpace.toSpec n (ULift.{0} ℤ) ≫
        terminal.from (Spec (.of (ULift.{0} ℤ))) := terminal.hom_ext _ _
  rw [h]
  have := smoothOfRelativeDimension_toSpec n (ULift.{0} ℤ)
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- Upstream's ℙⁿ over ℂ is smooth of relative dimension `n`. -/
instance smoothOfRelativeDimension_projectiveSpace (n : ℕ) :
    SmoothOfRelativeDimension n (projectiveSpace n).hom := by
  have := smooth_terminal_space n
  change SmoothOfRelativeDimension n (pullback.fst _ _)
  infer_instance

/-- Upstream's ℙⁿ over ℂ is smooth. -/
instance smooth_projectiveSpace (n : ℕ) : Smooth (projectiveSpace n).hom :=
  SmoothOfRelativeDimension.smooth n _

/-- Upstream's ℙⁿ over ℂ is projective: the identity presentation. -/
instance isProjective_projectiveSpace (n : ℕ) : IsProjective (projectiveSpace n).hom :=
  ⟨⟨{ ambientDimension := n
      immersion := 𝟙 _
      immersion_toBase := Category.id_comp _ }⟩⟩

/-! ### Integrality -/

/-- A space with an irreducible open `U` and a cover by irreducible sets, each meeting `U`,
is irreducible. -/
theorem irreducibleSpace_of_cover {X ι : Type*} [TopologicalSpace X] {U : Set X} {V : ι → Set X}
    (hU : IsOpen U) (hUi : IsIrreducible U) (hVi : ∀ i, IsIrreducible (V i))
    (hcov : ⋃ i, V i = univ) (hUV : ∀ i, (U ∩ V i).Nonempty) : IrreducibleSpace X := by
  have h1 : ∀ i, V i ⊆ closure U := fun i =>
    (subset_closure_inter_of_isPreirreducible_of_isOpen (hVi i).2 hU
      (by rw [inter_comm]; exact hUV i)).trans (closure_mono inter_subset_right)
  have h2 : closure U = univ :=
    eq_univ_of_univ_subset (hcov ▸ iUnion_subset h1)
  have h3 := hUi.closure
  rw [h2] at h3
  exact (irreducibleSpace_def X).mpr h3

/-- The standard chart `x₀ ≠ 0` of ℙⁿ meets every standard chart `xᵢ ≠ 0`: the point with all
homogeneous coordinates `1` lies in both. -/
theorem chart_zero_inter_nonempty (n : ℕ) (i : Fin (n + 1)) :
    (((AlgebraicGeometry.ProjectiveSpace.U n ℂ 0 : ℙₒ(n; ℂ).Opens) : Set ℙₒ(n; ℂ)) ∩
      ((AlgebraicGeometry.ProjectiveSpace.U n ℂ i : ℙₒ(n; ℂ).Opens) : Set ℙₒ(n; ℂ))).Nonempty := by
  let v : Fin (n + 1) → ℂ := fun _ => 1
  let p := (AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin (n + 1))).base
    (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ)
      (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 0 v))
  refine ⟨p, ?_, ?_⟩
  · rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart]
    exact ⟨_, rfl⟩
  · exact (AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff (RingHom.id ℂ) 0 i v
      one_ne_zero).mpr one_ne_zero

/-- Oka's ℙⁿ over ℂ is reduced: its standard charts are spectra of polynomial rings. -/
instance isReduced_okaProjectiveSpace (n : ℕ) : IsReduced ℙₒ(n; ℂ) := by
  have (i : (AlgebraicGeometry.ProjectiveSpace.affineOpenCover n ℂ).openCover.I₀) :
      IsReduced ((AlgebraicGeometry.ProjectiveSpace.affineOpenCover n ℂ).openCover.X i) :=
    inferInstanceAs (IsReduced (Spec (.of (MvPolynomial (Fin n) ℂ))))
  exact IsReduced.of_openCover
    (𝒰 := (AlgebraicGeometry.ProjectiveSpace.affineOpenCover n ℂ).openCover)

/-- Each standard chart `xᵢ ≠ 0` of ℙⁿ over ℂ is irreducible, as the image of the irreducible
`Spec ℂ[Y₁, …, Yₙ]`. -/
lemma isIrreducible_U_space (n : ℕ) (i : Fin (n + 1)) :
    IsIrreducible ((AlgebraicGeometry.ProjectiveSpace.U n ℂ i : ℙₒ(n; ℂ).Opens) :
      Set ℙₒ(n; ℂ)) := by
  rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart, Scheme.Hom.coe_opensRange,
    ← image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (.of (MvPolynomial (Fin n) ℂ)))).image _
    (AlgebraicGeometry.ProjectiveSpace.chart i).base.hom.continuous.continuousOn

/-- Oka's ℙⁿ over ℂ is irreducible: the `n + 1` irreducible standard charts cover it and each
meets the chart `x₀ ≠ 0`. -/
instance irreducibleSpace_okaProjectiveSpace (n : ℕ) : IrreducibleSpace ℙₒ(n; ℂ) := by
  refine irreducibleSpace_of_cover (AlgebraicGeometry.ProjectiveSpace.U n ℂ 0).isOpen
    (isIrreducible_U_space n 0) (isIrreducible_U_space n) ?_ (chart_zero_inter_nonempty n)
  have h := AlgebraicGeometry.ProjectiveSpace.iSup_U n ℂ
  rw [← Opens.coe_iSup, h, Opens.coe_top]

/-- Oka's ℙⁿ over ℂ is integral. -/
instance isIntegral_okaProjectiveSpace (n : ℕ) : IsIntegral ℙₒ(n; ℂ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Oka's ℙⁿ over ℂ is the pullback defining upstream's ℙⁿ. -/
theorem isPullback_projectiveSpace (n : ℕ) :
    IsPullback (AlgebraicGeometry.ProjectiveSpace.toSpec n ℂ)
      (AlgebraicGeometry.ProjectiveSpace.map (n := n) intToComplex)
      (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  exact (AlgebraicGeometry.ProjectiveSpace.isPullback_map (n := n) intToComplex).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (terminal.from (Spec (.of (ULift.{0} ℤ)))))
    (by simp) (by simp) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The isomorphism `ℙₒ(n; ℂ) ≅ (projectiveSpace n).left`. -/
def okaIsoSpace (n : ℕ) : ℙₒ(n; ℂ) ≅ (projectiveSpace n).left :=
  (isPullback_projectiveSpace n).isoPullback

/-- `okaIsoSpace` lies over `Spec ℂ`: followed by upstream's structure morphism it is Oka's
structure morphism. -/
@[reassoc]
theorem okaIsoSpace_hom_toBase (n : ℕ) :
    (okaIsoSpace n).hom ≫ (projectiveSpace n).hom = AlgebraicGeometry.ProjectiveSpace.toSpec n ℂ :=
  (isPullback_projectiveSpace n).isoPullback_hom_fst

/-- The second projection of `okaIsoSpace` is Oka's coefficient change along `ULift ℤ → ℂ`,
which preserves the standard opens `D₊(xᵢ)`. -/
@[reassoc]
theorem okaIsoSpace_hom_snd (n : ℕ) :
    (okaIsoSpace n).hom ≫ pullback.snd _ _ =
      AlgebraicGeometry.ProjectiveSpace.map (n := n) intToComplex :=
  (isPullback_projectiveSpace n).isoPullback_hom_snd

/-- Upstream's ℙⁿ over ℂ is integral. -/
instance isIntegral_projectiveSpace (n : ℕ) : IsIntegral (projectiveSpace n).left :=
  have : Nonempty (projectiveSpace n).left :=
    ⟨((okaIsoSpace n).hom).base (Classical.arbitrary ℙₒ(n; ℂ))⟩
  isIntegral_of_isOpenImmersion (okaIsoSpace n).inv

/-- Upstream's dimension of ℙⁿ over ℂ is `n` (upstream's `SmoothOfRelativeDimension.dim_eq`). -/
theorem dim_projectiveSpace (n : ℕ) : TopologicalSpace.dim (projectiveSpace n).left = n :=
  SmoothOfRelativeDimension.dim_eq (f := (projectiveSpace n).hom) n

/-- The relative dimension of ℙⁿ over ℂ is unique: any `d` with `SmoothOfRelativeDimension d`
is `n`. -/
theorem relativeDimension_projectiveSpace_eq (n d : ℕ)
    [SmoothOfRelativeDimension d (projectiveSpace n).hom] : d = n :=
  (SmoothOfRelativeDimension.dim_eq (f := (projectiveSpace n).hom) d).symm.trans
    (dim_projectiveSpace n)

/-! ### The plane -/

/-- ℙ² over ℂ satisfies the scheme hypotheses of the statements of record: integral, smooth of
relative dimension two (hence smooth), and projective. -/
theorem projectivePlane_witness :
    IsIntegral projectivePlane.left ∧ SmoothOfRelativeDimension 2 projectivePlane.hom ∧
      Smooth projectivePlane.hom ∧ IsProjective projectivePlane.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The complex points of ℙ² are Hausdorff (upstream's instance
`ComplexProjectiveSpace.instT2SpaceProjectiveSpaceComplexPoint`). -/
theorem projectivePlane_t2Space : T2Space (ComplexPoint projectivePlane) := inferInstance

/-- Every open subset of the complex points of ℙ² is paracompact (upstream's
`ComplexPoint.openParacompactSpace`). -/
theorem projectivePlane_openParacompactSpace :
    ∀ U : Opens (ComplexPoint projectivePlane), ParacompactSpace U :=
  ComplexPoint.openParacompactSpace projectivePlane

end HodgeLadder.Tests
