module

public import LefschetzPort.Oka.AlgebraicGeometry.ProjectiveSpace.Points
public import LefschetzPort.Oka.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Analysis.Complex.Basic

/-!
# ℙ¹ over ℂ satisfies the hypotheses of the statements of record

Rung `projective-line-witness`. Upstream's projective line `ProjectiveSpace.toBase (Fin 2)
(Spec ℂ)`, as an object of `Over (Spec ℂ)`, is integral, smooth of relative dimension one, and
projective. Smoothness: the standard charts of `ℙₒ(n; R) = Proj R[X₀, …, Xₙ]` are spectra of
polynomial rings in `n` variables, standard smooth of relative dimension `n`, and upstream's
structure morphism is a base change of `ℙₒ(1; ULift ℤ) ⟶ Spec (ULift ℤ)`. Integrality: the base
change `ℙₒ(1; ℂ)` is reduced (its charts are) and irreducible (two irreducible charts that cover
and meet), and it is isomorphic to upstream's object.

## Main definitions

* `HodgeLadder.Tests.projectiveLine`, `HodgeLadder.Tests.okaIso`

## Main results

* `HodgeLadder.Tests.smoothOfRelativeDimension_toSpec`, `isIntegral_okaProjectiveLine`
* instances `IsIntegral projectiveLine.left`, `SmoothOfRelativeDimension 1 projectiveLine.hom`,
  `Smooth projectiveLine.hom`, `IsProjective projectiveLine.hom`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial RingHom Set

namespace HodgeLadder.Tests

/-- Oka's projective `n`-space over any ring is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_toSpec (n : ℕ) (R : Type) [CommRing R] :
    SmoothOfRelativeDimension n (AlgebraicGeometry.ProjectiveSpace.toSpec n R) := by
  have hP : HasRingHomProperty (@SmoothOfRelativeDimension.{0} n)
      (Locally (IsStandardSmoothOfRelativeDimension n)) := inferInstance
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ hP
  apply IsZariskiLocalAtSource.of_openCover
    (AlgebraicGeometry.ProjectiveSpace.affineOpenCover n R).openCover
  intro (i : Fin (n + 1))
  change SmoothOfRelativeDimension n (AlgebraicGeometry.ProjectiveSpace.chart i ≫ _)
  rw [AlgebraicGeometry.ProjectiveSpace.chart_toSpec, @HasRingHomProperty.Spec_iff _ _ hP]
  apply locally_of
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · show (algebraMap R (MvPolynomial (Fin n) R)).IsStandardSmoothOfRelativeDimension n
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance

/-- ℙ¹ over ℂ in upstream's sense. -/
noncomputable abbrev projectiveLine : Over (Spec ↧ℂ) :=
  Over.mk (_root_.ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The structure morphism of upstream's integral `Proj` model of ℙ¹. -/
theorem smooth_terminal :
    SmoothOfRelativeDimension 1
      (terminal.from (Proj (homogeneousSubmodule (Fin 2) (ULift.{0} ℤ)))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  have h : terminal.from (Proj (homogeneousSubmodule (Fin 2) (ULift.{0} ℤ))) =
      AlgebraicGeometry.ProjectiveSpace.toSpec 1 (ULift.{0} ℤ) ≫
        terminal.from (Spec (.of (ULift.{0} ℤ))) := terminal.hom_ext _ _
  rw [h]
  have := smoothOfRelativeDimension_toSpec 1 (ULift.{0} ℤ)
  exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0) _)

instance : SmoothOfRelativeDimension 1 projectiveLine.hom := by
  have := smooth_terminal
  change SmoothOfRelativeDimension 1 (pullback.fst _ _)
  infer_instance

instance : Smooth projectiveLine.hom := SmoothOfRelativeDimension.smooth 1 _

instance : IsProjective projectiveLine.hom :=
  ⟨⟨{ ambientDimension := 1
      immersion := 𝟙 _
      immersion_toBase := Category.id_comp _ }⟩⟩


/-- A space covered by two irreducible open sets that meet is irreducible. -/
theorem irreducibleSpace_of_two {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hUi : IsIrreducible U) (hVi : IsIrreducible V)
    (hcov : U ∪ V = univ) (hUV : (U ∩ V).Nonempty) : IrreducibleSpace X := by
  have h1 : V ⊆ closure U :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hVi.2 hU
      (by rwa [inter_comm])).trans (closure_mono inter_subset_right)
  have h2 : closure U = univ :=
    eq_univ_of_univ_subset (hcov ▸ union_subset subset_closure h1)
  have h3 := hUi.closure
  rw [h2] at h3
  exact (irreducibleSpace_def X).mpr h3

/-- The two standard charts of ℙ¹ meet. -/
theorem chart_nonempty_inter :
    (((AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 0 : ℙₒ(1; ℂ).Opens) : Set ℙₒ(1; ℂ)) ∩
      ((AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 1 : ℙₒ(1; ℂ).Opens) : Set ℙₒ(1; ℂ))).Nonempty := by
  let v : Fin 2 → ℂ := fun _ => 1
  let p := (AlgebraicGeometry.ProjectiveSpace.chart (R := ℂ) (0 : Fin 2)).base
    (AlgebraicGeometry.ProjectiveSpace.evalPoint (RingHom.id ℂ)
      (AlgebraicGeometry.ProjectiveSpace.dehomogenizeVec 0 v))
  refine ⟨p, ?_, ?_⟩
  · rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart]
    exact ⟨_, rfl⟩
  · exact (AlgebraicGeometry.ProjectiveSpace.chart_base_evalPoint_mem_U_iff (RingHom.id ℂ) 0 1 v
      one_ne_zero).mpr one_ne_zero

/-- Oka's ℙ¹ over ℂ is reduced. -/
instance isReduced_P1 : IsReduced ℙₒ(1; ℂ) := by
  have (i : (AlgebraicGeometry.ProjectiveSpace.affineOpenCover 1 ℂ).openCover.I₀) :
      IsReduced ((AlgebraicGeometry.ProjectiveSpace.affineOpenCover 1 ℂ).openCover.X i) :=
    inferInstanceAs (IsReduced (Spec (.of (MvPolynomial (Fin 1) ℂ))))
  exact IsReduced.of_openCover (𝒰 := (AlgebraicGeometry.ProjectiveSpace.affineOpenCover 1 ℂ).openCover)

/-- Each standard chart of ℙ¹ is irreducible. -/
lemma isIrreducible_U (i : Fin 2) :
    IsIrreducible ((AlgebraicGeometry.ProjectiveSpace.U 1 ℂ i : ℙₒ(1; ℂ).Opens) : Set ℙₒ(1; ℂ)) := by
  rw [← AlgebraicGeometry.ProjectiveSpace.opensRange_chart, Scheme.Hom.coe_opensRange,
    ← image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (.of (MvPolynomial (Fin 1) ℂ)))).image _
    (AlgebraicGeometry.ProjectiveSpace.chart i).base.hom.continuous.continuousOn

/-- Oka's ℙ¹ over ℂ is irreducible. -/
instance irreducibleSpace_P1 : IrreducibleSpace ℙₒ(1; ℂ) := by
  refine irreducibleSpace_of_two (AlgebraicGeometry.ProjectiveSpace.U 1 ℂ 0).isOpen
    (isIrreducible_U 0) (isIrreducible_U 1) ?_ chart_nonempty_inter
  have h := AlgebraicGeometry.ProjectiveSpace.iSup_U 1 ℂ
  ext x
  simp only [mem_union, SetLike.mem_coe, mem_univ, iff_true]
  have hx : x ∈ (⨆ i, AlgebraicGeometry.ProjectiveSpace.U 1 ℂ i) := h ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- Oka's ℙ¹ over ℂ is integral. -/
instance isIntegral_okaProjectiveLine : IsIntegral ℙₒ(1; ℂ) := isIntegral_of_irreducibleSpace_of_isReduced _

/-- The ring map `ULift ℤ → ℂ`. -/
abbrev intToComplex : ULift.{0} ℤ →+* ℂ := (Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Oka's ℙ¹ over ℂ is the pullback defining upstream's ℙ¹. -/
theorem isPullback_projectiveLine :
    IsPullback (AlgebraicGeometry.ProjectiveSpace.toSpec 1 ℂ)
      (AlgebraicGeometry.ProjectiveSpace.map (n := 1) intToComplex)
      (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (homogeneousSubmodule (Fin 2) (ULift.{0} ℤ)))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  exact (AlgebraicGeometry.ProjectiveSpace.isPullback_map (n := 1) intToComplex).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (terminal.from (Spec (.of (ULift.{0} ℤ)))))
    (by simp) (by simp) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The isomorphism `ℙₒ(1; ℂ) ≅ projectiveLine.left`. -/
def okaIso : ℙₒ(1; ℂ) ≅ projectiveLine.left := isPullback_projectiveLine.isoPullback

instance : Nonempty projectiveLine.left :=
  ⟨(okaIso.hom).base (Classical.arbitrary ℙₒ(1; ℂ))⟩

instance : IsIntegral projectiveLine.left := isIntegral_of_isOpenImmersion okaIso.inv

end HodgeLadder.Tests
