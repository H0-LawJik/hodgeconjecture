module

public import HodgeLadder.Supported.Pullback
public import HodgeLadder.Cup.SingularUnit
public import HodgeLadder.Tests.P1p1Witness
public import HodgeLadder.Supported.PullbackNamed

/-!
# Degree-zero tests of the supported pullback

Rung `supported-class-pullback-test`. With support the whole space, the supported pullback of
rung `supported-class-pullback` sends a lift of the unit of `H⁰(X; ℚ)` to a lift of the unit of
`H⁰(X'; ℚ)`, so it is nonzero on a smooth integral `X'` with a complex point; the last test
instantiates this on pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, the morphism `fibre-class-pullback` first uses.
`pullbackCocycle_prodFst_ne_zero` tests rung `supported-pullback-named` on the same morphism: some
pulled-back pair cocycle has nonzero derived class, so neither `pullbackCocycle` nor
`supportedPullback_named` is trivially zero there. Positive degrees and supports other than the
whole space are untested here.

## Main results

* `HodgeLadder.Tests.exists_forgetSupport_supportedPullback_eq_one`
* `HodgeLadder.Tests.supportedPullback_top_ne_zero`
* `HodgeLadder.Tests.supportedPullback_prodFst_ne_zero`
* `HodgeLadder.Tests.pullbackCocycle_prodFst_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint CochainComplex HomComplex
open HodgeLadder.Cup HodgeLadder.Supported

namespace HodgeLadder.Tests

section

variable {X X' : Over (Spec ↧ℂ)} (g : X' ⟶ X)

/-- **Non-vacuity in degree zero**: with support the whole space, a supported class lifting the
unit of `H⁰(X; ℚ)` pulls back to a supported class lifting the unit of `H⁰(X'; ℚ)`. -/
theorem exists_forgetSupport_supportedPullback_eq_one :
    ∃ α : H_[⊤]^0(X; ℚ), forgetSupport ℚ X ⊤ 0 α = one X ∧
      forgetSupport ℚ X' ⊤ 0 (supportedPullback g ⊤ ⊤ (Set.subset_univ _) 0 α) = one X' := by
  obtain ⟨α, hα⟩ := forgetSupport_surjective_of_eq_top (X := X) ⊤ rfl 0 (one X)
  exact ⟨α, hα, by rw [forgetSupport_supportedPullback, hα, pullbackCoh_one]⟩

/-- **Non-vacuity**: on a smooth integral `X'` with nonempty complex points (and upstream's
point-set hypotheses for the sheaf–singular comparison), the supported pullback with support the
whole space is nonzero in degree zero. -/
theorem supportedPullback_top_ne_zero [IsIntegral X'.left] [Smooth X'.hom]
    [T2Space (ComplexPoint X')] [∀ U : Opens (ComplexPoint X'), ParacompactSpace U]
    [Nonempty (ComplexPoint X')] :
    ∃ α : H_[⊤]^0(X; ℚ), supportedPullback g ⊤ ⊤ (Set.subset_univ _) 0 α ≠ 0 := by
  obtain ⟨α, -, h⟩ := exists_forgetSupport_supportedPullback_eq_one g
  refine ⟨α, fun h0 => oneSing_ne_zero (TopCat.of (ComplexPoint X')) ?_⟩
  rw [← rationalCohomologyAddEquivSingularCohomology_one X', ← h, h0, map_zero, map_zero]


end

attribute [local instance] p1p1_openParacompactSpace in
/-- **Non-vacuity on the first use**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support the whole space,
the supported pullback is nonzero in degree zero. -/
theorem supportedPullback_prodFst_ne_zero :
    ∃ α : H_[⊤]^0(projectiveLine; ℚ),
      supportedPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) 0 α ≠ 0 :=
  supportedPullback_top_ne_zero _

/-- Upstream's `openParacompactSpace` on ℙ¹, as a local instance for the test below. -/
local instance projectiveLine_openParacompactSpace :
    ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory
  p1p1_openParacompactSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **Non-vacuity of `supportedPullback_named`**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support the
whole space, some pulled-back pair cocycle has nonzero derived class in degree zero. -/
theorem pullbackCocycle_prodFst_ne_zero :
    ∃ z : PairCocycle projectiveLine ⊤ 0,
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (pullbackCocycle (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _) z))
        DerivedCategory.Q ≠ 0 := by
  obtain ⟨α, hα⟩ := supportedPullback_prodFst_ne_zero
  obtain ⟨z, hz⟩ := exists_named_supportedPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤
    (Set.subset_univ _) α
  refine ⟨z, fun h0 => hα ?_⟩
  rw [h0] at hz
  have : Smooth p1p1.hom := smooth_p1p1
  have : QuasiIso (iotaQ p1p1) := iotaQ_quasiIso p1p1
  have : IsIso (DerivedCategory.Q.map (iotaQ p1p1)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have h1 := (Preadditive.IsIso.comp_right_eq_zero _ _).1 hz
  apply Abelian.Ext.homAddEquiv.injective
  rw [map_zero]
  exact h1

end HodgeLadder.Tests
