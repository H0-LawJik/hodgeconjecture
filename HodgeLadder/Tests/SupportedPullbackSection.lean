module

public import HodgeLadder.Supported.PullbackSection
public import HodgeLadder.Tests.SupportedPullback

/-!
# A nonzero instance of the pulled-back pair cocycle

Rung `supported-pullback-section`. `pullbackCocycle_supCocycle` holds at `x = 0` as `0 = 0`, so
it needs a nonzero instance. Along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support the whole space, some
relative cocycle `x` on ℙ¹(ℂ) in degree zero has `supCocycle (rawMap (relPullback x))` with
nonzero derived class: the supported pullback of `supportedPullback_prodFst_ne_zero` is named by
it, through `supportedPullback_named` and `pullbackCocycle_supCocycle`. Positive degrees and
proper supports are left to `supported-pullback-transport-test`.

## Main results

* `HodgeLadder.Tests.supCocycle_relPullback_prodFst_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint CochainComplex HomComplex
open HodgeLadder.Cup HodgeLadder.Supported

namespace HodgeLadder.Tests

/-- Upstream's `openParacompactSpace` on ℙ¹, as a local instance for the test below. -/
local instance projectiveLine_openParacompactSpace' :
    ∀ U : Opens (ComplexPoint projectiveLine), ParacompactSpace U :=
  openParacompactSpace projectiveLine

attribute [local instance] pointPullbackAdditive pointPullbackPreservesFiniteLimits
  pointPullbackPreservesFiniteColimits finHasDerivedCategory finSiteHasDerivedCategory
  p1p1_openParacompactSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **Non-vacuity of `pullbackCocycle_supCocycle`**: along pr₁ : ℙ¹ × ℙ¹ ⟶ ℙ¹, with support
the whole space, some relative cocycle `x` on ℙ¹(ℂ) has `supCocycle (rawMap (relPullback x))`
with nonzero derived class in degree zero. -/
theorem supCocycle_relPullback_prodFst_ne_zero :
    ∃ (x : RelCochain projectiveLine ⊤ 0)
      (hx : (relSeq (TopCat.of (ComplexPoint projectiveLine)) (⊤ : Closeds _).compl ⊤).X₁.d
        ((0 : ℕ) : ℤ) (((0 : ℕ) : ℤ) + 1) x = 0),
      ShiftedHom.map (Cocycle.equivHomShift.symm (supCocycle p1p1 ⊤
        ((rawMap (TopCat.of (ComplexPoint p1p1)) (⊤ : Closeds _).compl ⊤).τ₁.f ((0 : ℕ) : ℤ)
          ((relPullback (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤ (Set.subset_univ _)).f
            ((0 : ℕ) : ℤ) x))
        (map_d_eq_zero _ _ (map_d_eq_zero _ x hx)))) DerivedCategory.Q ≠ 0 := by
  obtain ⟨α, hα0⟩ := supportedPullback_prodFst_ne_zero
  obtain ⟨x, hx, -, hα⟩ := exists_supported_rep projectiveLine ⊤ α
  have hz := supportedPullback_named (prod.fst : p1p1 ⟶ projectiveLine) ⊤ ⊤
    (Set.subset_univ _) α _ hα
  rw [pullbackCocycle_supCocycle _ _ _ _ x hx] at hz
  refine ⟨x, hx, fun h0 => hα0 ?_⟩
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
