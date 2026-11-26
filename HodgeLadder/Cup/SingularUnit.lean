module

public import HodgeLadder.Cup.Product
public import HodgeLadder.Cup.OneIsKappa
public import HodgeLadder.Cup.CupSingular
public import HodgeLadder.Cup.RelCupNaturality
public import Other.AlgebraicGeometry.Hodge.Filtration

/-!
# The unit of the singular cup product

Rung `singular-unit` (front `cup`, foundation of `fundamental-class-unit`). The class `oneSing Y`
of the constant `0`-cocycle with value `1`, moved from Tau Ceti's singular cohomology to upstream's
along `cohIso`, is a two-sided unit of `cupSing`, natural under pullback and nonzero on a nonempty
space. Upstream's comparison `Ψ = rationalCohomologyAddEquivSingularCohomology` sends the unit
`one X` of the Yoneda cup product to `oneSing`, with no sign; and `one X` is upstream's degree-zero
unit `fieldCohomologyUnit ℚ X`. Conventions: `docs/conventions.md`, rows "Singular cup product",
"Sheaf–singular comparison Ψ" and "Degree-zero orientation and the unit".

## Main definitions

* `HodgeLadder.Cup.oneSing`

## Main results

* `HodgeLadder.Cup.cupSing_oneSing`, `HodgeLadder.Cup.oneSing_cupSing`: the unit laws.
* `HodgeLadder.Cup.cohomologyMap_oneSing`, `HodgeLadder.Cup.oneSing_ne_zero`.
* `HodgeLadder.Cup.rationalCohomologyAddEquivSingularCohomology_one`: `Ψ (one X) = oneSing`.
* `HodgeLadder.Cup.one_eq_fieldCohomologyUnit`: `one X = fieldCohomologyUnit ℚ X`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicTopology.Singular
  AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLadder.Cup

/-- **The ladder's unit is upstream's degree-zero unit.** `one X = oneY` is the class of
`κ : ℤ_X → ℚ_X` (`one-is-kappa`); upstream's `fieldCohomologyUnit ℚ X` is the class of the
composite `ℤ_X → ℤ_X → ℚ_X` of the `ULift` equivalence and `n ↦ n • 1`. -/
theorem one_eq_fieldCohomologyUnit (X : Over (Spec ↧ℂ)) :
    one X = fieldCohomologyUnit ℚ X := by
  rw [one, oneY_eq_kappa, fieldCohomologyUnit, fieldCohomologyClass, kappaSheaf,
    uliftIntegerToIntegerConstantSheaf, integerToFieldConstantSheaf, ← Functor.map_comp]
  congr 2
  ext n
  simp [kappaAb]

/-- The class of the constant `0`-cocycle with value `1` in upstream's singular cohomology,
moved from Tau Ceti's along `cohIso`. -/
def oneSing (Y : TopCat.{0}) : AlgebraicTopology.Singular.Cohomology ℚ Y 0 :=
  (cohIso Y 0).inv
    ((Y.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).homologyπ 0
      (Y.constSingularCocycle ℚ (𝟙 (𝟙_ (ModuleCat.{0} ℚ)))))

/-- **Right unit law** for `cupSing`. -/
theorem cupSing_oneSing (Y : TopCat.{0}) {p : ℕ} (a : AlgebraicTopology.Singular.Cohomology ℚ Y p) :
    cupSing Y a (oneSing Y) p (add_zero p) = a := by
  unfold cupSing oneSing
  rw [Iso.inv_hom_id_apply]
  erw [TopCat.singularCup_constSingularCocycle_right Y ℚ (η := 𝟙 (𝟙_ (ModuleCat.{0} ℚ)))
    (by simp [unitors_inv_equal]) (by simp [unitors_equal]) (add_zero p)]
  exact Iso.hom_inv_id_apply _ _

/-- **Left unit law** for `cupSing`. -/
theorem oneSing_cupSing (Y : TopCat.{0}) {q : ℕ} (b : AlgebraicTopology.Singular.Cohomology ℚ Y q) :
    cupSing Y (oneSing Y) b q (zero_add q) = b := by
  unfold cupSing oneSing
  rw [Iso.inv_hom_id_apply]
  erw [TopCat.singularCup_constSingularCocycle_left Y ℚ (η := 𝟙 (𝟙_ (ModuleCat.{0} ℚ)))
    (by simp) (by simp) (zero_add q)]
  exact Iso.hom_inv_id_apply _ _

/-- Pullback preserves `oneSing`. -/
theorem cohomologyMap_oneSing {Y Y' : TopCat.{0}} (f : Y ⟶ Y') :
    cohomologyMap ℚ 0 f (oneSing Y') = oneSing Y := by
  apply (cohIso Y 0).toLinearEquiv.injective
  change (cohIso Y 0).hom _ = (cohIso Y 0).hom _
  have h : ∀ γ, (cohIso Y 0).hom (cohomologyMap ℚ 0 f γ) =
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{0} ℚ)) (k := ℚ) (M := 𝟙_ (ModuleCat.{0} ℚ))
        f 0 ((cohIso Y' 0).hom γ) :=
    fun γ => homologyMap_dualIsoYoneda_apply (singularChainComplexMap ℚ f) 0 γ
  rw [h, oneSing, oneSing, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  exact TopCat.singularCohomologyMap_homologyπ_constSingularCocycle f ℚ _

/-- `oneSing` is nonzero on a nonempty space. -/
theorem oneSing_ne_zero (Y : TopCat.{0}) [Nonempty Y] : oneSing Y ≠ 0 := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  intro h
  set K := Y.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))
  have h1 : K.homologyπ 0 (Y.constSingularCocycle ℚ (𝟙 (𝟙_ (ModuleCat.{0} ℚ)))) = 0 := by
    have := congrArg (cohIso Y 0).hom h
    rwa [oneSing, Iso.inv_hom_id_apply, map_zero] at this
  have hπ : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
  have h2 : Y.constSingularCocycle ℚ (𝟙 (𝟙_ (ModuleCat.{0} ℚ))) = 0 :=
    (ConcreteCategory.bijective_of_isIso (K.homologyπ 0)).1 (h1.trans (map_zero _).symm)
  have h3 := congrArg (K.iCycles 0) h2
  rw [TopCat.iCycles_constSingularCocycle, map_zero] at h3
  have h4 := congrArg (fun g => (TopCat.toSSet.obj Y).ιChainComplex
    (TopCat.toSSetObj₀Equiv.symm y) ≫ g) h3
  simp only [SSet.ιChainComplex_constCochain] at h4
  erw [Limits.comp_zero] at h4
  have h5 := ConcreteCategory.congr_hom h4 (1 : ℚ)
  exact one_ne_zero (α := ℚ) h5

/-- **`Ψ` sends the unit to the unit.** From `cup_singular_comparison` at `p = 0` (sign
`(−1)^0 = 1`): `Ψ (one ∪ w) = cupSing (Ψ one) (Ψ w)`; take `Ψ w = oneSing` and use the right unit
law. -/
theorem rationalCohomologyAddEquivSingularCohomology_one (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] :
    rationalCohomologyAddEquivSingularCohomology X 0 (one X) =
      oneSing (TopCat.of (ComplexPoint X)) := by
  obtain ⟨w, hw⟩ := (rationalCohomologyAddEquivSingularCohomology X 0).surjective
    (oneSing (TopCat.of (ComplexPoint X)))
  have h := cup_singular_comparison X (one X) w
  have h1 : cup (one X) w (0 + 0) rfl = w := one_cup w
  rw [h1] at h
  simp only [Nat.cast_zero, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul] at h
  have h2 := cupSing_oneSing (TopCat.of (ComplexPoint X))
    (rationalCohomologyAddEquivSingularCohomology X 0 (one X))
  rw [← hw] at h2
  exact h2.symm.trans (h.symm.trans hw)

end HodgeLadder.Cup
