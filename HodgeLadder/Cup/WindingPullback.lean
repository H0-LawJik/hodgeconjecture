module

public import HodgeLadder.Cup.WindingTorus
public import LefschetzPort.AlgebraicGeometry.ChernWindingCohomologyNaturality

/-!
# Pullback and additivity of winding classes, on any space

Rung `winding-class-pullback` (issue #267, sketch `docs/sketches/torus-singular-cohomology.md`,
order 5). Everything here is singular: upstream's `AlgebraicTopology.Singular.Cohomology ℚ` and
its pullback `cohomologyMap`. The sheaf-singular comparison `Ψ` does not enter.

For a nowhere vanishing `g : C(Y, ℂ)` let `[g] ∈ H¹(Y; ℚ)` be its winding class
(`HodgeLadder.Cup.windingClass`). Then, exactly and with no scalar:

* `f^* [g] = [g ∘ f]` for every continuous `f : Y' ⟶ Y` (`windingClass_comp`);
* `[g g'] = [g] + [g']` (`windingClass_mul`), `[g] = 0` when `g = 1`, and `[k] = −[g]` when
  `k g = 1`.

The first comes from identifying `windingClass g hg` with the port's
`ChernWinding.rationalWindingCohomologyClass g hg`
(`windingClass_eq_rationalWindingCohomologyClass`: the two cocycles are the same cochain
`rationalWindingCochain g hg` read through `dualIsoYoneda`) and the port's naturality of that
class. The second is additivity of the complex winding cochain.

For a homeomorphism `h : Y ≃ₜ X`, pullback `h^*` is a linear equivalence
`H^k(X; ℚ) ≃ H^k(Y; ℚ)` (`cohomologyEquivOfHomeomorph`), with inverse the pullback along
`h.symm`, from upstream's `cohomologyMap_comp` and `cohomologyMap_id`.

## Main definitions

* `HodgeLadder.Cup.cohomologyEquivOfHomeomorph`: `h^*` as a linear equivalence.

## Main results

* `HodgeLadder.Cup.windingClass_eq_rationalWindingCohomologyClass`,
  `HodgeLadder.Cup.windingClass_comp`, `HodgeLadder.Cup.windingClass_mul`,
  `HodgeLadder.Cup.windingClass_of_eq_one`, `HodgeLadder.Cup.windingClass_eq_neg_of_mul_eq_one`,
  `HodgeLadder.Cup.windingClass_ext`; helpers `HodgeLadder.Cup.cocycleOf_add`,
  `HodgeLadder.Cup.windingTC_mul`.
* `HodgeLadder.Cup.cohomologyEquivOfHomeomorph_apply`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLadder.Cup

variable {Y Y' : TopCat.{0}}

/-- **The winding class is the port's rational winding class**: `windingClass g hg` and
`ChernWinding.rationalWindingCohomologyClass g hg` are the same element of `H¹(Y; ℚ)`. Both are
the class of the cochain `rationalWindingCochain g hg`, read through `dualIsoYoneda`. -/
theorem windingClass_eq_rationalWindingCohomologyClass (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    windingClass g hg = ChernWinding.rationalWindingCohomologyClass g hg := by
  apply (cohIso Y 1).toLinearEquiv.injective
  change (cohIso Y 1).hom ((cohIso Y 1).inv _) = (cohIso Y 1).hom _
  rw [Iso.inv_hom_id_apply]
  change _ = HomologicalComplex.homologyMap (dualIsoYoneda _).hom 1
    ((ChernWinding.singularChains Y).linearDualCochainComplex.homologyπ 1
      (ChernWinding.rationalWindingCocycle g hg))
  rw [windingClassTC]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (dualIsoYoneda (SingularChainComplex ℚ Y)).hom 1)
    (ChernWinding.rationalWindingCocycle g hg)
  change _ = (ConcreteCategory.hom
        (HomologicalComplex.homologyπ (HomologicalComplex.linearDualCochainComplex
          (SingularChainComplex ℚ Y)) 1 ≫
          HomologicalComplex.homologyMap (dualIsoYoneda (SingularChainComplex ℚ Y)).hom 1))
      (ChernWinding.rationalWindingCocycle g hg)
  rw [h]
  change _ = (tcCochains Y).homologyπ 1 (HomologicalComplex.cyclesMap
    (dualIsoYoneda (SingularChainComplex ℚ Y)).hom 1 (ChernWinding.rationalWindingCocycle g hg))
  congr 1
  apply (ModuleCat.mono_iff_injective ((tcCochains Y).iCycles 1)).mp inferInstance
  rw [iCycles_cocycleOf]
  have h2 := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (dualIsoYoneda (SingularChainComplex ℚ Y)).hom 1)
    (ChernWinding.rationalWindingCocycle g hg)
  refine Eq.trans ?_ h2.symm
  change windingTC g hg = (dualIsoYoneda (SingularChainComplex ℚ Y)).hom.f 1
    ((ChernWinding.singularChains Y).linearDualCochainComplex.iCycles 1
      (ChernWinding.rationalWindingCocycle g hg))
  rw [ChernWinding.iCycles_rationalWindingCocycle]
  rfl

/-- **Pullback of a winding class**: `f^* [g] = [g ∘ f]` in `H¹(Y'; ℚ)`, exact, no sign. -/
theorem windingClass_comp (f : Y' ⟶ Y) (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    cohomologyMap ℚ 1 f (windingClass g hg) =
      windingClass (g.comp f.hom) (fun y => hg (f y)) := by
  rw [windingClass_eq_rationalWindingCohomologyClass,
    windingClass_eq_rationalWindingCohomologyClass]
  exact ChernWinding.rationalWindingCohomologyClass_naturality g hg f _

/-- `cocycleOf` is additive. -/
theorem cocycleOf_add {n : ℕ} (φ ψ : (tcCochains Y).X n) (hφ : (tcCochains Y).d n (n + 1) φ = 0)
    (hψ : (tcCochains Y).d n (n + 1) ψ = 0) (hφψ : (tcCochains Y).d n (n + 1) (φ + ψ) = 0) :
    cocycleOf (φ + ψ) hφψ = cocycleOf φ hφ + cocycleOf ψ hψ := by
  apply (ModuleCat.mono_iff_injective ((tcCochains Y).iCycles n)).mp inferInstance
  rw [map_add, iCycles_cocycleOf, iCycles_cocycleOf, iCycles_cocycleOf]

/-- The rational winding cochain of a product is the sum of the two cochains. -/
theorem windingTC_mul (g g' : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hg' : ∀ y, g' y ≠ 0) :
    windingTC (g * g') (fun y => mul_ne_zero (hg y) (hg' y)) = windingTC g hg + windingTC g' hg' :=
  ChernWinding.rationalWindingCochain_mul g hg g' (g * g') hg' _ (fun _ => rfl)

/-- **The winding class is additive**: `[g g'] = [g] + [g']`, exact, no sign. -/
theorem windingClass_mul (g g' : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hg' : ∀ y, g' y ≠ 0) :
    windingClass (g * g') (fun y => mul_ne_zero (hg y) (hg' y)) =
      windingClass g hg + windingClass g' hg' := by
  unfold windingClass windingClassTC
  rw [← map_add, ← map_add]
  congr 2
  rw [← cocycleOf_add _ _ _ _ (by rw [map_add, d_windingTC, d_windingTC, add_zero])]
  congr 1
  exact windingTC_mul g g' hg hg'

/-- **The constant function `1` has winding class `0`.** -/
theorem windingClass_of_eq_one (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (h : ∀ y, g y = 1) :
    windingClass g hg = 0 := by
  obtain rfl : g = 1 := ContinuousMap.ext h
  have h0 : windingTC (1 : C(Y, ℂ)) hg = 0 := ChernWinding.rationalWindingCochain_one
  have hc : cocycleOf (windingTC (1 : C(Y, ℂ)) hg) (d_windingTC _ hg) = 0 := by
    apply (ModuleCat.mono_iff_injective ((tcCochains Y).iCycles 1)).mp inferInstance
    rw [iCycles_cocycleOf, h0, map_zero]
  unfold windingClass windingClassTC
  rw [hc, map_zero, map_zero]

/-- The winding class depends only on the values of the function. -/
theorem windingClass_ext {g g' : C(Y, ℂ)} (hg : ∀ y, g y ≠ 0) (hg' : ∀ y, g' y ≠ 0)
    (h : ∀ y, g y = g' y) : windingClass g hg = windingClass g' hg' := by
  obtain rfl : g = g' := ContinuousMap.ext h
  rfl

/-- **The inverse function has the negative class**: `[k] = −[g]` when `k g = 1`. -/
theorem windingClass_eq_neg_of_mul_eq_one (g k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (h : ∀ y, k y * g y = 1) : windingClass k hk = -windingClass g hg := by
  have h1 := windingClass_mul k g hk hg
  rw [windingClass_of_eq_one _ _ h] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

/-! ### Pullback along a homeomorphism -/

/-- **Pullback along a homeomorphism `h : Y ≃ₜ X` as a linear equivalence**
`H^k(X; ℚ) ≃ H^k(Y; ℚ)`, with inverse the pullback along `h.symm`. -/
def cohomologyEquivOfHomeomorph {X : TopCat.{0}} (h : Y ≃ₜ X) (k : ℕ) :
    Cohomology ℚ X k ≃ₗ[ℚ] Cohomology ℚ Y k where
  toLinearMap := cohomologyMap ℚ k (TopCat.ofHom (h : C(Y, X)))
  invFun := cohomologyMap ℚ k (TopCat.ofHom (h.symm : C(X, Y)))
  left_inv x := by
    change cohomologyMap ℚ k _ (cohomologyMap ℚ k _ x) = x
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    convert LinearMap.congr_fun (cohomologyMap_id ℚ X k) x
    ext x
    exact h.apply_symm_apply x
  right_inv x := by
    change cohomologyMap ℚ k _ (cohomologyMap ℚ k _ x) = x
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    convert LinearMap.congr_fun (cohomologyMap_id ℚ Y k) x
    ext x
    exact h.symm_apply_apply x

/-- `cohomologyEquivOfHomeomorph h k` applies as `cohomologyMap`, by `rfl`. -/
theorem cohomologyEquivOfHomeomorph_apply {X : TopCat.{0}} (h : Y ≃ₜ X) (k : ℕ)
    (x : Cohomology ℚ X k) :
    cohomologyEquivOfHomeomorph h k x = cohomologyMap ℚ k (TopCat.ofHom (h : C(Y, X))) x :=
  rfl

end HodgeLadder.Cup
