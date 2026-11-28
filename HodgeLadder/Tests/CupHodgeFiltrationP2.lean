module

public import HodgeLadder.Hodge.CupHodgeFiltration
public import HodgeLadder.Tests.DeRhamCupP2
public import HodgeLadder.Tests.CycleClassMultiplicativeP2
public import HodgeLadder.Divisor.LefschetzEquality

/-!
# The filtration law of the de Rham cup product on ℙ², with a nonzero product

Non-vacuity test of rung `cup-hodge-filtration`. On `projectivePlane`, with `[L₀], [L₁]` the
classes of the coordinate lines and `ι = fieldToDeRhamCohomology ℚ`: `ι [L₀], ι [L₁] ∈ F^1 H_dR^2`
(`cycleComponentSheafClass_mem_hodgeClasses_one`, `mem_hodgeClasses_iff_mem_hodgeFiltration`),
their product `deRhamCup (ι [L₀]) (ι [L₁])` lies in `F^2 H_dR^4` by
`deRhamCup_mem_hodgeFiltration` and is nonzero (`planeLines_deRhamCup_ne_zero`). So the
hypotheses of statement (a) hold with a nonzero product. Statement (b) then gives
`[pt] ∈ Hdg^2(ℙ²; ℚ)` for the class of the point `[0 : 0 : 1]`, through
`planeLines_cup_eq_planeOrigin`.

The conclusion `F^2 H_dR^4(ℙ²)` is the whole group in classical Hodge theory (unverified at the
pin). The sharp test is `planeLine_not_mem_hodgeFiltration_two`: with `F^3 H_dR^4(ℙ²) = 0`
(upstream's `hodgeFiltration_eq_bot_of_lt`), statement (a) and the nonzero product force
`ι [L₀] ∉ F^2 H_dR^2`, so the index `p + q` is sharp, both hypotheses carry content, and upstream's
filtration on ℙ² is proper in degrees 2 and 4 (`plane_hodgeFiltration_three_four`).

## Main results

* `HodgeLadder.Tests.planeLines_deRhamCup_mem_hodgeFiltration`
* `HodgeLadder.Tests.planeLine_not_mem_hodgeFiltration_two`
* `HodgeLadder.Tests.plane_hodgeFiltration_three_four`
* `HodgeLadder.Tests.planeOrigin_mem_hodgeClasses`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLadder.Tests

/-- On ℙ², `ι [L₀], ι [L₁] ∈ F^1 H_dR^2`, and `deRhamCup (ι [L₀]) (ι [L₁])` lies in
`F^{1+1} H_dR^4` and is nonzero. -/
theorem planeLines_deRhamCup_mem_hodgeFiltration :
    fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)) ∈
      hodgeFiltration projectivePlane 1 ((2 * 1 : ℕ) : ℤ) ∧
    fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)) ∈
      hodgeFiltration projectivePlane 1 ((2 * 1 : ℕ) : ℤ) ∧
    deRhamCup
        (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
          (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
        (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
          (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
        4 (by norm_num) ∈ hodgeFiltration projectivePlane (1 + 1) 4 ∧
    deRhamCup
        (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
          (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)))
        (fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
          (cycleComponentSheafClass projectivePlane (planeLine 1) (coheight_planeLine 1)))
        4 (by norm_num) ≠ 0 := by
  have h0 := (mem_hodgeClasses_iff_mem_hodgeFiltration projectivePlane 1 _).mp
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 0))
  have h1 := (mem_hodgeClasses_iff_mem_hodgeFiltration projectivePlane 1 _).mp
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 1))
  exact ⟨h0, h1, deRhamCup_mem_hodgeFiltration _ h0 h1, planeLines_deRhamCup_ne_zero⟩

/-- The class of the point `[0 : 0 : 1]` of ℙ² is a Hodge class: `[pt] = [L₀] ∪ [L₁]`
(`planeLines_cup_eq_planeOrigin`) and `cupPreservesHodgeClasses_holds`. -/
theorem planeOrigin_mem_hodgeClasses :
    cycleComponentSheafClass projectivePlane planeOrigin coheight_planeOrigin_add ∈
      Hdg^(1 + 1)(projectivePlane; ℚ) := by
  rw [← planeLines_cup_eq_planeOrigin]
  exact cupPreservesHodgeClasses_holds projectivePlane 1 1 _ _
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 0))
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 1))

/-- **The filtration law is sharp on ℙ².** `ι [L₀] ∉ F^2 H_dR^2(ℙ²)`: otherwise
`deRhamCup (ι [L₀]) (ι [L₁])` would lie in `F^{2+1} H_dR^4(ℙ²)`, which is zero since
`dim ℙ² = 2` (upstream's `hodgeFiltration_eq_bot_of_lt`), against
`planeLines_deRhamCup_ne_zero`. -/
theorem planeLine_not_mem_hodgeFiltration_two :
    fieldToDeRhamCohomology ℚ projectivePlane (2 * 1)
        (cycleComponentSheafClass projectivePlane (planeLine 0) (coheight_planeLine 0)) ∉
      hodgeFiltration projectivePlane 2 ((2 * 1 : ℕ) : ℤ) := by
  intro h
  have h1 := (mem_hodgeClasses_iff_mem_hodgeFiltration projectivePlane 1 _).mp
    (cycleComponentSheafClass_mem_hodgeClasses_one projectivePlane _ (coheight_planeLine 1))
  have hm := deRhamCup_mem_hodgeFiltration (n := 4) (by norm_num) h h1
  have hd : TopologicalSpace.dim projectivePlane.left = 2 := dim_projectiveSpace 2
  rw [AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt projectivePlane
    (p := 2 + ((1 : ℕ) : ℤ)) (by rw [hd]; norm_num) 4] at hm
  exact planeLines_deRhamCup_ne_zero ((AddSubgroup.mem_bot).mp hm)

/-- On ℙ², `F^3 H_dR^4 = 0` while `F^2 H_dR^4` contains the nonzero class
`deRhamCup (ι [L₀]) (ι [L₁])`. -/
theorem plane_hodgeFiltration_three_four :
    hodgeFiltration projectivePlane 3 4 = ⊥ ∧ hodgeFiltration projectivePlane 2 4 ≠ ⊥ := by
  have hd : TopologicalSpace.dim projectivePlane.left = 2 := dim_projectiveSpace 2
  refine ⟨AlgebraicGeometry.ComplexPoint.hodgeFiltration_eq_bot_of_lt projectivePlane
    (p := 3) (by rw [hd]; norm_num) 4, ?_⟩
  intro hb
  have h := (planeLines_deRhamCup_mem_hodgeFiltration).2.2.1
  rw [show (1 + 1 : ℤ) = 2 from rfl, hb] at h
  exact (planeLines_deRhamCup_mem_hodgeFiltration).2.2.2 ((AddSubgroup.mem_bot).mp h)

end HodgeLadder.Tests
