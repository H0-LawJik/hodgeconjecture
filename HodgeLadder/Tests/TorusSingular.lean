module

public import HodgeLadder.Cup.WindingTorus

/-!
# A sign-visible singular cup product on `ℂˣ × ℂˣ`

Rung `singular-odd-cup-test` (test for `cup-graded-commutative`, sub-rung of
`cup-odd-degree-test`). On the space `ℂˣ × ℂˣ`, realized as the subspace of `ℂ × ℂ` where both
coordinates are nonzero, the two coordinates have winding classes `a₁ a₂ ∈ H¹(ℂˣ × ℂˣ; ℚ)` (in
upstream's singular cohomology) with

  `⟨a₁ ⌣ a₂, T⟩ = 1`, `⟨a₂ ⌣ a₁, T⟩ = −1`,

on the torus `T (s, t) = (exp (2πi s), exp (2πi t))`. So the singular cup product of two
degree-one classes is nonzero there, and swapping the factors changes it: the sign `(−1)^{1·1}`
of `cupSing_gradedComm` is `−1` on a computed instance.

## Main definitions

* `HodgeLadder.Tests.puncturedSquare`, `HodgeLadder.Tests.coordOne`,
  `HodgeLadder.Tests.coordTwo`, `HodgeLadder.Tests.standardTorus`

## Main results

* `HodgeLadder.Tests.puncturedSquare_cupSing_eval`,
  `HodgeLadder.Tests.puncturedSquare_cupSing_swap_eval`,
  `HodgeLadder.Tests.puncturedSquare_cupSing_ne_zero`,
  `HodgeLadder.Tests.puncturedSquare_cupSing_swap_ne`
-/

@[expose] public noncomputable section

open ChernWinding HodgeLadder.Cup

namespace HodgeLadder.Tests

/-- `ℂˣ × ℂˣ`, as the subspace of `ℂ × ℂ` where both coordinates are nonzero. -/
abbrev puncturedSquare : TopCat.{0} := TopCat.of {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.2 ≠ 0}

/-- The first coordinate. -/
def coordOne : C(puncturedSquare, ℂ) := ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The second coordinate. -/
def coordTwo : C(puncturedSquare, ℂ) := ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩

/-- The first coordinate does not vanish. -/
theorem coordOne_ne_zero (p : puncturedSquare) : coordOne p ≠ 0 := p.2.1

/-- The second coordinate does not vanish. -/
theorem coordTwo_ne_zero (p : puncturedSquare) : coordTwo p ≠ 0 := p.2.2

/-- The standard torus `(s, t) ↦ (exp (2πi s), exp (2πi t))`. -/
def standardTorus : C(ℝ × ℝ, puncturedSquare) :=
  ⟨fun p => ⟨(Complex.exp (twoPiI * (p.1 : ℂ)), Complex.exp (twoPiI * (p.2 : ℂ))),
      Complex.exp_ne_zero _, Complex.exp_ne_zero _⟩,
    by fun_prop⟩

/-- `exp (2πi · 1) = exp (2πi · 0)`. -/
theorem exp_twoPiI_one :
    Complex.exp (twoPiI * ((1 : ℝ) : ℂ)) = Complex.exp (twoPiI * ((0 : ℝ) : ℂ)) := by
  simp [twoPiI, Complex.exp_two_pi_mul_I]

/-- The standard torus has period `1` in the first variable. -/
theorem standardTorus_one_left (t : ℝ) : standardTorus (1, t) = standardTorus (0, t) := by
  apply Subtype.ext
  simp only [standardTorus, ContinuousMap.coe_mk]
  rw [exp_twoPiI_one]

/-- The standard torus has period `1` in the second variable. -/
theorem standardTorus_one_right (s : ℝ) : standardTorus (s, 1) = standardTorus (s, 0) := by
  apply Subtype.ext
  simp only [standardTorus, ContinuousMap.coe_mk]
  rw [exp_twoPiI_one]

/-- `⟨a₁ ⌣ a₂, T⟩ = 1` on `ℂˣ × ℂˣ`. -/
theorem puncturedSquare_cupSing_eval :
    torusEval standardTorus_one_left standardTorus_one_right
      (cupSing puncturedSquare (windingClass coordOne coordOne_ne_zero)
        (windingClass coordTwo coordTwo_ne_zero) 2 rfl) = 1 :=
  torusEval_cupSing_winding _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)

/-- `⟨a₂ ⌣ a₁, T⟩ = −1` on `ℂˣ × ℂˣ`. -/
theorem puncturedSquare_cupSing_swap_eval :
    torusEval standardTorus_one_left standardTorus_one_right
      (cupSing puncturedSquare (windingClass coordTwo coordTwo_ne_zero)
        (windingClass coordOne coordOne_ne_zero) 2 rfl) = -1 :=
  torusEval_cupSing_winding_swap _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)

/-- **A nonzero singular cup product of two degree-one classes.** -/
theorem puncturedSquare_cupSing_ne_zero :
    cupSing puncturedSquare (windingClass coordOne coordOne_ne_zero)
      (windingClass coordTwo coordTwo_ne_zero) 2 rfl ≠ 0 :=
  cupSing_winding_ne_zero standardTorus_one_left standardTorus_one_right _ _ _ _
    (fun _ => rfl) (fun _ => rfl)

/-- **The singular cup product of two degree-one classes is not commutative**: the sign of
`cupSing_gradedComm` in degrees `(1, 1)` is visible. -/
theorem puncturedSquare_cupSing_swap_ne :
    cupSing puncturedSquare (windingClass coordTwo coordTwo_ne_zero)
        (windingClass coordOne coordOne_ne_zero) 2 rfl ≠
      cupSing puncturedSquare (windingClass coordOne coordOne_ne_zero)
        (windingClass coordTwo coordTwo_ne_zero) 2 rfl :=
  cupSing_winding_swap_ne standardTorus_one_left standardTorus_one_right _ _ _ _
    (fun _ => rfl) (fun _ => rfl)

end HodgeLadder.Tests
